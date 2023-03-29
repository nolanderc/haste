use futures::{future::BoxFuture, FutureExt};
use smallvec::smallvec;

use crate::{
    error,
    index_map::IndexMap,
    naming::{self, DeclId, DeclPath},
    span::Span,
    syntax::{self, ChannelKind, ExprId, ExprRange, Node, NodeId, NodeRange, NodeView},
    typing::{Field, TypeClass},
    HashMap, Result,
};

use super::{
    ConstantKind, FunctionType, InferredType, InterfaceMethod, InterfaceType, Signature,
    StructType, Type, TypeKind, TypeList,
};

pub(super) struct TypingContext<'db> {
    pub db: &'db dyn crate::Db,
    pub ast: &'db syntax::File,
    pub references: &'db IndexMap<NodeId, naming::Symbol>,
    pub nodes: &'db NodeView,

    pub path: DeclPath,

    /// Types of all expressions and types.
    pub node_types: HashMap<NodeId, Type>,
    /// Types of all local variables.
    pub local_types: HashMap<naming::Local, InferredType>,
}

impl<'db> TypingContext<'db> {
    pub async fn new(db: &'db dyn crate::Db, decl: DeclId) -> Result<TypingContext<'db>> {
        let path = decl.path(db).await?;
        let ast = syntax::parse_file(db, path.source).await.as_ref()?;
        let references = naming::decl_symbols(db, decl).await.as_ref()?;
        let nodes = &ast.declarations[path.index].nodes;

        Ok(Self {
            db,
            ast,
            references,
            nodes,
            path,
            node_types: HashMap::default(),
            local_types: HashMap::default(),
        })
    }

    pub fn finish(self) -> Result<super::TypingInfo> {
        Ok(super::TypingInfo {
            nodes: self.node_types,
            locals: self.local_types,
        })
    }

    async fn lookup_type(&self, typ: syntax::TypeId) -> Result<Option<Type>> {
        let Some(inferred) = self.lookup_node(typ.node).await? else { return Ok(None) };
        match inferred {
            InferredType::Type(typ) => Ok(Some(typ)),
            InferredType::Value(inner) => Err(error!("expected a type, but found a value").label(
                self.node_span(typ),
                format!("this is a value of type `{inner}`"),
            )),
        }
    }

    async fn lookup_node(&self, node: NodeId) -> Result<Option<InferredType>> {
        let Some(&symbol) = self.references.get(&node) else { return Ok(None) };
        match symbol {
            naming::Symbol::Local(local) => Ok(self.local_types.get(&local).copied()),
            naming::Symbol::Global(global) => match super::signature(self.db, global).await? {
                Signature::Value(typ) => Ok(Some(InferredType::Value(typ))),
                Signature::Type(typ) => Ok(Some(InferredType::Type(typ))),
                Signature::Package(_) => Err(error!("packages cannot be used as values")
                    .label(self.node_span(node), "this is a package")),
            },
        }
    }

    /// Resolve the given type, but only fetch the needed dependencies.
    pub async fn resolve_precise(&mut self, typ: syntax::TypeId) -> Result<Type> {
        self.resolve_type_impl(typ).await
    }

    /// Get the type represented by the given syntax tree.
    pub fn resolve_type(&mut self, typ: syntax::TypeId) -> BoxFuture<Result<Type>> {
        self.resolve_type_impl(typ).boxed()
    }

    async fn resolve_type_impl(&mut self, typ: syntax::TypeId) -> Result<Type> {
        let node = typ.node;
        match self.nodes.kind(node) {
            Node::Name(name) => match self.lookup_type(typ).await? {
                Some(typ) => Ok(typ),
                None => {
                    let name = name.map(|t| t.get(self.db)).unwrap_or("_");
                    Err(error!("unresolved type {name}").label(self.node_span(typ), ""))
                }
            },
            Node::Selector(_, _) => {
                if let Some(typ) = self.lookup_type(typ).await? {
                    return Ok(typ);
                }

                Err(error!("expression not valid in type context")
                    .label(self.ast.node_span(self.path.index, node), "expected a type"))
            }
            Node::Pointer(inner) => {
                let inner = self.resolve_type(inner).await?;
                Ok(TypeKind::Pointer(inner).insert(self.db))
            }
            Node::Array(len, inner) => {
                let inner_type = self.resolve_type(inner).await?;

                if let Some(len) = len {
                    let len = self.evaluate_integer(len).await?;
                    Ok(TypeKind::Array(len, inner_type).insert(self.db))
                } else {
                    Err(error!("cannot infer length of array").label(self.node_span(node), ""))
                }
            }
            Node::Slice(inner) => {
                let inner = self.resolve_type(inner).await?;
                Ok(TypeKind::Slice(inner).insert(self.db))
            }
            Node::Map(key, value) => {
                let key = self.resolve_type(key).await?;
                let value = self.resolve_type(value).await?;
                Ok(TypeKind::Map(key, value).insert(self.db))
            }
            Node::Channel(kind, typ) => {
                let inner = self.resolve_type(typ).await?;
                Ok(TypeKind::Channel(kind, inner).insert(self.db))
            }
            Node::FunctionType(signature) => {
                let func = self.resolve_signature(signature).await?;
                Ok(TypeKind::Function(func).insert(self.db))
            }
            Node::Struct(field_nodes) => {
                let mut fields = Vec::with_capacity(field_nodes.len());

                let mut names = HashMap::default();
                names.reserve(field_nodes.len());

                for &node in self.nodes.indirect(field_nodes) {
                    let kind = self.nodes.kind(node);
                    match kind {
                        Node::Field(ident, typ, tag) | Node::EmbeddedField(ident, typ, tag) => {
                            if let Some(name) = ident.text {
                                if let Some(previous) = names.insert(name, ident.span) {
                                    let old_span = self.ast.span(Some(self.path.index), previous);
                                    let new_span = self.ast.span(Some(self.path.index), ident.span);
                                    return Err(error!("field names must be unique")
                                        .label(old_span, format!("{name} first declared here"))
                                        .label(new_span, "then redeclared here"));
                                }
                            }

                            let typ = self.resolve_type(typ).await?;
                            fields.push(Field {
                                name: ident.text,
                                typ,
                                tag,
                                embedded: matches!(kind, syntax::Node::EmbeddedField { .. }),
                            });
                        }
                        _ => unreachable!("not a field"),
                    }
                }

                let fields = fields.into_boxed_slice();
                Ok(TypeKind::Struct(StructType { fields }).insert(self.db))
            }
            Node::Interface(elements) => {
                let mut methods = Vec::with_capacity(elements.len());

                let mut names = HashMap::default();
                names.reserve(elements.len());

                for &node in self.nodes.indirect(elements) {
                    let kind = self.nodes.kind(node);
                    match kind {
                        Node::MethodElement(ident, signature) => {
                            let Some(name) = ident.text else {
                                return Err(error!("method names may not be blank")
                                    .label(self.ast.span(Some(self.path.index), ident.span), "invalid method name"))
                            };

                            if let Some(previous) = names.insert(name, ident.span) {
                                let old_span = self.ast.span(Some(self.path.index), previous);
                                let new_span = self.ast.span(Some(self.path.index), ident.span);
                                return Err(error!("method names must be unique")
                                    .label(old_span, format!("{name} first declared here"))
                                    .label(new_span, "then redeclared here"));
                            }

                            let signature = self.resolve_signature(signature).await?;
                            methods.push(InterfaceMethod { name, signature });
                        }
                        _ => unreachable!("not a field"),
                    }
                }

                methods.sort_by_key(|method| method.name.get(self.db));

                let methods = methods.into_boxed_slice();
                Ok(TypeKind::Interface(InterfaceType { methods }).insert(self.db))
            }

            kind => unreachable!("not a type: {:?}", kind),
        }
    }

    pub async fn resolve_signature(
        &mut self,
        signature: syntax::Signature,
    ) -> Result<FunctionType> {
        let mut types = TypeList::with_capacity(signature.inputs_and_outputs().len());

        for node in self.nodes.indirect(signature.inputs_and_outputs()) {
            let param = self.nodes.parameter(*node);
            types.push(self.resolve_type(param.typ).await?);
        }

        Ok(FunctionType {
            types,
            inputs: signature.inputs().len(),
            variadic: signature.is_variadic(),
        })
    }

    pub async fn check_function(
        &mut self,
        signature: syntax::Signature,
        body: syntax::FunctionBody,
    ) -> Result<FunctionType> {
        let mut types = TypeList::with_capacity(signature.inputs_and_outputs().len());

        for node in self.nodes.indirect(signature.inputs_and_outputs()) {
            let param = self.nodes.parameter(*node);
            types.push(self.resolve_type(param.typ).await?);
        }

        tracing::warn!("TODO: check function body");

        Ok(FunctionType {
            types,
            inputs: signature.inputs().len(),
            variadic: signature.is_variadic(),
        })
    }

    pub fn node_span(&self, node: impl Into<NodeId>) -> crate::span::Span {
        self.ast.node_span(self.path.index, node)
    }

    pub fn range_span(&self, range: impl Into<NodeRange>) -> Option<crate::span::Span> {
        self.ast.range_span(self.path.index, range)
    }

    pub async fn infer_assignment(&mut self, expr: ExprId) -> Result<TypeList> {
        let mut list = TypeList::new();

        match self.nodes.kind(expr) {
            Node::Unary(syntax::UnaryOperator::Recv, channel) => {
                let (_kind, inner) = self.infer_recv_channel(channel).await?;
                list.push(inner);
                list.push(TypeKind::Bool.insert(self.db));
            }
            Node::Index(target, index) => {
                let (output, extra) = self.infer_index_type(target, index).await?;
                list.push(output);
                if let Some(extra) = extra {
                    list.push(extra);
                }
            }
            Node::Call(target, args, spread) => {
                return self.infer_function_call(expr, target, args, spread).await;
            }
            Node::TypeAssertion(_, _) => {
                let target_type = self.infer_expr(expr).await?;
                list.push(target_type);
                list.push(TypeKind::Bool.insert(self.db));
            }
            _ => list.push(self.infer_expr(expr).await?),
        }

        Ok(list)
    }

    /// Check that the given expression is valid for the given type
    pub async fn check_expr(&mut self, expr: ExprId, expected: Type) -> Result<()> {
        if let Node::CompositeLiteral(composite) = self.nodes.kind(expr) {
            return self
                .check_composite_literal_boxed(expr, expected, composite, move |this| {
                    this.node_span(expr)
                })
                .await;
        }

        let inferred = self.infer_expr(expr).await?;

        if !self.is_assignable(expected, inferred).await? {
            let span = self.node_span(expr);
            return Err(error!("type mismatch").label(
                span,
                format!("found `{inferred}`, but expected `{expected}`"),
            ));
        }

        Ok(())
    }

    async fn check_assignable(&self, expected: Type, found: Type, expr: ExprId) -> Result<()> {
        if !self.is_assignable(expected, found).await? {
            let span = self.node_span(expr);
            return Err(error!("type mismatch")
                .label(span, format!("found `{found}`, but expected `{expected}`")));
        }

        Ok(())
    }

    pub fn infer_expr(&mut self, expr: ExprId) -> BoxFuture<Result<Type>> {
        async move {
            match self.infer_expr_impl(expr).await? {
                InferredType::Value(typ) => Ok(typ),
                InferredType::Type(typ) => Err(error!("expected a value, but found a type")
                    .label(self.node_span(expr), format!("found the type `{typ}`"))),
            }
        }
        .boxed()
    }

    pub fn infer_expr_any(&mut self, expr: ExprId) -> BoxFuture<Result<InferredType>> {
        self.infer_expr_impl(expr).boxed()
    }

    async fn infer_expr_impl(&mut self, expr: ExprId) -> Result<InferredType> {
        use InferredType::Value;

        match self.nodes.kind(expr) {
            Node::Name(name) => match self.lookup_node(expr.node).await? {
                Some(typ) => Ok(typ),
                None => {
                    let name = name.map(|t| t.get(self.db)).unwrap_or("_");
                    Err(error!("unresolved reference {name}").label(self.node_span(expr), ""))
                }
            },
            Node::Selector(base, ident) => {
                if let Some(typ) = self.lookup_node(expr.node).await? {
                    return Ok(typ);
                }

                let base_type = self.infer_expr(ExprId::new(base)).await?;
                let core_type = if base_type.lookup(self.db).is_declared() {
                    super::underlying_type(self.db, base_type).await?
                } else {
                    base_type
                };

                let Some(name) = ident.text else {
                    return Err(error!("selector name must not be blank")
                        .label(self.ast.span(Some(self.path.index), ident.span), ""))
                };

                match core_type.lookup(self.db) {
                    TypeKind::Struct(strukt) => {
                        let Some(field) = strukt.get_field(name) else {
                            return Err(error!("no field `{name}` found for `{base_type}`")
                                .label(self.ast.span(Some(self.path.index), ident.span), ""))
                        };
                        Ok(Value(field.typ))
                    }
                    _ => Err(error!(
                        "cannot access field or method `{name}` of type `{base_type}`"
                    )
                    .label(self.node_span(expr), "")),
                }
            }

            Node::IntegerSmall(_) => Ok(Value(
                TypeKind::Untyped(super::ConstantKind::Integer).insert(self.db),
            )),
            Node::FloatSmall(_) => Ok(Value(
                TypeKind::Untyped(super::ConstantKind::Float).insert(self.db),
            )),
            Node::ImaginarySmall(_) => Ok(Value(
                TypeKind::Untyped(super::ConstantKind::Complex).insert(self.db),
            )),
            Node::Rune(_) => Ok(Value(
                TypeKind::Untyped(super::ConstantKind::Rune).insert(self.db),
            )),
            Node::String(_) => Ok(Value(
                TypeKind::Untyped(super::ConstantKind::String).insert(self.db),
            )),

            Node::Call(target, args, spread) => {
                let outputs = self.infer_function_call(expr, target, args, spread).await?;
                if outputs.len() != 1 {
                    return Err(error!(
                        "function with multi-value return may not be called in expression position"
                    )
                    .label(
                        self.node_span(expr),
                        format!("found outputs: {}", crate::util::fmt_tuple(&outputs)),
                    ));
                }
                Ok(Value(outputs[0]))
            }

            Node::Composite(typ, composite) => {
                let typ = self.infer_composite_init(expr, typ, composite).await?;
                Ok(Value(typ))
            }
            Node::CompositeLiteral(_) => {
                Err(error!("could not infer type of composite literal")
                    .label(self.node_span(expr), ""))
            }

            Node::TypeAssertion(base, typ) => {
                let Some(typ) = typ else {
                    return Err(error!("only allowed within `switch` statement")
                        .label(self.node_span(expr), ""))
                };

                let base_type = self.infer_expr(base).await?;
                let target_type = self.resolve_type(typ).await?;

                match base_type.lookup(self.db) {
                    TypeKind::Interface(_) => {
                        tracing::warn!(
                            "ensure that `{target_type}` implements the interface `{base_type}`"
                        );
                        Ok(Value(target_type))
                    }
                    _ => Err(error!("argument in type assertion must be an `interface`")
                        .label(self.node_span(base), "must be an interface")),
                }
            }

            Node::Unary(op, arg) => match op {
                syntax::UnaryOperator::Plus => {
                    let arg_type = self.infer_expr(arg).await?;
                    if !arg_type.lookup(self.db).is_numeric() {
                        return Err(error!("the operator `+` expected a numeric type")
                            .label(self.node_span(arg), format!("this has type `{arg_type}`")));
                    }
                    Ok(Value(arg_type))
                }
                syntax::UnaryOperator::Minus => {
                    let arg_type = self.infer_expr(arg).await?;
                    if !arg_type.lookup(self.db).is_signed() {
                        return Err(error!("the operator `-` expected a signed numeric type")
                            .label(self.node_span(arg), format!("this has type `{arg_type}`")));
                    }
                    Ok(Value(arg_type))
                }
                syntax::UnaryOperator::Xor => {
                    let arg_type = self.infer_expr(arg).await?;
                    if !arg_type.lookup(self.db).is_integer() {
                        return Err(error!("the operator `^` expected an integer")
                            .label(self.node_span(arg), format!("this has type `{arg_type}`")));
                    }
                    Ok(Value(arg_type))
                }
                syntax::UnaryOperator::Not => {
                    let arg_type = self.infer_expr(arg).await?;
                    if !arg_type.lookup(self.db).is_bool() {
                        return Err(error!("`!` expected a `bool`")
                            .label(self.node_span(arg), format!("this has type `{arg_type}`")));
                    }
                    Ok(Value(arg_type))
                }
                syntax::UnaryOperator::Deref => {
                    match self.infer_expr_any(arg).await? {
                        // looks like a dereference
                        InferredType::Value(typ) => match typ.lookup(self.db) {
                            TypeKind::Pointer(inner) => Ok(Value(*inner)),
                            _ => Err(error!("can only dereference pointers")
                                .label(self.node_span(arg), format!("this has type `{typ}`"))),
                        },
                        // looks like a pointer type
                        InferredType::Type(typ) => {
                            Ok(InferredType::Type(TypeKind::Pointer(typ).insert(self.db)))
                        }
                    }
                }
                syntax::UnaryOperator::Ref => {
                    let arg_type = self.infer_expr(arg).await?;
                    Ok(Value(TypeKind::Pointer(arg_type).insert(self.db)))
                }
                syntax::UnaryOperator::Recv => {
                    let arg_type = self.infer_expr(arg).await?;
                    match arg_type.lookup(self.db) {
                        TypeKind::Channel(kind, inner) => {
                            if !kind.is_recv() {
                                return Err(error!(
                                    "cannot receive values from a send-only channel"
                                )
                                .label(
                                    self.node_span(arg),
                                    format!("this has type `{arg_type}`"),
                                ));
                            }
                            Ok(Value(*inner))
                        }
                        _ => Err(error!("expected a channel")
                            .label(self.node_span(arg), format!("this has type `{arg_type}`"))),
                    }
                }
            },
            Node::Binary(interleaved) => {
                use syntax::BinaryOperator as BinOp;

                let interleaved = self.nodes.indirect(interleaved);

                let lhs_span = |this: &Self, index: usize| {
                    this.node_span(interleaved[0])
                        .join(this.node_span(interleaved[2 * index]))
                };

                let mut lhs = self.infer_expr(interleaved[0]).await?;
                for (index, pair) in interleaved[1..].chunks_exact(2).enumerate() {
                    let Node::BinaryOp(op) = self.nodes.kind(pair[0]) else { unreachable!() };
                    let rhs = self.infer_expr(pair[1]).await?;

                    match op {
                        BinOp::LogicalOr | BinOp::LogicalAnd => {
                            if lhs.lookup(self.db).is_bool() && rhs.lookup(self.db).is_bool() {
                                lhs = Type::untyped_bool(self.db);
                                continue;
                            }
                            return Err(error!("incompatible types for `{op}`")
                                .label(
                                    self.node_span(pair[0]),
                                    "expected both operands to be of type `bool`",
                                )
                                .label(
                                    lhs_span(self, index),
                                    format!("this is found to be of type `{lhs}`"),
                                )
                                .label(
                                    self.node_span(pair[1]),
                                    format!("this is found to be of type `{rhs}`"),
                                ));
                        }
                        BinOp::Equal | BinOp::NotEqual => {
                            if self.is_comparable(lhs, rhs).await? {
                                lhs = Type::untyped_bool(self.db);
                                continue;
                            }
                            return Err(error!("the operands are not comparable")
                                .label(self.node_span(pair[0]), "in this comparison")
                                .label(
                                    lhs_span(self, index),
                                    format!("this is found to be of type `{lhs}`"),
                                )
                                .label(
                                    self.node_span(pair[1]),
                                    format!("this is found to be of type `{rhs}`"),
                                ));
                        }
                        BinOp::Less | BinOp::LessEqual | BinOp::Greater | BinOp::GreaterEqual => {
                            if self.is_ordered(lhs, rhs).await? {
                                lhs = Type::untyped_bool(self.db);
                                continue;
                            }
                            return Err(error!("the operands cannot be ordered")
                                .label(self.node_span(pair[0]), "in this comparison")
                                .label(
                                    lhs_span(self, index),
                                    format!("this is found to be of type `{lhs}`"),
                                )
                                .label(
                                    self.node_span(pair[1]),
                                    format!("this is found to be of type `{rhs}`"),
                                ));
                        }

                        BinOp::Add
                        | BinOp::Sub
                        | BinOp::BitOr
                        | BinOp::BitXor
                        | BinOp::Mul
                        | BinOp::Div
                        | BinOp::Rem
                        | BinOp::BitAnd
                        | BinOp::BitNand => {
                            let lhs_kind = lhs.lookup(self.db);
                            let rhs_kind = rhs.lookup(self.db);

                            let lhs_class = lhs_kind.class();
                            let rhs_class = rhs_kind.class();

                            let classes = match op {
                                BinOp::Add => TypeClass::NUMERIC | TypeClass::STRING,
                                BinOp::Sub | BinOp::Mul | BinOp::Div => TypeClass::NUMERIC,
                                BinOp::Rem
                                | BinOp::BitOr
                                | BinOp::BitXor
                                | BinOp::BitAnd
                                | BinOp::BitNand => TypeClass::INTEGER,
                                _ => unreachable!(),
                            };

                            let overlap = lhs_class.intersection(rhs_class);

                            if overlap.intersects(classes) {
                                if lhs == rhs || lhs_class.is_untyped() || rhs_class.is_untyped() {
                                    lhs = if lhs_class.is_untyped() && rhs_class.is_untyped() {
                                        let order = [
                                            TypeClass::COMPLEX,
                                            TypeClass::FLOAT,
                                            TypeClass::RUNE,
                                            TypeClass::INTEGER,
                                        ];

                                        'order: {
                                            for order in order {
                                                if lhs_class.contains(order) {
                                                    break 'order lhs;
                                                }
                                                if rhs_class.contains(order) {
                                                    break 'order rhs;
                                                }
                                            }

                                            lhs
                                        }
                                    } else if lhs_class.is_untyped() {
                                        rhs
                                    } else {
                                        lhs
                                    };
                                    continue;
                                }
                            }

                            return Err(error!("incompatible types for `{op}`")
                                .label(
                                    self.node_span(pair[0]),
                                    "both operands must be of the same type",
                                )
                                .label(
                                    lhs_span(self, index),
                                    format!("this is found to be of type `{lhs}`"),
                                )
                                .label(
                                    self.node_span(pair[1]),
                                    format!("this is found to be of type `{rhs}`"),
                                ));
                        }

                        BinOp::ShiftLeft | BinOp::ShiftRight => {
                            let lhs_class = lhs.lookup(self.db).class();
                            let rhs_class = rhs.lookup(self.db).class();

                            if lhs_class.is_integer() && rhs_class.is_integer() {
                                continue;
                            }

                            return Err(error!("incompatible types for `{op}`")
                                .label(self.node_span(pair[0]), "both operands must be integers")
                                .label(
                                    lhs_span(self, index),
                                    format!("this is found to be of type `{lhs}`"),
                                )
                                .label(
                                    self.node_span(pair[1]),
                                    format!("this is found to be of type `{rhs}`"),
                                ));
                        }
                    }
                }
                Ok(Value(lhs))
            }
            Node::BinaryOp(_) => unreachable!("handled by `Node::Binary`"),

            Node::Function(signature, body) => {
                let func = self.check_function(signature, body).await?;
                Ok(Value(TypeKind::Function(func).insert(self.db)))
            }

            Node::Index(target, index) => {
                let target_type = self.infer_expr(target).await?;
                match target_type.lookup(self.db) {
                    &TypeKind::Array(_, inner) | &TypeKind::Slice(inner) => {
                        let index_type = self.infer_expr(index).await?;
                        if !index_type.lookup(self.db).is_integer() {
                            return Err(error!("expecetd an integer index").label(
                                self.node_span(index),
                                format!("this is of type `{index_type}`"),
                            ));
                        }
                        Ok(Value(inner))
                    }
                    &TypeKind::Map(key, value) => {
                        self.check_expr(index, key).await?;
                        Ok(Value(value))
                    }
                    _ => Err(error!("cannot index into value of type `{target_type}`")
                        .label(self.node_span(expr), "")),
                }
            }
            Node::SliceIndex(target, start, end) => {
                let target_type = self.infer_expr(target).await?;
                match target_type.lookup(self.db) {
                    &TypeKind::Array(_, inner) | &TypeKind::Slice(inner) => {
                        let check_integer = |this: &Self, index: ExprId, typ: Type| {
                            if !typ.lookup(this.db).is_integer() {
                                return Err(error!("expecetd an integer index")
                                    .label(
                                        this.node_span(index),
                                        format!("this is of type `{typ}`"),
                                    )
                                    .label(this.node_span(expr), "in this slice operation"));
                            }
                            Ok(())
                        };

                        if let Some(start) = start {
                            let typ = self.infer_expr(start).await?;
                            check_integer(self, start, typ)?;
                        }

                        if let Some(end) = end {
                            let typ = self.infer_expr(end).await?;
                            check_integer(self, end, typ)?;
                        }

                        Ok(Value(inner))
                    }
                    _ => Err(error!("cannot slice into value of type `{target_type}`")
                        .label(self.node_span(expr), "")
                        .label(self.node_span(target), "expected a slice or array")),
                }
            }
            Node::SliceCapacity(target, start, end, cap) => {
                let target_type = self.infer_expr(target).await?;
                match target_type.lookup(self.db) {
                    &TypeKind::Array(_, inner) | &TypeKind::Slice(inner) => {
                        let check_integer = |this: &Self, index: ExprId, typ: Type| {
                            if !typ.lookup(this.db).is_integer() {
                                return Err(error!("expecetd an integer index")
                                    .label(
                                        this.node_span(index),
                                        format!("this is of type `{typ}`"),
                                    )
                                    .label(this.node_span(expr), "in this slice operation"));
                            }
                            Ok(())
                        };

                        if let Some(start) = start {
                            let typ = self.infer_expr(start).await?;
                            check_integer(self, start, typ)?;
                        }

                        let typ = self.infer_expr(end).await?;
                        check_integer(self, end, typ)?;

                        let typ = self.infer_expr(cap).await?;
                        check_integer(self, end, typ)?;

                        Ok(Value(inner))
                    }
                    _ => Err(error!("cannot slice into value of type `{target_type}`")
                        .label(self.node_span(expr), "")
                        .label(self.node_span(target), "expected a slice or array")),
                }
            }

            Node::Parameter(_) => unreachable!("parameters are not expressions"),

            Node::Pointer(_)
            | Node::Array(_, _)
            | Node::Slice(_)
            | Node::Map(_, _)
            | Node::Channel(_, _)
            | Node::FunctionType(_)
            | Node::Struct(_)
            | Node::Field(_, _, _)
            | Node::EmbeddedField(_, _, _)
            | Node::Interface(_)
            | Node::MethodElement(_, _) => {
                let typ = self.resolve_type(syntax::TypeId::new(expr.node)).await?;
                Ok(InferredType::Type(typ))
            }

            Node::TypeDef(_)
            | Node::TypeAlias(_)
            | Node::TypeList(_)
            | Node::ConstDecl(_, _, _)
            | Node::ConstList(_)
            | Node::VarDecl(_, _, _)
            | Node::VarList(_)
            | Node::Block(_)
            | Node::Label(_, _)
            | Node::Return(_)
            | Node::ReturnMulti(_)
            | Node::Assign(_, _)
            | Node::AssignOp(_, _, _)
            | Node::Increment(_)
            | Node::Decrement(_)
            | Node::Send(_)
            | Node::Go(_)
            | Node::Defer(_)
            | Node::Break(_)
            | Node::Continue(_)
            | Node::Goto(_)
            | Node::If(_, _, _, _)
            | Node::Select(_)
            | Node::SelectSend(_, _)
            | Node::SelectRecv(_, _, _, _)
            | Node::SelectDefault(_)
            | Node::Switch(_, _, _)
            | Node::TypeSwitch(_, _)
            | Node::SwitchCase(_, _)
            | Node::Fallthrough
            | Node::For(_, _, _, _)
            | Node::ForRangePlain(_, _)
            | Node::ForRange(_, _, _, _, _) => {
                Err(error!("statements are not allowed in expression context")
                    .label(self.node_span(expr), "expected an expression"))
            }
        }
    }

    async fn infer_composite_init(
        &mut self,
        expr: ExprId,
        typ: syntax::TypeId,
        composite: syntax::CompositeRange,
    ) -> Result<Type> {
        let expected = match self.nodes.kind(typ) {
            Node::Array(None, inner) => {
                let inner = self.resolve_type(inner).await?;
                TypeKind::Array(composite.len() as u64, inner).insert(self.db)
            }
            _ => self.resolve_type(typ).await?,
        };

        self.check_composite_literal(expr, expected, composite, |this| this.node_span(typ))
            .await?;

        Ok(expected)
    }

    fn check_composite_literal_boxed(
        &mut self,
        expr: ExprId,
        expected: Type,
        composite: syntax::CompositeRange,
        type_span: impl Fn(&Self) -> Span + Send + 'static,
    ) -> BoxFuture<Result<()>> {
        self.check_composite_literal(expr, expected, composite, type_span)
            .boxed()
    }

    async fn check_composite_literal(
        &mut self,
        expr: ExprId,
        mut target: Type,
        composite: syntax::CompositeRange,
        type_span: impl Fn(&Self) -> Span,
    ) -> Result<()> {
        loop {
            match target.lookup(self.db) {
                &TypeKind::Pointer(inner) => target = inner,

                &TypeKind::Array(_, inner) | &TypeKind::Slice(inner) => {
                    for key in composite.keys(self.nodes) {
                        self.evaluate_integer(key).await?;
                    }
                    for value in composite.values(self.nodes) {
                        self.check_expr(value, inner).await?;
                    }
                    return Ok(());
                }
                &TypeKind::Map(expected_key, expected_value) => {
                    let keys = composite.keys(self.nodes);
                    let values = composite.values(self.nodes);
                    if keys.len() != values.len() {
                        return Err(error!("every element in a map literal must have a key")
                            .label(self.node_span(expr), ""));
                    }

                    for (key, value) in keys.zip(values) {
                        self.check_expr(key, expected_key).await?;
                        self.check_expr(value, expected_value).await?;
                    }

                    return Ok(());
                }
                TypeKind::Struct(strukt) => {
                    let keys = composite.keys(self.nodes);
                    let values = composite.values(self.nodes);

                    if values.len() > strukt.fields.len() {
                        return Err(error!(
                            "number of elements ({}) exceed the number of fields ({})",
                            values.len(),
                            strukt.fields.len(),
                        )
                        .label(
                            self.node_span(expr),
                            format!("when initializing `{target}`"),
                        ));
                    }

                    if keys.len() == 0 {
                        for (value, field) in values.zip(strukt.fields.iter()) {
                            self.check_expr(value, field.typ).await?;
                        }
                    } else {
                        if keys.len() != values.len() {
                            return Err(error!(
                                "either all elements must specify a field name, or none"
                            )
                            .label(self.node_span(expr), ""));
                        }

                        for (key, value) in keys.zip(values) {
                            let Node::Name(name) = self.nodes.kind(key) else {
                                return Err(error!("expected the name of a field")
                                    .label(self.node_span(key), "expected an identifier"))
                            };

                            let Some(name) = name else {
                                return Err(error!("field name must not be blank")
                                    .label(self.node_span(key), ""))
                            };

                            let Some(field) = strukt.get_field(name) else {
                                return Err(error!("no field `{name}` found for `{target}`")
                                    .label(self.node_span(key), ""))
                            };

                            self.check_expr(value, field.typ).await?;
                        }
                    }

                    return Ok(());
                }
                &TypeKind::Declared(_) => {
                    target = super::underlying_type(self.db, target).await?;
                }
                _ => {
                    return Err(error!("not a composite type: `{target}`")
                        .label(type_span(self), "cannot initialize using composite syntax"))
                }
            }
        }
    }

    async fn infer_recv_channel(&mut self, channel: ExprId) -> Result<(ChannelKind, Type)> {
        let typ = self.infer_expr(channel).await?;
        match *typ.lookup(self.db) {
            TypeKind::Channel(kind, typ) if kind.is_recv() => Ok((kind, typ)),
            _ => Err(error!("unexpected type `{typ}`")
                .label(self.node_span(channel), "expected a receive channel")),
        }
    }

    async fn infer_index_type(
        &mut self,
        target: ExprId,
        index: ExprId,
    ) -> Result<(Type, Option<Type>)> {
        let mut target_type = self.infer_expr(target).await?;

        let typ = loop {
            match target_type.lookup(self.db) {
                TypeKind::Pointer(inner) => target_type = *inner,
                TypeKind::Slice(inner) => {
                    break self.check_array_index(*inner, None, index).await?
                }
                TypeKind::Array(len, inner) => {
                    break self.check_array_index(*inner, Some(*len), index).await?
                }
                TypeKind::String => {
                    let inner = TypeKind::Uint8.insert(self.db);
                    break self.check_array_index(inner, None, index).await?;
                }

                TypeKind::Map(key, value) => {
                    self.check_expr(index, *key).await?;
                    return Ok((*value, Some(TypeKind::Bool.insert(self.db))));
                }

                _ => {
                    return Err(
                        error!("cannot index into value of type `{target_type}`").label(
                            self.node_span(target),
                            "expected an array, slice, string or map",
                        ),
                    )
                }
            }
        };

        Ok((typ, None))
    }

    async fn check_array_index(
        &mut self,
        inner: Type,
        len: Option<u64>,
        index: ExprId,
    ) -> Result<Type> {
        let index_type = self.infer_expr(index).await?;
        match index_type.lookup(self.db) {
            TypeKind::Int
            | TypeKind::Int8
            | TypeKind::Int16
            | TypeKind::Int32
            | TypeKind::Int64
            | TypeKind::Uint
            | TypeKind::Uint8
            | TypeKind::Uint16
            | TypeKind::Uint32
            | TypeKind::Uint64
            | TypeKind::Uintptr => return Ok(inner),
            TypeKind::Untyped(constant) => {
                let representable = match constant {
                    super::ConstantKind::Rune | super::ConstantKind::Integer => true,
                    super::ConstantKind::Float | super::ConstantKind::Complex => {
                        todo!("determine if float constant is representable as int")
                    }
                    super::ConstantKind::Boolean
                    | super::ConstantKind::String
                    | super::ConstantKind::Nil => false,
                };

                if representable {
                    if len.is_some() {
                        tracing::warn!("TODO: check that constant index is within bounds");
                    }

                    return Ok(inner);
                }
            }
            _ => {}
        }

        Err(error!("cannot index into an array using `{index_type}`")
            .label(self.node_span(index), "not representable by an `int`"))
    }

    async fn evaluate_integer(&mut self, expr: ExprId) -> Result<u64> {
        let _typ = self.infer_expr(expr).await?;
        match self.nodes.kind(expr) {
            Node::IntegerSmall(value) => Ok(value),
            _ => Err(error!("could not evaluate expression")
                .label(self.node_span(expr), "must be a constant")),
        }
    }

    fn infer_function_call_boxed(
        &mut self,
        call_expr: ExprId,
        target: ExprId,
        args: ExprRange,
        spread: Option<syntax::ArgumentSpread>,
    ) -> BoxFuture<Result<TypeList>> {
        self.infer_function_call(call_expr, target, args, spread)
            .boxed()
    }

    async fn infer_function_call(
        &mut self,
        call_expr: ExprId,
        target: ExprId,
        args: ExprRange,
        spread: Option<syntax::ArgumentSpread>,
    ) -> Result<TypeList> {
        if spread.is_some() {
            todo!("implement function spread");
        }

        let target_type = match self.infer_expr_any(target).await? {
            InferredType::Value(value_type) => value_type,
            InferredType::Type(target_type) => {
                let cast = self
                    .infer_cast(call_expr, target_type, args, spread)
                    .await?;
                return Ok(smallvec![cast]);
            }
        };

        match target_type.lookup(self.db) {
            TypeKind::Builtin(builtin) => {
                Err(error!("TODO: call builtin {builtin:?}").label(self.node_span(call_expr), ""))
            }
            TypeKind::Function(func) => {
                let arg_exprs = self.nodes.indirect(args);

                if args.len() == 1 && func.inputs > 1 {
                    let arg_call = arg_exprs[0];
                    if let Node::Call(arg_target, arg_args, arg_spread) = self.nodes.kind(arg_call)
                    {
                        let types = self
                            .infer_function_call_boxed(arg_call, arg_target, arg_args, arg_spread)
                            .await?;

                        if types.len() != args.len() {
                            return Err(
                                self.emit_invalid_argument_count(target, func, args, call_expr)
                            );
                        }

                        for (&expected, arg) in func.inputs().iter().zip(types) {
                            self.check_assignable(expected, arg, arg_call).await?;
                        }

                        return Ok(TypeList::from(func.outputs()));
                    }
                }

                if func.inputs != args.len() {
                    return Err(self.emit_invalid_argument_count(target, func, args, call_expr));
                }

                for (&expected, &arg) in func.inputs().iter().zip(arg_exprs) {
                    self.check_expr(arg, expected).await?;
                }

                Ok(TypeList::from(func.outputs()))
            }
            _ => Err(error!("not a valid function type: {target_type}")
                .label(self.node_span(target), "expected a function")),
        }
    }

    fn emit_invalid_argument_count(
        &mut self,
        target: ExprId,
        func: &FunctionType,
        args: ExprRange,
        call_expr: ExprId,
    ) -> crate::Diagnostic {
        error!("invalid number of arguments")
            .label(
                self.node_span(target),
                format!("this function expected {} arguments", func.inputs),
            )
            .label(
                self.range_span(args)
                    .unwrap_or_else(|| self.node_span(call_expr)),
                format!("found {} arguments", args.len()),
            )
    }

    async fn infer_cast(
        &mut self,
        entire_expr: ExprId,
        target_type: Type,
        args: ExprRange,
        spread: Option<syntax::ArgumentSpread>,
    ) -> Result<Type> {
        if args.len() == 0 {
            return Err(error!("type conversions must have an argument")
                .label(self.node_span(entire_expr), ""));
        }

        if args.len() > 1 {
            return Err(error!("type only take a single argument").label(
                self.range_span(args).unwrap(),
                format!("found `{}` arguments, expected 1", args.len()),
            ));
        }

        if spread.is_some() {
            return Err(
                error!("spread operator not allowed in type conversions").label(
                    self.range_span(args)
                        .unwrap_or_else(|| self.node_span(entire_expr)),
                    format!("found `{}` arguments, expected 1", args.len()),
                ),
            );
        }

        let arg = self.nodes.indirect(args)[0];
        let source_type = self.infer_expr(arg).await?;

        if !self.can_convert(target_type, source_type).await? {
            return Err(error!("invalid conversion").label(
                self.node_span(entire_expr),
                format!("trying to cast `{target_type}` from `{source_type}`"),
            ));
        }

        Ok(target_type)
    }

    /// Determines if the two types are comparable.
    async fn is_comparable(&self, lhs: Type, rhs: Type) -> Result<bool> {
        if self.is_assignable(lhs, rhs).await? {
            if lhs.lookup(self.db).is_comparable(self.db) {
                return Ok(true);
            }
        } else if self.is_assignable(rhs, lhs).await? {
            if rhs.lookup(self.db).is_comparable(self.db) {
                return Ok(true);
            }
        }

        // not assignable
        Ok(false)
    }

    /// Can `source` be assigned to a destination of type `target`?
    async fn is_assignable(&self, target: Type, source: Type) -> Result<bool> {
        if target == source {
            return Ok(true);
        }

        let target_kind = target.lookup(self.db);
        let source_kind = source.lookup(self.db);

        let assignable = match (target_kind, source_kind) {
            (target, TypeKind::Untyped(ConstantKind::Boolean)) if target.is_bool() => true,
            (target, TypeKind::Untyped(ConstantKind::Integer)) if target.is_integer() => true,
            (target, TypeKind::Untyped(ConstantKind::Rune)) if target.is_integer() => true,
            (target, TypeKind::Untyped(ConstantKind::Float)) if target.is_float() => true,
            (target, TypeKind::Untyped(ConstantKind::Complex)) if target.is_complex() => true,
            (target, TypeKind::Untyped(ConstantKind::String)) if target.is_string() => true,
            (target, TypeKind::Untyped(ConstantKind::Nil)) if target.is_nillable() => true,

            (_, TypeKind::Untyped(_)) if self.is_representable(target, source).await? => true,

            (TypeKind::Interface(interface), _) => {
                if interface.methods.is_empty() {
                    // all types implement the trivial empty interface
                    return Ok(true);
                }

                return Err(error!(
                    "TODO: determine if `{source}` implements the interface `{target}`"
                ));
            }
            _ => {
                if !target_kind.is_declared() || !source_kind.is_declared() {
                    let target_core = super::underlying_type(self.db, target).await?;
                    let source_core = super::underlying_type(self.db, source).await?;
                    if target_core == source_core {
                        return Ok(true);
                    }
                }

                false
            }
        };

        Ok(assignable)
    }

    /// Can the `source` type be represented by the `target` type?
    async fn is_representable(&self, target: Type, source: Type) -> Result<bool> {
        if target == source {
            return Ok(true);
        }

        let target_kind = target.lookup(self.db);
        let source_kind = source.lookup(self.db);

        if let TypeKind::Untyped(untyped) = source_kind {
            let target_kind = if target_kind.is_declared() {
                super::underlying_type(self.db, target)
                    .await?
                    .lookup(self.db)
            } else {
                target_kind
            };

            let target_class = target_kind.class();
            return Ok(match untyped {
                ConstantKind::Boolean => target_kind.is_bool(),
                ConstantKind::Rune => target_class
                    .intersects(TypeClass::INTEGER | TypeClass::RUNE | TypeClass::STRING),
                ConstantKind::Integer => target_class.intersects(TypeClass::NUMERIC),
                ConstantKind::Float => target_class.intersects(TypeClass::NUMERIC),
                ConstantKind::Complex => target_class.intersects(TypeClass::NUMERIC),
                ConstantKind::String => target_class.intersects(TypeClass::STRING),
                ConstantKind::Nil => target_class.contains(TypeClass::NILLABLE),
            });
        }

        Ok(false)
    }

    /// Determines if the two types are ordered.
    async fn is_ordered(&self, lhs: Type, rhs: Type) -> Result<bool> {
        if self.is_assignable(lhs, rhs).await? {
            if lhs.lookup(self.db).is_ordered() {
                return Ok(true);
            }
        } else if self.is_assignable(rhs, lhs).await? {
            if rhs.lookup(self.db).is_ordered() {
                return Ok(true);
            }
        }

        // not assignable
        Ok(false)
    }

    async fn can_convert(&mut self, target: Type, source: Type) -> Result<bool> {
        if self.is_assignable(target, source).await?
            || self.is_representable(target, source).await?
        {
            return Ok(true);
        }

        let target_kind = target.lookup(self.db);
        let source_kind = source.lookup(self.db);

        match source_kind {
            TypeKind::String | TypeKind::Untyped(ConstantKind::String) => match target_kind {
                TypeKind::Slice(inner) => Ok(matches!(
                    inner.lookup(self.db),
                    TypeKind::Uint8 | TypeKind::Int32
                )),
                _ => Ok(false),
            },
            TypeKind::Slice(inner) => match inner.lookup(self.db) {
                TypeKind::Uint8 | TypeKind::Int32 => Ok(matches!(target_kind, TypeKind::String)),
                _ => Ok(false),
            },
            _ => Ok(false),
        }
    }
}
