use futures::{future::BoxFuture, FutureExt};

use crate::{
    error,
    index_map::IndexMap,
    naming::{self, DeclId, DeclPath},
    syntax::{self, ChannelKind, ExprId, ExprRange, Node, NodeId, NodeRange, NodeView},
    typing::{Field, TypeClass},
    HashMap, Result,
};

use super::{
    ConstantKind, FunctionType, InterfaceMethod, InterfaceType, Signature, StructType, Type,
    TypeKind, TypeList,
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
    pub local_types: HashMap<naming::Local, Type>,
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
        let node = typ.node;
        let Some(&symbol) = self.references.get(&node) else { return Ok(None) };
        match symbol {
            naming::Symbol::Local(local) => Ok(self.local_types.get(&local).copied()),
            naming::Symbol::Global(global) => match super::signature(self.db, global).await? {
                Signature::Type(typ) => Ok(Some(typ)),
                Signature::Package(_) => Err(error!("packages cannot be used as types")
                    .label(self.node_span(node), "this is a package")),
                Signature::Value(inner) => Err(error!("expected a type, but found a value").label(
                    self.node_span(node),
                    format!("this is a value of type `{inner}`"),
                )),
            },
        }
    }

    async fn lookup_value(&mut self, expr: ExprId) -> Result<Option<Type>> {
        let Some(&symbol) = self.references.get(&expr.node) else { return Ok(None) };
        match symbol {
            naming::Symbol::Local(local) => Ok(self.local_types.get(&local).copied()),
            naming::Symbol::Global(global) => match super::signature(self.db, global).await? {
                Signature::Value(typ) => Ok(Some(typ)),
                Signature::Package(_) => Err(error!("packages cannot be used as values")
                    .label(self.node_span(expr), "this is a package")),
                Signature::Type(inner) => Err(error!("expected a value, but found a type")
                    .label(self.node_span(expr), format!("this has type `{inner}`"))),
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
        let inferred = self.infer_expr(expr).await?;

        if !self.is_assignable(expected, inferred) {
            let span = self.node_span(expr);
            return Err(error!("type mismatch").label(
                span,
                format!("this is `{inferred}`, but expected `{expected}`"),
            ));
        }

        Ok(())
    }

    pub fn infer_expr(&mut self, expr: ExprId) -> BoxFuture<Result<Type>> {
        self.infer_expr_impl(expr).boxed()
    }

    async fn infer_expr_impl(&mut self, expr: ExprId) -> Result<Type> {
        match self.nodes.kind(expr) {
            Node::Name(name) => match self.lookup_value(expr).await? {
                Some(typ) => Ok(typ),
                None => {
                    let name = name.map(|t| t.get(self.db)).unwrap_or("_");
                    Err(error!("unresolved reference {name}").label(self.node_span(expr), ""))
                }
            },
            Node::Selector(base, name) => {
                if let Some(typ) = self.lookup_value(expr).await? {
                    return Ok(typ);
                }

                let base_type = self.infer_expr(ExprId::new(base)).await?;

                Err(
                    error!("TODO: access field or method `{name}` of type `{base_type}`")
                        .label(self.node_span(expr), ""),
                )
            }

            Node::IntegerSmall(_) => {
                Ok(TypeKind::Untyped(super::ConstantKind::Integer).insert(self.db))
            }
            Node::FloatSmall(_) => {
                Ok(TypeKind::Untyped(super::ConstantKind::Float).insert(self.db))
            }
            Node::ImaginarySmall(_) => {
                Ok(TypeKind::Untyped(super::ConstantKind::Complex).insert(self.db))
            }
            Node::Rune(_) => Ok(TypeKind::Untyped(super::ConstantKind::Rune).insert(self.db)),
            Node::String(_) => Ok(TypeKind::Untyped(super::ConstantKind::String).insert(self.db)),
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
                Ok(outputs[0])
            }
            Node::Composite(typ, composite) => {
                let expected = match self.nodes.kind(typ) {
                    Node::Array(None, inner) => {
                        let inner = self.resolve_type(inner).await?;
                        TypeKind::Array(composite.len() as u64, inner).insert(self.db)
                    }
                    _ => self.resolve_type(typ).await?,
                };

                match expected.lookup(self.db) {
                    &TypeKind::Array(_, inner) | &TypeKind::Slice(inner) => {
                        for key in composite.keys(self.nodes) {
                            self.evaluate_integer(key).await?;
                        }
                        for value in composite.values(self.nodes) {
                            self.check_expr(value, inner).await?;
                        }
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
                                format!("when initializing `{expected}`"),
                            ));
                        }

                        if keys.len() != 0 {
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

                                let Some(field) = strukt.fields.iter().find(|field| field.name == name) else {
                                    let name = name.map(|t| t.get(self.db)).unwrap_or("_");
                                    return Err(error!("no field `{name}` found for `{expected}`")
                                        .label(self.node_span(key), ""))
                                };

                                self.check_expr(value, field.typ).await?;
                            }
                        } else {
                            for (value, field) in values.zip(strukt.fields.iter()) {
                                self.check_expr(value, field.typ).await?;
                            }
                        }
                    }
                    TypeKind::Declared(_) => {
                        return Err(error!("TODO: resolve declared type: `{expected}`")
                            .label(self.node_span(expr), ""))
                    }
                    _ => {
                        return Err(error!("not a composite type: `{expected}`")
                            .label(self.node_span(typ), ""))
                    }
                }

                Ok(expected)
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
                        Ok(target_type)
                    }
                    _ => Err(error!("argument in type assertion must be an `interface`")
                        .label(self.node_span(base), "must be an interface")),
                }
            }

            Node::Unary(op, arg) => {
                let arg_type = self.infer_expr(arg).await?;
                match op {
                    syntax::UnaryOperator::Plus => {
                        if !arg_type.lookup(self.db).is_numeric() {
                            return Err(error!("the operator `+` expected a numeric type").label(
                                self.node_span(arg),
                                format!("this has type `{arg_type}`"),
                            ));
                        }
                        Ok(arg_type)
                    }
                    syntax::UnaryOperator::Minus => {
                        if !arg_type.lookup(self.db).is_signed() {
                            return Err(error!("the operator `-` expected a signed numeric type")
                                .label(
                                    self.node_span(arg),
                                    format!("this has type `{arg_type}`"),
                                ));
                        }
                        Ok(arg_type)
                    }
                    syntax::UnaryOperator::Xor => {
                        if !arg_type.lookup(self.db).is_integer() {
                            return Err(error!("the operator `^` expected an integer").label(
                                self.node_span(arg),
                                format!("this has type `{arg_type}`"),
                            ));
                        }
                        Ok(arg_type)
                    }
                    syntax::UnaryOperator::Not => {
                        if !arg_type.lookup(self.db).is_bool() {
                            return Err(error!("`!` expected a `bool`").label(
                                self.node_span(arg),
                                format!("this has type `{arg_type}`"),
                            ));
                        }
                        Ok(arg_type)
                    }
                    syntax::UnaryOperator::Deref => match arg_type.lookup(self.db) {
                        TypeKind::Pointer(inner) => Ok(*inner),
                        _ => Err(error!("can only dereference pointers")
                            .label(self.node_span(arg), format!("this has type `{arg_type}`"))),
                    },
                    syntax::UnaryOperator::Ref => Ok(TypeKind::Pointer(arg_type).insert(self.db)),
                    syntax::UnaryOperator::Recv => match arg_type.lookup(self.db) {
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
                            Ok(*inner)
                        }
                        _ => Err(error!("expected a channel")
                            .label(self.node_span(arg), format!("this has type `{arg_type}`"))),
                    },
                }
            }
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
                            if self.is_comparable(lhs, rhs) {
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
                            if self.is_ordered(lhs, rhs) {
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
                Ok(lhs)
            }
            Node::BinaryOp(_) => unreachable!("handled by `Node::Binary`"),

            Node::Function(signature, body) => {
                let func = self.check_function(signature, body).await?;
                Ok(TypeKind::Function(func).insert(self.db))
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
                        Ok(inner)
                    }
                    &TypeKind::Map(key, value) => {
                        self.check_expr(index, key).await?;
                        Ok(value)
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

                        Ok(inner)
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

                        Ok(inner)
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
            | Node::MethodElement(_, _) => Err(error!("types are not valid in expression context")
                .label(self.node_span(expr), "expected an expression")),

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

        // TODO: implement casts, in which case this could be a type (instead of an expression)
        let target_type = self.infer_expr(target).await?;

        match target_type.lookup(self.db) {
            TypeKind::Builtin(builtin) => {
                Err(error!("TODO: call builtin {builtin:?}").label(self.node_span(call_expr), ""))
            }
            TypeKind::Function(func) => {
                let arg_exprs = self.nodes.indirect(args);

                if args.len() == 1 && func.inputs > 1 {
                    return Err(
                        error!("TODO: multi-value call").label(self.node_span(arg_exprs[0]), "")
                    );
                }

                if func.inputs != args.len() {
                    return Err(error!("invalid number of arguments")
                        .label(
                            self.node_span(target),
                            format!("this function expected {} arguments", func.inputs),
                        )
                        .label(
                            self.range_span(args)
                                .unwrap_or_else(|| self.node_span(call_expr)),
                            format!("found {} arguments", args.len()),
                        ));
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

    /// Determines if the two types are comparable.
    fn is_comparable(&self, lhs: Type, rhs: Type) -> bool {
        if self.is_assignable(lhs, rhs) {
            if lhs.lookup(self.db).is_comparable(self.db) {
                return true;
            }
        } else if self.is_assignable(rhs, lhs) {
            if rhs.lookup(self.db).is_comparable(self.db) {
                return true;
            }
        }

        // not assignable
        false
    }

    /// Can `source` be assigned to a destination of type `target`?
    fn is_assignable(&self, target: Type, source: Type) -> bool {
        if target == source {
            return true;
        }

        match (target.lookup(self.db), source.lookup(self.db)) {
            (target, TypeKind::Untyped(ConstantKind::Boolean)) if target.is_bool() => true,
            (target, TypeKind::Untyped(ConstantKind::Integer)) if target.is_integer() => true,
            (target, TypeKind::Untyped(ConstantKind::Float)) if target.is_float() => true,
            (target, TypeKind::Untyped(ConstantKind::Complex)) if target.is_complex() => true,
            (target, TypeKind::Untyped(ConstantKind::String)) if target.is_string() => true,
            (target, TypeKind::Untyped(ConstantKind::Nil)) if target.is_nillable() => true,
            _ => false,
        }
    }

    /// Determines if the two types are ordered.
    fn is_ordered(&self, lhs: Type, rhs: Type) -> bool {
        if self.is_assignable(lhs, rhs) {
            if lhs.lookup(self.db).is_ordered() {
                return true;
            }
        } else if self.is_assignable(rhs, lhs) {
            if rhs.lookup(self.db).is_ordered() {
                return true;
            }
        }

        // not assignable
        false
    }
}
