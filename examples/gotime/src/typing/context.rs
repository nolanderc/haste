use futures::{future::BoxFuture, FutureExt};
use smallvec::smallvec;

use crate::{
    common::Text,
    diagnostic::bug,
    error,
    index_map::IndexMap,
    naming::{self, DeclId, DeclPath},
    span::Span,
    syntax::{
        self, BinaryOperator, ChannelKind, ExprId, ExprRange, Node, NodeId, NodeRange, NodeView,
        SpanId, StmtId, TypeId,
    },
    typing::{Field, TypeClass},
    HashMap, Result,
};

use super::{
    eval::EvalContext, ConstValue, ConstantKind, FunctionType, InferredType, InterfaceMethod,
    InterfaceType, Signature, StructType, Type, TypeKind, TypeList,
};

pub(super) struct TypingContext<'db> {
    pub db: &'db dyn crate::Db,
    pub ast: &'db syntax::File,
    pub references: &'db IndexMap<NodeId, naming::Symbol>,
    pub nodes: &'db NodeView,

    pub decl: DeclId,
    pub path: DeclPath,

    pub types: super::TypingInfo,

    pub func: Option<FunctionData>,
}

pub struct FunctionData {
    output: FunctionOutputs,
    named_output: bool,
}

struct FunctionOutputs {
    nodes: NodeRange,
    types: TypeList,
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
            decl,
            path,
            types: super::TypingInfo {
                nodes: IndexMap::new(),
                locals: IndexMap::new(),
            },
            func: None,
        })
    }

    pub fn finish(self) -> Result<super::TypingInfo> {
        Ok(self.types)
    }

    async fn lookup_type(&self, typ: TypeId) -> Result<Option<Type>> {
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
            naming::Symbol::Local(local) => Ok(self.types.locals.get(&local).copied()),
            naming::Symbol::Global(global) => match super::signature(self.db, global).await? {
                Signature::Value(typ) => Ok(Some(InferredType::Value(typ))),
                Signature::Type(typ) => Ok(Some(InferredType::Type(typ))),
                Signature::Package(_) => Err(error!("packages cannot be used as values")
                    .label(self.node_span(node), "this is a package")),
            },
        }
    }

    /// Resolve the given type, but only fetch the needed dependencies.
    pub async fn resolve_precise(&mut self, typ: TypeId) -> Result<Type> {
        self.resolve_type_impl(typ).await
    }

    /// Get the type represented by the given syntax tree.
    pub fn resolve_type(&mut self, typ: TypeId) -> BoxFuture<Result<Type>> {
        self.resolve_type_impl(typ).boxed()
    }

    async fn resolve_type_impl(&mut self, typ: TypeId) -> Result<Type> {
        let resolved = self.resolve_type_raw(typ).await?;
        self.types
            .nodes
            .insert(typ.node, InferredType::Type(resolved));
        Ok(resolved)
    }

    async fn resolve_type_raw(&mut self, typ: TypeId) -> Result<Type> {
        let node = typ.node;
        match self.nodes.kind(node) {
            Node::Name(name) => match self.lookup_type(typ).await? {
                Some(typ) => Ok(typ),
                None => {
                    let name = name.map(|t| t.get(self.db)).unwrap_or("_");
                    Err(error!("missign typed declaration `{name}`").label(self.node_span(typ), ""))
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
            Node::Array(len_expr, inner) => {
                let inner_type = self.resolve_type(inner).await?;

                if let Some(len_expr) = len_expr {
                    let len = self.evaluate_integer(len_expr).await?;
                    match u64::try_from(len) {
                        Ok(len) => Ok(TypeKind::Array(len, inner_type).insert(self.db)),
                        Err(_) => Err(error!("array length cannot be negative").label(
                            self.node_span(len_expr),
                            format!("this evaluates to `{len}`"),
                        )),
                    }
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
                        _ => {
                            return Err(
                                bug!("not a field").label(self.node_span(node), "expected a field")
                            )
                        }
                    }
                }

                let fields = fields.into_boxed_slice();
                Ok(TypeKind::Struct(StructType { fields }).insert(self.db))
            }
            Node::Interface(elements) => {
                let mut methods = Vec::with_capacity(elements.len());

                let mut names = HashMap::<Text, SpanId>::default();
                names.reserve(elements.len());

                let mut register_method = |this: &Self, name, span: SpanId, signature| {
                    if let Some(previous) = names.insert(name, span) {
                        let old_span = this.ast.span(Some(this.path.index), previous);
                        let new_span = this.ast.span(Some(this.path.index), span);
                        return Err(error!("method names must be unique")
                            .label(old_span, format!("{name} first declared here"))
                            .label(new_span, "then redeclared here"));
                    }

                    methods.push(InterfaceMethod { name, signature });

                    Ok(())
                };

                for &node in self.nodes.indirect(elements) {
                    let kind = self.nodes.kind(node);
                    match kind {
                        Node::MethodElement(ident, signature) => {
                            let Some(name) = ident.text else {
                                return Err(error!("method names may not be blank")
                                    .label(self.ast.span(Some(self.path.index), ident.span), "invalid method name"))
                            };
                            let signature = self.resolve_signature(signature).await?;
                            register_method(self, name, ident.span, signature)?;
                        }

                        Node::Name(_) | Node::Selector(_, _) => {
                            let typ = self.resolve_type(syntax::TypeId::new(node)).await?;
                            let core_type = super::underlying_type(self.db, typ).await?;
                            let TypeKind::Interface(embedded) = core_type.lookup(self.db) else {
                                return Err(error!("expected an embedded interface")
                                    .label(self.node_span(node), format!("found `{}`", typ)))
                            };

                            let span = self.nodes.span(node);
                            let mut buffer = None;
                            for method in embedded.methods(self.db, &mut buffer) {
                                register_method(self, method.name, span, method.signature.clone())?;
                            }
                        }

                        _ => {
                            return Err(bug!("only methods and embedded interfaces allowed")
                                .label(self.node_span(node), ""))
                        }
                    }
                }

                methods.sort_by_key(|method| method.name.get(self.db));

                let methods = methods.into_boxed_slice();
                Ok(TypeKind::Interface(InterfaceType::Methods(methods)).insert(self.db))
            }

            _ => Err(bug!("only types allowed in type context")
                .label(self.node_span(typ), "expected a type")),
        }
    }

    pub async fn resolve_signature(
        &mut self,
        signature: syntax::Signature,
    ) -> Result<FunctionType> {
        let parameters = signature.inputs_and_outputs();

        let mut types = TypeList::with_capacity(parameters.len());

        let variadic_index = if signature.is_variadic() {
            Some(signature.inputs().len() - 1)
        } else {
            None
        };

        for (i, &node) in self.nodes.indirect(parameters).iter().enumerate() {
            let param = self.nodes.parameter(node);
            let typ = self.resolve_type(param.typ).await?;
            let local = naming::Local { node, index: 0 };

            let local_type = if Some(i) == variadic_index {
                TypeKind::Slice(typ).insert(self.db)
            } else {
                typ
            };

            self.types
                .locals
                .insert(local, InferredType::Value(local_type));

            types.push(typ);
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
        let typ = self.resolve_signature(signature).await?;

        let old_func = self.func.replace(FunctionData {
            output: FunctionOutputs {
                nodes: signature.outputs(),
                types: typ.outputs().into(),
            },
            named_output: {
                let mut named = false;
                for &node in self.nodes.indirect(signature.outputs()) {
                    named |= self.nodes.parameter(node).name.is_some();
                }
                named
            },
        });

        for &stmt in self.nodes.indirect(body.block.statements) {
            if let Err(error) = self.check_stmt(stmt).await {
                self.func = old_func;
                return Err(error);
            }
        }

        self.func = old_func;

        Ok(typ)
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
        self.check_assignable(expected, inferred, expr).await?;

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

    /// Infers the type of an expression without necessarily verifying that the entire expression
    /// is sound, which means we don't have to treverse the entire expression tree. This is most
    /// useful for determining the type of variables, as large constants (eg lookup tables) can
    /// take a while to type-check, which introduces bottlenecks into the compilation.
    pub async fn try_infer_expr_no_check(&mut self, expr: ExprId) -> Result<Option<Type>> {
        let typ = match self.nodes.kind(expr) {
            Node::Composite(typ, composite) => {
                self.infer_composite_init_no_check(typ, composite).await?
            }
            Node::Function(signature, _) => {
                let func = self.resolve_signature(signature).await?;
                TypeKind::Function(func).insert(self.db)
            }

            Node::Name(name) => {
                let inferred = self.infer_expr_name(expr, name).await?;
                self.as_value(expr, inferred)?
            }
            Node::Selector(base, ident) => {
                let inferred = self.infer_expr_selector(expr, ident, base).await?;
                self.as_value(expr, inferred)?
            }

            Node::IntegerSmall(_) => {
                TypeKind::Untyped(super::ConstantKind::Integer).insert(self.db)
            }
            Node::FloatSmall(_) => TypeKind::Untyped(super::ConstantKind::Float).insert(self.db),
            Node::ImaginarySmall(_) => {
                TypeKind::Untyped(super::ConstantKind::Complex).insert(self.db)
            }
            Node::Rune(_) => TypeKind::Untyped(super::ConstantKind::Rune).insert(self.db),
            Node::String(_) => TypeKind::Untyped(super::ConstantKind::String).insert(self.db),

            _ => return Ok(None),
        };

        Ok(Some(typ))
    }

    pub fn infer_expr(&mut self, expr: ExprId) -> BoxFuture<Result<Type>> {
        self.infer_expr_value(expr).boxed()
    }

    pub async fn infer_expr_value(&mut self, expr: ExprId) -> Result<Type> {
        let inferred = self.infer_expr_impl(expr).await?;
        self.as_value(expr, inferred)
    }

    fn as_value(&mut self, expr: ExprId, inferred: InferredType) -> Result<Type> {
        match inferred {
            InferredType::Value(typ) => Ok(typ),
            InferredType::Type(typ) => Err(error!("expected a value, but found a type")
                .label(self.node_span(expr), format!("found the type `{typ}`"))),
        }
    }

    pub fn infer_expr_any(&mut self, expr: ExprId) -> BoxFuture<Result<InferredType>> {
        self.infer_expr_impl(expr).boxed()
    }

    async fn infer_expr_impl(&mut self, expr: ExprId) -> Result<InferredType> {
        let inferred = self.infer_expr_raw(expr).await?;
        self.types.nodes.insert(expr.node, inferred);
        Ok(inferred)
    }

    async fn infer_expr_raw(&mut self, expr: ExprId) -> Result<InferredType> {
        use InferredType::Value;

        match self.nodes.kind(expr) {
            Node::Name(name) => self.infer_expr_name(expr, name).await,
            Node::Selector(base, ident) => self.infer_expr_selector(expr, ident, base).await,

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

                let core_type = super::underlying_type(self.db, base_type).await?;
                let TypeKind::Interface(interface) = core_type.lookup(self.db) else {
                    return Err(error!("argument in type assertion must be an `interface`")
                        .label(self.node_span(base), "must be an interface"))
                };

                self.check_interface_satisfied(base_type, interface, target_type)
                    .await
                    .map_err(|error| error.label(self.node_span(expr), "in this type assertion"))?;

                Ok(Value(target_type))
            }

            Node::Unary(op, arg) => match op {
                syntax::UnaryOperator::Plus => {
                    let arg_type = self.infer_expr(arg).await?;
                    let arg_class = arg_type.lookup(self.db).underlying_class(self.db).await?;
                    if !arg_class.is_numeric() {
                        return Err(error!("the operator `+` expected a numeric type")
                            .label(self.node_span(arg), format!("this has type `{arg_type}`")));
                    }
                    Ok(Value(arg_type))
                }
                syntax::UnaryOperator::Minus => {
                    let arg_type = self.infer_expr(arg).await?;
                    let arg_class = arg_type.lookup(self.db).underlying_class(self.db).await?;
                    if !arg_class.is_signed() {
                        return Err(error!("the operator `-` expected a signed numeric type")
                            .label(self.node_span(arg), format!("this has type `{arg_type}`")));
                    }
                    Ok(Value(arg_type))
                }
                syntax::UnaryOperator::Xor => {
                    let arg_type = self.infer_expr(arg).await?;
                    let arg_class = arg_type.lookup(self.db).underlying_class(self.db).await?;
                    if !arg_class.is_integer() {
                        return Err(error!("the operator `^` expected an integer")
                            .label(self.node_span(arg), format!("this has type `{arg_type}`")));
                    }
                    Ok(Value(arg_type))
                }
                syntax::UnaryOperator::Not => {
                    let arg_type = self.infer_expr(arg).await?;
                    let core_type = super::underlying_type(self.db, arg_type).await?;
                    if !core_type.lookup(self.db).is_bool() {
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
                syntax::UnaryOperator::Recv => self.infer_recv_expr(arg).await.map(Value),
            },
            Node::Binary(interleaved) => self.infer_binary_expr(interleaved).await,
            Node::BinaryOp(_) => unreachable!("handled by `Node::Binary`"),

            Node::Function(signature, body) => {
                let func = self.check_function(signature, body).await?;
                Ok(Value(TypeKind::Function(func).insert(self.db)))
            }

            Node::Index(target, index) => {
                let target_type = self.infer_expr(target).await?;
                let core_type = super::underlying_type(self.db, target_type).await?;
                match core_type.lookup(self.db) {
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
                    TypeKind::String => {
                        let index_type = self.infer_expr(index).await?;
                        if !index_type.lookup(self.db).is_integer() {
                            return Err(error!("expecetd an integer index").label(
                                self.node_span(index),
                                format!("this is of type `{index_type}`"),
                            ));
                        }
                        Ok(Value(TypeKind::Uint8.insert(self.db)))
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
                let check_integer = |this: &Self, index: ExprId, typ: Type| {
                    if !typ.lookup(this.db).is_integer() {
                        return Err(error!("expecetd an integer index")
                            .label(this.node_span(index), format!("this is of type `{typ}`"))
                            .label(this.node_span(expr), "in this slice operation"));
                    }
                    Ok(())
                };

                let target_type = self.infer_expr(target).await?;
                let core_type = super::underlying_type(self.db, target_type).await?;
                match core_type.lookup(self.db) {
                    &TypeKind::Array(_, inner) | &TypeKind::Slice(inner) => {
                        if let Some(start) = start {
                            let typ = self.infer_expr(start).await?;
                            check_integer(self, start, typ)?;
                        }

                        if let Some(end) = end {
                            let typ = self.infer_expr(end).await?;
                            check_integer(self, end, typ)?;
                        }

                        Ok(Value(TypeKind::Slice(inner).insert(self.db)))
                    }
                    TypeKind::String | TypeKind::Untyped(ConstantKind::String) => {
                        if let Some(start) = start {
                            let typ = self.infer_expr(start).await?;
                            check_integer(self, start, typ)?;
                        }

                        if let Some(end) = end {
                            let typ = self.infer_expr(end).await?;
                            check_integer(self, end, typ)?;
                        }

                        Ok(Value(target_type))
                    }
                    _ => Err(error!("cannot slice into value of type `{target_type}`")
                        .label(self.node_span(expr), "")
                        .label(self.node_span(target), "expected a slice or array")),
                }
            }
            Node::SliceCapacity(target, start, end, cap) => {
                let target_type = self.infer_expr(target).await?;
                let core_type = super::underlying_type(self.db, target_type).await?;
                match core_type.lookup(self.db) {
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
                let typ = self.resolve_type(TypeId::new(expr.node)).await?;
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

    async fn infer_recv_expr(&mut self, expr: ExprId) -> Result<Type> {
        let arg_type = self.infer_expr(expr).await?;
        match arg_type.lookup(self.db) {
            TypeKind::Channel(kind, inner) => {
                if !kind.is_recv() {
                    return Err(error!("cannot receive values from a send-only channel")
                        .label(self.node_span(expr), format!("this has type `{arg_type}`")));
                }
                Ok(*inner)
            }
            _ => Err(error!("expected a channel")
                .label(self.node_span(expr), format!("this has type `{arg_type}`"))),
        }
    }

    async fn infer_expr_selector(
        &mut self,
        expr: ExprId,
        ident: syntax::Identifier,
        base: NodeId,
    ) -> Result<InferredType> {
        if let Some(typ) = self.lookup_node(expr.node).await? {
            // qualified identifier
            return Ok(typ);
        }

        let Some(name) = ident.text else {
            return Err(error!("selector name must not be blank")
                .label(self.ast.span(Some(self.path.index), ident.span), ""))
        };

        let base_type = self.infer_expr(ExprId::new(base)).await?;

        let selection = super::resolve_selector(self.db, base_type, name).await?;

        if let Some(selection) = selection {
            match selection {
                super::Selection::Element(typ) => Ok(InferredType::Value(typ)),
                super::Selection::Method(typ) => {
                    // the result is the method signature, with the first parameter
                    // removed.
                    let TypeKind::Function(func) = typ.lookup(self.db) else { unreachable!() };
                    let applied_method = func.without_receiver();
                    Ok(InferredType::Value(
                        TypeKind::Function(applied_method).insert(self.db),
                    ))
                }
            }
        } else {
            Err(
                error!("no field or method `{name}` found for `{base_type}`")
                    .label(self.node_span(expr), ""),
            )
        }
    }

    async fn infer_expr_name(&mut self, expr: ExprId, name: Option<Text>) -> Result<InferredType> {
        if name.is_none() {
            return Ok(InferredType::Value(
                TypeKind::Interface(InterfaceType::Methods([].into())).insert(self.db),
            ));
        }

        match self.lookup_node(expr.node).await? {
            Some(typ) => Ok(typ),
            None => {
                let name = name.map(|t| t.get(self.db)).unwrap_or("_");
                Err(error!("missing typed declaration `{name}`").label(self.node_span(expr), ""))
            }
        }
    }

    async fn infer_binary_expr(&mut self, interleaved: ExprRange) -> Result<InferredType> {
        let interleaved = self.nodes.indirect(interleaved);

        let lhs_span = |this: &Self, index: usize| {
            this.node_span(interleaved[0])
                .join(this.node_span(interleaved[2 * index]))
        };

        let mut lhs = self.infer_expr(interleaved[0]).await?;
        for (index, pair) in interleaved[1..].chunks_exact(2).enumerate() {
            let op_node = pair[0];
            let rhs_node = pair[1];

            let Node::BinaryOp(op) = self.nodes.kind(pair[0]) else { unreachable!() };
            let rhs = self.infer_expr(pair[1]).await?;

            lhs = self
                .infer_binary_op(
                    lhs,
                    op,
                    rhs,
                    |this| lhs_span(this, index),
                    |this| this.node_span(op_node),
                    |this| this.node_span(rhs_node),
                )
                .await?;
        }
        Ok(InferredType::Value(lhs))
    }

    async fn infer_binary_op(
        &mut self,
        mut lhs: Type,
        op: BinaryOperator,
        mut rhs: Type,
        lhs_span: impl Fn(&Self) -> Span,
        op_span: impl Fn(&Self) -> Span,
        rhs_span: impl Fn(&Self) -> Span,
    ) -> Result<Type> {
        use syntax::BinaryOperator as BinOp;

        match op {
            BinOp::LogicalOr | BinOp::LogicalAnd => {
                if lhs.lookup(self.db).is_bool() && rhs.lookup(self.db).is_bool() {
                    return Ok(Type::untyped_bool(self.db));
                }
                Err(error!("incompatible types for `{op}`")
                    .label(op_span(self), "expected both operands to be of type `bool`")
                    .label(
                        lhs_span(self),
                        format!("this is found to be of type `{lhs}`"),
                    )
                    .label(
                        rhs_span(self),
                        format!("this is found to be of type `{rhs}`"),
                    ))
            }
            BinOp::Equal | BinOp::NotEqual => {
                if self.is_comparable(lhs, rhs).await? {
                    return Ok(Type::untyped_bool(self.db));
                }
                Err(error!("the operands are not comparable")
                    .label(op_span(self), "in this comparison")
                    .label(
                        lhs_span(self),
                        format!("this is found to be of type `{lhs}`"),
                    )
                    .label(
                        rhs_span(self),
                        format!("this is found to be of type `{rhs}`"),
                    ))
            }
            BinOp::Less | BinOp::LessEqual | BinOp::Greater | BinOp::GreaterEqual => {
                if self.is_ordered(lhs, rhs).await? {
                    return Ok(Type::untyped_bool(self.db));
                }
                Err(error!("the operands cannot be ordered")
                    .label(op_span(self), "in this comparison")
                    .label(
                        lhs_span(self),
                        format!("this is found to be of type `{lhs}`"),
                    )
                    .label(
                        rhs_span(self),
                        format!("this is found to be of type `{rhs}`"),
                    ))
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
                let mut lhs_kind = lhs.lookup(self.db);
                let mut rhs_kind = rhs.lookup(self.db);

                if lhs_kind.is_untyped() {
                    if !rhs_kind.is_untyped() && self.can_convert(rhs, lhs).await? {
                        lhs_kind = rhs_kind;
                        lhs = rhs;
                    }
                } else {
                    if rhs_kind.is_untyped() && self.can_convert(lhs, rhs).await? {
                        rhs_kind = lhs_kind;
                        rhs = lhs;
                    }
                }

                let lhs_class = lhs_kind.underlying_class(self.db).await?;
                let rhs_class = rhs_kind.underlying_class(self.db).await?;

                let overlap = lhs_class.intersection(rhs_class);
                let both_numeric = lhs_class.intersects(TypeClass::NUMERIC)
                    && rhs_class.intersects(TypeClass::NUMERIC);

                let valid_combination = match op {
                    BinOp::Add => both_numeric || overlap.intersects(TypeClass::STRING),
                    BinOp::Sub | BinOp::Mul | BinOp::Div => both_numeric,
                    BinOp::Rem | BinOp::BitOr | BinOp::BitXor | BinOp::BitAnd | BinOp::BitNand => {
                        overlap.intersects(TypeClass::INTEGER)
                    }
                    _ => unreachable!(),
                };

                if valid_combination {
                    if lhs == rhs || lhs_class.is_untyped() || rhs_class.is_untyped() {
                        if lhs_class.is_untyped() && rhs_class.is_untyped() {
                            let order = [
                                TypeClass::COMPLEX,
                                TypeClass::FLOAT,
                                TypeClass::RUNE,
                                TypeClass::INTEGER,
                            ];

                            for order in order {
                                if lhs_class.contains(order) {
                                    return Ok(lhs);
                                }
                                if rhs_class.contains(order) {
                                    return Ok(rhs);
                                }
                            }

                            return Ok(lhs);
                        } else if lhs_class.is_untyped() {
                            return Ok(rhs);
                        } else {
                            return Ok(lhs);
                        }
                    }
                }

                return Err(error!("incompatible types for `{op}`")
                    .label(
                        op_span(self),
                        "both operands must be of the same type ({classes:?})",
                    )
                    .label(
                        lhs_span(self),
                        format!("this is found to be of type `{lhs}`"),
                    )
                    .label(
                        rhs_span(self),
                        format!("this is found to be of type `{rhs}`"),
                    ));
            }

            BinOp::ShiftLeft | BinOp::ShiftRight => {
                let lhs_class = lhs.lookup(self.db).underlying_class(self.db).await?;
                let rhs_class = rhs.lookup(self.db).underlying_class(self.db).await?;

                if lhs_class.is_integer() && rhs_class.is_integer() {
                    return Ok(lhs);
                }

                return Err(error!("incompatible types for `{op}`")
                    .label(op_span(self), "both operands must be integers")
                    .label(
                        lhs_span(self),
                        format!("this is found to be of type `{lhs}`"),
                    )
                    .label(
                        rhs_span(self),
                        format!("this is found to be of type `{rhs}`"),
                    ));
            }
        }
    }

    async fn infer_composite_init_no_check(
        &mut self,
        typ: TypeId,
        composite: syntax::CompositeRange,
    ) -> Result<Type> {
        match self.nodes.kind(typ) {
            Node::Array(None, inner) => {
                let inner = self.resolve_type(inner).await?;
                Ok(TypeKind::Array(composite.len() as u64, inner).insert(self.db))
            }
            _ => self.resolve_type(typ).await,
        }
    }

    async fn infer_composite_init(
        &mut self,
        expr: ExprId,
        typ: TypeId,
        composite: syntax::CompositeRange,
    ) -> Result<Type> {
        let expected = self.infer_composite_init_no_check(typ, composite).await?;

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
                TypeKind::String | TypeKind::Untyped(ConstantKind::String) => {
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

    async fn evaluate_integer(&mut self, expr: ExprId) -> Result<i64> {
        match self.evaluate(expr).await? {
            ConstValue::Integer(value) => Ok(value.try_into().expect("handle large integers")),
            _ => Err(error!("cannot be represented as an integer").label(self.node_span(expr), "")),
        }
    }

    async fn evaluate_float(&mut self, expr: ExprId) -> Result<f64> {
        match self.evaluate(expr).await? {
            ConstValue::Integer(value) => Ok(value as f64),
            _ => Err(error!("cannot be represented as a float").label(self.node_span(expr), "")),
        }
    }

    async fn evaluate(&mut self, expr: ExprId) -> Result<ConstValue> {
        if !self.types.nodes.contains_key(&expr.node) {
            self.infer_expr(expr).await?;
        }

        let value = match self.nodes.kind(expr) {
            Node::IntegerSmall(value) => ConstValue::Integer(value.into()),
            _ => self.eval_context().eval(expr).await?,
        };

        // TODO: cache values to avoid repeated work
        Ok(value)
    }

    fn eval_context(&self) -> EvalContext {
        EvalContext {
            decl: self.decl,
            path: self.path,
            db: self.db,
            ast: self.ast,
            nodes: self.nodes,
            references: self.references,
            types: &self.types,
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
        let target_type = match self.infer_expr_any(target).await? {
            InferredType::Value(value_type) => value_type,
            InferredType::Type(target_type) => {
                let cast = self
                    .infer_cast(call_expr, target_type, args, spread)
                    .await?;
                return Ok(smallvec![cast]);
            }
        };

        let arg_exprs = self.nodes.indirect(args);
        let core_type = super::underlying_type(self.db, target_type).await?;

        match core_type.lookup(self.db) {
            TypeKind::Builtin(builtin) => {
                match builtin {
                    super::BuiltinFunction::Close => {
                        if arg_exprs.len() != 1 {
                            return Err(error!("`close` expects a single argument (chan)")
                                .label(self.node_span(call_expr), ""));
                        }
                        let typ = self.infer_expr(arg_exprs[0]).await?;
                        let core = super::underlying_type(self.db, typ).await?;
                        let TypeKind::Channel(kind, _) = core.lookup(self.db) else {
                            return Err(error!("can only close channels")
                                .label(self.node_span(arg_exprs[0]), "expected a channel"))
                        };

                        if !kind.is_send() {
                            return Err(error!("can only close send channels")
                                .label(self.node_span(arg_exprs[0]), ""));
                        }

                        Ok(smallvec![])
                    }

                    super::BuiltinFunction::Copy => {
                        if arg_exprs.len() != 2 {
                            return Err(error!("`copy` expects two arguments ([]T, []T)")
                                .label(self.node_span(call_expr), ""));
                        }

                        let dst = self.infer_expr(arg_exprs[0]).await?;
                        let core = super::underlying_type(self.db, dst).await?;
                        let &TypeKind::Slice(inner) = core.lookup(self.db) else {
                            return Err(error!("can only copy to slices")
                                .label(self.node_span(arg_exprs[0]), "expected a slice"))
                        };

                        let src = self.infer_expr(arg_exprs[1]).await?;

                        let is_byte_slice = *inner.lookup(self.db) == TypeKind::Uint8;
                        if is_byte_slice && src.lookup(self.db).is_string() {
                            // ok
                        } else {
                            self.check_assignable(dst, src, arg_exprs[1]).await?;
                        }

                        Ok(smallvec![TypeKind::Int.insert(self.db)])
                    }

                    super::BuiltinFunction::Append => {
                        if arg_exprs.is_empty() {
                            return Err(error!(
                                "`append` expects at least a single argument ([]T, ...T)"
                            )
                            .label(self.node_span(call_expr), ""));
                        }
                        let slice = self.infer_expr(arg_exprs[0]).await?;
                        let core = super::underlying_type(self.db, slice).await?;
                        let &TypeKind::Slice(inner) = core.lookup(self.db) else {
                            return Err(error!("can only append to slices")
                                .label(self.node_span(arg_exprs[0]), "expected a slice"))
                        };

                        let is_byte_slice = *inner.lookup(self.db) == TypeKind::Uint8;

                        let last_arg = arg_exprs.len() - 1;
                        for (i, &arg) in arg_exprs[..].iter().enumerate().skip(1) {
                            let arg_type = self.infer_expr(arg).await?;

                            if i == last_arg && spread.is_some() {
                                if is_byte_slice && arg_type.lookup(self.db).is_string() {
                                    // ok
                                } else {
                                    self.check_assignable(slice, arg_type, arg).await?;
                                }
                            } else {
                                self.check_assignable(inner, arg_type, arg).await?;
                            }
                        }

                        Ok(smallvec![slice])
                    }
                    super::BuiltinFunction::Delete => {
                        if arg_exprs.len() != 2 {
                            return Err(error!("`delete` expects two arguments (map[K]V, K)")
                                .label(self.node_span(call_expr), ""));
                        }
                        let map = self.infer_expr(arg_exprs[0]).await?;
                        let core = super::underlying_type(self.db, map).await?;
                        let &TypeKind::Map(key, _value) = core.lookup(self.db) else {
                            return Err(error!("can only append to slices")
                                .label(self.node_span(arg_exprs[0]), "expected a map"))
                        };

                        self.check_expr(arg_exprs[1], key).await?;

                        Ok(smallvec![])
                    }

                    super::BuiltinFunction::Complex => {
                        if arg_exprs.len() != 2 {
                            return Err(error!("`complex` expects two arguments (floatT, floatT)")
                                .label(self.node_span(call_expr), ""));
                        }

                        let real_expr = arg_exprs[0];
                        let imag_expr = arg_exprs[1];

                        let real = self.infer_expr(real_expr).await?;
                        let imag = self.infer_expr(imag_expr).await?;

                        let real_kind = real.lookup(self.db);
                        let imag_kind = imag.lookup(self.db);

                        let actual = if real_kind.is_untyped() && imag_kind.is_untyped() {
                            let _real_val = self.evaluate_float(real_expr).await?;
                            let _imag_val = self.evaluate_float(imag_expr).await?;
                            TypeKind::Untyped(ConstantKind::Complex).insert(self.db)
                        } else if real_kind.is_untyped() {
                            let actual = match imag.lookup(self.db) {
                                TypeKind::Float32 => TypeKind::Complex64,
                                TypeKind::Float64 => TypeKind::Complex128,
                                _ => {
                                    return Err(error!("expected a float")
                                        .label(self.node_span(imag_expr), ""))
                                }
                            };
                            self.check_assignable(imag, real, real_expr).await?;
                            actual.insert(self.db)
                        } else {
                            let actual = match real.lookup(self.db) {
                                TypeKind::Float32 => TypeKind::Complex64,
                                TypeKind::Float64 => TypeKind::Complex128,
                                _ => {
                                    return Err(error!("expected a float")
                                        .label(self.node_span(real_expr), ""))
                                }
                            };
                            self.check_assignable(real, imag, imag_expr).await?;
                            actual.insert(self.db)
                        };

                        Ok(smallvec![actual])
                    }

                    super::BuiltinFunction::Real | super::BuiltinFunction::Imag => {
                        if arg_exprs.len() != 1 {
                            return Err(error!("`{builtin}` expects one arguments (complex)")
                                .label(self.node_span(call_expr), ""));
                        }
                        let complex = self.infer_expr(arg_exprs[0]).await?;
                        let out = match complex.lookup(self.db) {
                            TypeKind::Untyped(ConstantKind::Complex) => complex,
                            TypeKind::Complex64 => TypeKind::Float32.insert(self.db),
                            TypeKind::Complex128 => TypeKind::Float64.insert(self.db),
                            _ => {
                                return Err(error!("expected a complex number")
                                    .label(self.node_span(arg_exprs[0]), ""))
                            }
                        };

                        Ok(smallvec![out])
                    }

                    super::BuiltinFunction::Cap => {
                        if arg_exprs.len() != 1 {
                            return Err(error!("`cap` expects a single argument (collection)")
                                .label(self.node_span(call_expr), ""));
                        }
                        let typ = self.infer_expr(arg_exprs[0]).await?;
                        let core = super::underlying_type(self.db, typ).await?;
                        if let Some(cap_typ) = core.lookup(self.db).capacity(self.db) {
                            Ok(smallvec![cap_typ])
                        } else {
                            Err(
                                error!("cannot only get capacity of arrays, slices and channels")
                                    .label(
                                        self.node_span(arg_exprs[0]),
                                        format!("this has type `{typ}`"),
                                    ),
                            )
                        }
                    }
                    super::BuiltinFunction::Len => {
                        if arg_exprs.len() != 1 {
                            return Err(error!("`len` expects a single argument (collection)")
                                .label(self.node_span(call_expr), ""));
                        }
                        let typ = self.infer_expr(arg_exprs[0]).await?;
                        let core = super::underlying_type(self.db, typ).await?;
                        if let Some(len_typ) = core.lookup(self.db).length(self.db) {
                            Ok(smallvec![len_typ])
                        } else {
                            Err(error!("cannot only get length of strings, arrays, slices, maps and channels")
                                .label(self.node_span(arg_exprs[0]), format!("this has type `{typ}`")))
                        }
                    }

                    super::BuiltinFunction::Make => {
                        if arg_exprs.is_empty() {
                            return Err(error!("`make` expects a type as its argument")
                                .label(self.node_span(call_expr), ""));
                        }

                        let typ = self.resolve_type(TypeId::new(arg_exprs[0].node)).await?;
                        let core_type = super::underlying_type(self.db, typ).await?;

                        async fn check_make_parameter(
                            this: &mut TypingContext<'_>,
                            expr: ExprId,
                            name: &str,
                        ) -> Result<()> {
                            let typ = this.infer_expr(expr).await?;
                            if !typ
                                .lookup(this.db)
                                .underlying_class(this.db)
                                .await?
                                .is_integer()
                            {
                                return Err(error!("{name} must be an integer").label(
                                    this.node_span(expr),
                                    format!("this is of type `{typ}`"),
                                ));
                            }
                            Ok(())
                        }

                        match core_type.lookup(self.db) {
                            TypeKind::Slice(_) => {
                                if arg_exprs.len() > 3 {
                                    return Err(error!("`make` accepts at most 3 arguments (type, length, capacity)")
                                        .label(self.node_span(call_expr), ""));
                                }
                                if let Some(&len) = arg_exprs.get(1) {
                                    check_make_parameter(self, len, "slice length").await?;
                                }
                                if let Some(&cap) = arg_exprs.get(2) {
                                    check_make_parameter(self, cap, "slice capacity").await?;
                                }
                            }

                            TypeKind::Map(_, _) => {
                                if arg_exprs.len() > 2 {
                                    return Err(error!(
                                        "`make` accepts at most 2 arguments (type, capacity)"
                                    )
                                    .label(self.node_span(call_expr), ""));
                                }
                                if let Some(&len) = arg_exprs.get(1) {
                                    check_make_parameter(self, len, "map capacity").await?;
                                }
                            }

                            TypeKind::Channel(_, _) => {
                                if arg_exprs.len() > 2 {
                                    return Err(error!(
                                        "`make` accepts at most 2 arguments (type, capacity)"
                                    )
                                    .label(self.node_span(call_expr), ""));
                                }
                                if let Some(&len) = arg_exprs.get(1) {
                                    check_make_parameter(self, len, "channel capacity").await?;
                                }
                            }

                            _ => {
                                return Err(error!("cannot `make` the type `{typ}`")
                                    .label(self.node_span(call_expr), ""))
                            }
                        }

                        Ok(smallvec![typ])
                    }
                    super::BuiltinFunction::New => {
                        if arg_exprs.len() != 1 {
                            return Err(error!("`new` expects a single type as its argument")
                                .label(self.node_span(call_expr), ""));
                        }
                        let typ = self.resolve_type(TypeId::new(arg_exprs[0].node)).await?;
                        Ok(smallvec![TypeKind::Pointer(typ).insert(self.db)])
                    }

                    super::BuiltinFunction::Panic => {
                        if arg_exprs.len() != 1 {
                            return Err(error!(
                                "`panic` expects a single argument (interface{{}})"
                            )
                            .label(self.node_span(call_expr), ""));
                        }
                        self.infer_expr(arg_exprs[0]).await?;
                        Ok(smallvec![])
                    }

                    super::BuiltinFunction::Recover => {
                        if !arg_exprs.is_empty() {
                            return Err(error!("`recover` does not accept any arguments")
                                .label(self.node_span(call_expr), ""));
                        }
                        let interface = InterfaceType::Methods([].into());
                        Ok(smallvec![TypeKind::Interface(interface).insert(self.db)])
                    }

                    _ => {
                        Err(bug!("TODO: call builtin {builtin:?}")
                            .label(self.node_span(call_expr), ""))
                    }
                }
            }
            TypeKind::Function(func) => {
                if args.len() == 1 && func.inputs > 1 {
                    let arg_call = arg_exprs[0];
                    if let Node::Call(arg_target, arg_args, arg_spread) = self.nodes.kind(arg_call)
                    {
                        let types = self
                            .infer_function_call_boxed(arg_call, arg_target, arg_args, arg_spread)
                            .await?;

                        if !func.enough_arguments(types.len()) {
                            return Err(
                                self.emit_invalid_argument_count(target, func, args, call_expr)
                            );
                        }

                        for (expected, arg) in func.inputs().zip(types) {
                            self.check_assignable(expected, arg, arg_call).await?;
                        }

                        return Ok(TypeList::from(func.outputs()));
                    }
                }

                if !func.enough_arguments(args.len()) {
                    return Err(self.emit_invalid_argument_count(target, func, args, call_expr));
                }

                for (expected, &arg) in func.inputs().zip(arg_exprs) {
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
                format!(
                    "this function expected {} arguments{}",
                    func.required_inputs(),
                    if func.variadic { " (or more)" } else { "" }
                ),
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
                format!("cannot convert `{source_type}` into `{target_type}`"),
            ));
        }

        Ok(target_type)
    }

    /// Determines if the two types are comparable.
    async fn is_comparable(&self, lhs: Type, rhs: Type) -> Result<bool> {
        if self.is_assignable(lhs, rhs).await? {
            if rhs.lookup(self.db).is_nil() && lhs.lookup(self.db).is_nillable(self.db).await? {
                return Ok(true);
            }
            return super::comparable(self.db, lhs).await;
        } else if self.is_assignable(rhs, lhs).await? {
            if lhs.lookup(self.db).is_nil() && rhs.lookup(self.db).is_nillable(self.db).await? {
                return Ok(true);
            }
            return super::comparable(self.db, rhs).await;
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
            (target, TypeKind::Untyped(ConstantKind::Nil))
                if target.is_nillable(self.db).await? =>
            {
                true
            }

            (_, TypeKind::Untyped(_)) if self.is_representable(target, source).await? => true,
            (
                &TypeKind::Channel(target_dir, target_inner),
                &TypeKind::Channel(source_dir, source_inner),
            ) if target_inner == source_inner && target_dir.is_subset_of(source_dir) => true,

            _ => {
                if self.is_arbitrary_type(target_kind) {
                    return Ok(true);
                }

                let target_core = super::underlying_type(self.db, target).await?;

                let target_core_kind = target_core.lookup(self.db);

                if let TypeKind::Interface(interface) = target_core_kind {
                    return self.is_interface_satisfied(interface, source).await;
                }

                if let TypeKind::Pointer(inner) = target_core_kind {
                    if let TypeKind::Interface(interface) = inner.lookup(self.db) {
                        return self.is_interface_satisfied(interface, source).await;
                    }
                }

                if !target_kind.is_declared() || !source_kind.is_declared() {
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

    async fn check_interface_satisfied(
        &self,
        target: Type,
        interface: &InterfaceType,
        source: Type,
    ) -> Result<()> {
        if !self.is_interface_satisfied(interface, source).await? {
            return Err(error!(
                "the type `{source}` does not implement the interface `{target}`"
            ));
        }

        Ok(())
    }

    async fn is_interface_satisfied(
        &self,
        interface: &InterfaceType,
        source: Type,
    ) -> Result<bool> {
        if interface.is_empty() {
            // all types trivially implement the empty interface
            return Ok(true);
        }

        super::satisfies_interface(self.db, source, interface.clone()).await
    }

    fn is_arbitrary_type(&self, kind: &TypeKind) -> bool {
        let TypeKind::Declared(decl) = kind else { return false };
        super::is_unsafe_decl(self.db, *decl, "ArbitraryType")
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
            return super::ordered(self.db, lhs).await;
        } else if self.is_assignable(rhs, lhs).await? {
            return super::ordered(self.db, rhs).await;
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

        let target = super::underlying_type(self.db, target).await?;

        let target_kind = target.lookup(self.db);
        let source_kind = source.lookup(self.db);

        let target_class = target_kind.class();
        let source_class = source_kind.class();

        let common_class = target_class.intersection(source_class);

        if common_class.intersects(TypeClass::NUMERIC) {
            // target and source are the same kind of numeric type (eg. two integers)
            return Ok(true);
        }

        match source_kind {
            TypeKind::String | TypeKind::Untyped(ConstantKind::String) => match target_kind {
                TypeKind::Slice(inner) => Ok(matches!(
                    inner.lookup(self.db),
                    TypeKind::Uint8 | TypeKind::Int32
                )),
                _ => Ok(false),
            },
            TypeKind::Slice(inner) => match inner.lookup(self.db) {
                TypeKind::Uint8 | TypeKind::Int32 if matches!(target_kind, TypeKind::String) => {
                    Ok(true)
                }
                _ => {
                    if let TypeKind::Pointer(pointer) = target_kind {
                        match pointer.lookup(self.db) {
                            TypeKind::Array(_, element) if element == inner => return Ok(true),
                            _ => {}
                        }
                    }
                    Ok(false)
                }
            },
            TypeKind::Pointer(_) => {
                if let TypeKind::Pointer(inner) = target.lookup(self.db) {
                    if self.is_arbitrary_type(inner.lookup(self.db)) {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Ok(false),
        }
    }

    fn check_stmt_boxed(&mut self, stmt: StmtId) -> BoxFuture<Result<()>> {
        self.check_stmt(stmt).boxed()
    }

    async fn check_stmt(&mut self, mut stmt: StmtId) -> Result<()> {
        loop {
            break match self.nodes.kind(stmt) {
                Node::ConstDecl(names, typ, exprs) => {
                    self.check_var_decl(stmt, names, typ, Some(exprs), true)
                        .await
                }
                Node::VarDecl(names, typ, exprs) => {
                    self.check_var_decl(stmt, names, typ, exprs, false).await
                }

                Node::TypeList(list) | Node::VarList(list) | Node::ConstList(list) => {
                    for &node in self.nodes.indirect(list) {
                        self.check_stmt_boxed(StmtId::new(node)).await?;
                    }
                    Ok(())
                }

                Node::TypeDef(_spec) => {
                    Err(bug!("handle inline type def").label(self.node_span(stmt), ""))
                }
                Node::TypeAlias(spec) => {
                    let typ = self.resolve_type(spec.inner).await?;
                    let local = naming::Local {
                        node: stmt.node,
                        index: 0,
                    };
                    self.types.locals.insert(local, InferredType::Type(typ));
                    Ok(())
                }

                Node::Assign(targets, values) => {
                    let target_exprs = self.nodes.indirect(targets);
                    let value_exprs = self.nodes.indirect(values);

                    let mut target_types = TypeList::with_capacity(target_exprs.len());
                    for target in target_exprs {
                        target_types.push(self.infer_expr(*target).await?);
                    }

                    if value_exprs.len() == 1 {
                        let value_types = self.infer_assignment(value_exprs[0]).await?;
                        if targets.len() > value_types.len() {
                            return Err(error!("invalid assignment")
                                .label(
                                    self.range_span(targets).unwrap(),
                                    format!("found {} targets", targets.len()),
                                )
                                .label(
                                    self.range_span(values).unwrap(),
                                    format!("found {} values", value_types.len()),
                                ));
                        }

                        for (target, (expected, value)) in target_exprs
                            .iter()
                            .zip(target_types.iter().zip(value_types))
                        {
                            self.check_assignable(*expected, value, *target).await?;
                        }
                    } else {
                        if value_exprs.len() != target_exprs.len() {
                            return Err(error!("invalid assignment")
                                .label(
                                    self.range_span(targets).unwrap(),
                                    format!("found {} targets", targets.len()),
                                )
                                .label(
                                    self.range_span(values).unwrap(),
                                    format!("found {} values", values.len()),
                                ));
                        }

                        for (value, expected) in value_exprs.iter().zip(target_types) {
                            self.check_expr(*value, expected).await?;
                        }
                    }

                    Ok(())
                }

                Node::Call(target, args, spread) => {
                    self.infer_function_call(ExprId::new(stmt.node), target, args, spread)
                        .await?;
                    Ok(())
                }

                Node::If(init, cond, block, els) => {
                    if let Some(init) = init {
                        self.check_stmt_boxed(init).await?;
                    }

                    self.check_expr(cond, TypeKind::Bool.insert(self.db))
                        .await?;
                    self.check_block_boxed(block).await?;

                    if let Some(els) = els {
                        stmt = els;
                        continue;
                    }
                    Ok(())
                }

                Node::Return(None) => self.check_return(stmt, &[]).await,
                Node::Return(Some(expr)) => self.check_return(stmt, &[expr]).await,
                Node::ReturnMulti(exprs) => {
                    self.check_return(stmt, self.nodes.indirect(exprs)).await
                }

                Node::For(init, cond, post, block) => {
                    if let Some(init) = init {
                        self.check_stmt_boxed(init).await?;
                    }
                    if let Some(cond) = cond {
                        self.check_expr(cond, TypeKind::Bool.insert(self.db))
                            .await?;
                    }
                    if let Some(post) = post {
                        self.check_stmt_boxed(post).await?;
                    }

                    self.check_block_boxed(block).await
                }

                Node::ForRange(first, second, syntax::AssignOrDefine::Assign, list, block) => {
                    let first_type = self.infer_expr(first).await?;
                    let second_type = match second {
                        Some(second) => Some(self.infer_expr(second).await?),
                        None => None,
                    };

                    let list_type = self.infer_expr(list).await?;
                    let list_core = super::underlying_type(self.db, list_type).await?;

                    let Some((first_expected, second_expected)) = self.range_bindings(list_core) else {
                        return Err(error!("cannot iterate over `{list_type}`")
                            .label(self.node_span(list), "expected array, slice, string, map or channel"))
                    };

                    self.check_range_bindings(
                        first_expected,
                        second_expected,
                        (first_type, first),
                        second_type.map(|typ| (typ, second.unwrap())),
                    )
                    .await?;

                    self.check_block_boxed(block).await
                }

                Node::ForRange(_first, second, syntax::AssignOrDefine::Define, list, block) => {
                    let list_type = self.infer_expr(list).await?;
                    let list_core = super::underlying_type(self.db, list_type).await?;

                    let Some((first_type, second_type)) = self.range_bindings(list_core) else {
                        return Err(error!("cannot iterate over `{list_type}`")
                            .label(self.node_span(list), "expected array, slice, string, map or channel"))
                    };

                    self.types.locals.insert(
                        naming::Local {
                            node: stmt.node,
                            index: 0,
                        },
                        InferredType::Value(first_type),
                    );

                    if let Some(second) = second {
                        let Some(second_type) = second_type else {
                            return Err(error!("range only yields one value")
                                .label(self.node_span(second), "unexpected binding"))
                        };

                        self.types.locals.insert(
                            naming::Local {
                                node: stmt.node,
                                index: 1,
                            },
                            InferredType::Value(second_type),
                        );
                    }

                    self.check_block_boxed(block).await
                }

                Node::ForRangePlain(list, block) => {
                    let list_type = self.infer_expr(list).await?;
                    let list_core = super::underlying_type(self.db, list_type).await?;
                    if self.range_bindings(list_core).is_none() {
                        return Err(error!("cannot iterate over `{list_type}`").label(
                            self.node_span(list),
                            "expected array, slice, string, map or channel",
                        ));
                    }
                    self.check_block_boxed(block).await
                }

                Node::Switch(init, cond, cases) => {
                    if let Some(init) = init {
                        self.check_stmt_boxed(init).await?;
                    }

                    let cond_type = if let Some(cond) = cond {
                        if let Node::TypeSwitch(binding, inner) = self.nodes.kind(cond) {
                            return Err(bug!("TODO: type switch").label(self.node_span(cond), ""));
                        } else {
                            self.infer_expr(cond).await?
                        }
                    } else {
                        TypeKind::Bool.insert(self.db)
                    };

                    for &case in self.nodes.indirect(cases) {
                        let Node::SwitchCase(exprs, block) = self.nodes.kind(case) else {
                            unreachable!("switch must only contain switch-cases")
                        };

                        let exprs = exprs.map(|exprs| self.nodes.indirect(exprs)).unwrap_or(&[]);
                        for &expr in exprs {
                            self.check_expr(expr, cond_type).await?;
                        }

                        self.check_block_boxed(block).await?;
                    }

                    Ok(())
                }

                Node::Label(_label, inner) => {
                    stmt = inner;
                    continue;
                }
                Node::Continue(_) | Node::Break(_) | Node::Goto(_) => Ok(()),

                Node::Block(block) => self.check_block_boxed(block).await,

                Node::Increment(expr) | Node::Decrement(expr) => {
                    let typ = self.infer_expr(expr).await?;
                    let core = super::underlying_type(self.db, typ).await?;
                    let class = core.lookup(self.db).class();
                    if !class.intersects(TypeClass::INTEGER | TypeClass::FLOAT) {
                        return Err(
                            error!("expected an integer or float").label(self.node_span(expr), "")
                        );
                    }
                    Ok(())
                }

                Node::AssignOp(lhs, op, rhs) => {
                    let lhs_type = self.infer_expr(lhs).await?;
                    let rhs_type = self.infer_expr(rhs).await?;

                    let output = self
                        .infer_binary_op(
                            lhs_type,
                            op,
                            rhs_type,
                            |this| this.node_span(lhs),
                            |this| this.node_span(lhs).join(this.node_span(rhs)),
                            |this| this.node_span(rhs),
                        )
                        .await?;

                    self.check_assignable(lhs_type, output, ExprId::new(stmt.node))
                        .await
                }

                Node::Defer(call) => {
                    let Node::Call(target, args, spread) = self.nodes.kind(call) else {
                        return Err(error!("only calls may be deferred")
                            .label(self.node_span(call), "expected a call expression"))
                    };
                    self.infer_function_call(call, target, args, spread).await?;
                    Ok(())
                }

                Node::Go(call) => {
                    let Node::Call(target, args, spread) = self.nodes.kind(call) else {
                        return Err(error!("only calls may be started in a goroutine")
                            .label(self.node_span(call), "expected a call expression"))
                    };
                    self.infer_function_call(call, target, args, spread).await?;
                    Ok(())
                }

                Node::Unary(syntax::UnaryOperator::Recv, expr) => {
                    self.infer_recv_expr(expr).await?;
                    Ok(())
                }

                kind => Err(bug!("not a statement: {:?}", kind)
                    .label(self.node_span(stmt), "expected a statement")),
            };
        }
    }

    fn range_bindings(&mut self, list_type: Type) -> Option<(Type, Option<Type>)> {
        match list_type.lookup(self.db) {
            TypeKind::String => Some((
                TypeKind::Int.insert(self.db),
                Some(TypeKind::Int32.insert(self.db)),
            )),
            &TypeKind::Slice(inner) | &TypeKind::Array(_, inner) => {
                Some((TypeKind::Int.insert(self.db), Some(inner)))
            }
            TypeKind::Pointer(inner) => {
                if let &TypeKind::Array(_, inner) = inner.lookup(self.db) {
                    Some((TypeKind::Int.insert(self.db), Some(inner)))
                } else {
                    None
                }
            }
            &TypeKind::Map(key, value) => Some((key, Some(value))),
            &TypeKind::Channel(_, inner) => Some((inner, None)),
            _ => None,
        }
    }

    async fn check_range_bindings(
        &mut self,
        first_expected: Type,
        second_expected: Option<Type>,
        first: (Type, ExprId),
        second: Option<(Type, ExprId)>,
    ) -> Result<()> {
        self.check_assignable(first_expected, first.0, first.1)
            .await?;

        if let Some((second_type, second)) = second {
            let Some(second_expected) = second_expected else {
                return Err(error!("range only yields one value")
                    .label(self.node_span(second), "unexpected binding"))
            };

            self.check_assignable(second_expected, second_type, second)
                .await?;
        }

        Ok(())
    }

    async fn check_var_decl(
        &mut self,
        stmt: StmtId,
        names: NodeRange,
        typ: Option<TypeId>,
        exprs: Option<ExprRange>,
        constant: bool,
    ) -> std::result::Result<(), crate::Diagnostic> {
        let required_names;
        let types = if let Some(typ) = typ {
            let expected = self.resolve_type(typ).await?;
            if let Some(exprs) = exprs {
                for &expr in self.nodes.indirect(exprs) {
                    self.check_expr(expr, expected).await?;
                }
            }
            required_names = names.len();
            smallvec![expected; names.len()]
        } else {
            let Some(exprs) = exprs else {
                return Err(error!("expected either expression or type")
                    .label(self.node_span(stmt), ""));
            };
            let exprs = self.nodes.indirect(exprs);
            if let [single] = exprs {
                required_names = 1;
                self.infer_assignment(*single).await?
            } else {
                let mut types = TypeList::with_capacity(exprs.len());
                for expr in exprs {
                    types.push(self.infer_expr(*expr).await?);
                }
                required_names = exprs.len();
                types
            }
        };

        if names.len() < required_names {
            return Err(error!("assignment mismatch")
                .label(
                    self.range_span(names).unwrap(),
                    format!("found {} names", names.len()),
                )
                .label(
                    self.range_span(exprs.unwrap()).unwrap(),
                    format!("but expression has type {}", crate::util::fmt_tuple(&types)),
                ));
        }

        for (index, typ) in (0..).zip(types) {
            let typ = if constant {
                typ
            } else {
                typ.value_type(self.db).map_err(|error| {
                    error.label(
                        self.node_span(self.nodes.indirect(exprs.unwrap())[index]),
                        "",
                    )
                })?
            };

            let local = naming::Local {
                node: stmt.node,
                index: index as u16,
            };
            self.types.locals.insert(local, InferredType::Value(typ));
        }

        Ok(())
    }

    async fn check_return(&mut self, stmt: StmtId, exprs: &[ExprId]) -> Result<()> {
        let func = self
            .func
            .as_ref()
            .expect("statements only allowed in functions");

        if exprs.is_empty() && func.named_output {
            return Ok(());
        }

        let output_nodes = func.output.nodes;
        let output_types = func.output.types.clone();

        if exprs.len() == 1 && output_types.len() > 1 {
            let types = self.infer_assignment(exprs[0]).await?;

            if types.len() < output_types.len() {
                return Err(error!("too few values in return")
                    .label(
                        self.node_span(exprs[0]),
                        format!("found {}", crate::util::fmt_tuple(&output_types)),
                    )
                    .label(
                        self.range_span(output_nodes).unwrap(),
                        format!("expected {}", crate::util::fmt_tuple(&output_types)),
                    ));
            }

            if types[..output_types.len()] != output_types[..] {
                return Err(error!("invalid return type").label(
                    self.node_span(stmt),
                    format!("expected {}", crate::util::fmt_tuple(&output_types)),
                ));
            }
        } else {
            if exprs.len() < output_types.len() {
                return Err(error!("too few values in return").label(
                    self.node_span(stmt),
                    format!("expected {}", crate::util::fmt_tuple(&output_types)),
                ));
            }

            if exprs.len() > output_types.len() {
                return Err(error!("too many values in return").label(
                    self.node_span(stmt),
                    format!("expected {}", crate::util::fmt_tuple(&output_types)),
                ));
            }

            for (&expr, typ) in exprs.iter().zip(output_types) {
                self.check_expr(expr, typ).await?;
            }
        }

        Ok(())
    }

    fn check_block_boxed(&mut self, block: syntax::Block) -> BoxFuture<Result<()>> {
        self.check_block(block).boxed()
    }

    async fn check_block(&mut self, block: syntax::Block) -> Result<()> {
        for stmt in self.nodes.indirect(block.statements) {
            self.check_stmt(*stmt).await?;
        }
        Ok(())
    }
}
