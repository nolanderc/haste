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
        self, AssignOrDefine, BinaryOperator, ChannelKind, ExprId, ExprRange, Node, NodeId,
        NodeRange, NodeView, SpanId, StmtId, TypeId, TypeRange,
    },
    typing::{Field, TypeClass},
    HashMap, Result,
};

use super::{
    eval::EvalContext, ConstValue, ConstantKind, FunctionType, InferredType, InterfaceError,
    InterfaceMethod, InterfaceType, Signature, StructType, Type, TypeKind, TypeList,
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
                constants: IndexMap::new(),
                redeclarations: IndexMap::default(),
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
            naming::Symbol::Local(local) => match self.types.locals.get(&local) {
                Some(typ) => Ok(Some(*typ)),
                None => {
                    let Some(actual) = self.types.redeclarations.get(&local) else { return Ok(None) };
                    Ok(self.types.locals.get(&actual).copied())
                }
            },
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
            Node::Pointer(TypeId { node })
            | Node::Unary(syntax::UnaryOperator::Deref, ExprId { node }) => {
                let inner = self.resolve_type(TypeId { node }).await?;
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
            Node::Unary(syntax::UnaryOperator::Recv, expr_type) => {
                let typ = self.resolve_type(TypeId::new(expr_type.node)).await?;
                let TypeKind::Channel(syntax::ChannelKind::SendRecv, inner) = typ.lookup(self.db) else {
                    return Err(error!("only types allowed in type context")
                        .label(self.node_span(expr_type), "expected a channel type"))
                };
                Ok(TypeKind::Channel(syntax::ChannelKind::Recv, *inner).insert(self.db))
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
                let mut names = HashMap::<Text, (FunctionType, SpanId)>::default();
                names.reserve(elements.len());

                let mut register_method =
                    |this: &Self, name, span: SpanId, signature| match names.entry(name) {
                        std::collections::hash_map::Entry::Vacant(entry) => {
                            entry.insert((signature, span));
                            Ok(())
                        }
                        std::collections::hash_map::Entry::Occupied(entry) => {
                            let (old_signature, old_span) = entry.get();
                            if *old_signature == signature {
                                return Ok(());
                            }

                            let old_span = this.ast.span(Some(this.path.index), *old_span);
                            let new_span = this.ast.span(Some(this.path.index), span);
                            Err(error!("method names must be unique")
                                .label(old_span, format!("{name} first declared here"))
                                .label(new_span, "then redeclared here"))
                        }
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

                let mut methods = Vec::with_capacity(names.len());

                for (name, (signature, _)) in names {
                    methods.push(InterfaceMethod { name, signature });
                }

                methods.sort_by_key(|method| method.name.get(self.db));

                let methods = methods.into_boxed_slice();
                Ok(TypeKind::Interface(InterfaceType::Methods(methods)).insert(self.db))
            }

            _ => Err(error!("only types allowed in type context")
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
        match self.nodes.kind(expr) {
            Node::CompositeLiteral(composite) => {
                return self
                    .check_composite_literal_boxed(expr, expected, composite, move |this| {
                        this.node_span(expr)
                    })
                    .await;
            }
            Node::Name(None) => {
                self.types
                    .nodes
                    .insert(expr.node, InferredType::Value(expected));
                return Ok(());
            }
            _ => (),
        }

        let inferred = self.infer_expr(expr).await?;
        self.check_assignable(expected, inferred, expr).await?;

        Ok(())
    }

    async fn check_assignable(
        &self,
        target: Type,
        source: Type,
        source_expr: ExprId,
    ) -> Result<()> {
        match self.is_assignable(target, source).await? {
            AssignResult::Ok => Ok(()),
            AssignResult::Incompatible => {
                let span = self.node_span(source_expr);
                Err(error!("type mismatch")
                    .label(span, format!("expected `{target}`, but found `{source}`")))
            }
            AssignResult::Interface(error) => {
                let span = self.node_span(source_expr);
                Err(
                    error!("`{source}` does not implement the interface `{target}`")
                        .label(span, format!("{}", error)),
                )
            }
        }
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

                let target_core = super::underlying_type(self.db, target_type).await?;
                if !matches!(target_core.lookup(self.db), TypeKind::Interface(_)) {
                    self.check_interface_satisfied(base_type, interface, target_type)
                        .await
                        .map_err(|error| {
                            error.label(self.node_span(expr), "required by this type assertion")
                        })?;
                }

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
                    if !arg_class.intersects(TypeClass::NUMERIC) {
                        return Err(error!("the operator `-` expected a numeric type")
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
                let (typ, _) = self.infer_index_type(target, index).await?;
                Ok(Value(typ))
            }
            Node::SliceIndex(target, start, end) => {
                macro_rules! check_integer {
                    ($index:expr, $typ:expr) => {{
                        let core = super::underlying_type(self.db, $typ).await?;
                        if core.lookup(self.db).is_integer() {
                            Ok(())
                        } else {
                            Err(error!("expected an integer index")
                                .label(
                                    self.node_span($index),
                                    format!("this is of type `{}`", $typ),
                                )
                                .label(self.node_span(expr), "in this slice operation"))
                        }
                    }};
                }

                let target_type = self.infer_expr(target).await?;
                let mut core_type = super::underlying_type(self.db, target_type).await?;

                if let &TypeKind::Pointer(inner) = core_type.lookup(self.db) {
                    let inner_core = super::underlying_type(self.db, inner).await?;
                    if let TypeKind::Array(_, _) = inner_core.lookup(self.db) {
                        core_type = inner_core;
                    }
                }

                match core_type.lookup(self.db) {
                    &TypeKind::Array(_, inner) => {
                        if let Some(start) = start {
                            let typ = self.infer_expr(start).await?;
                            check_integer!(start, typ)?;
                        }

                        if let Some(end) = end {
                            let typ = self.infer_expr(end).await?;
                            check_integer!(end, typ)?;
                        }

                        Ok(Value(TypeKind::Slice(inner).insert(self.db)))
                    }
                    &TypeKind::Slice(_) => {
                        if let Some(start) = start {
                            let typ = self.infer_expr(start).await?;
                            check_integer!(start, typ)?;
                        }

                        if let Some(end) = end {
                            let typ = self.infer_expr(end).await?;
                            check_integer!(end, typ)?;
                        }

                        Ok(Value(target_type))
                    }
                    TypeKind::String | TypeKind::Untyped(ConstantKind::String) => {
                        if let Some(start) = start {
                            let typ = self.infer_expr(start).await?;
                            check_integer!(start, typ)?;
                        }

                        if let Some(end) = end {
                            let typ = self.infer_expr(end).await?;
                            check_integer!(end, typ)?;
                        }

                        Ok(Value(target_type))
                    }
                    _ => Err(error!("cannot slice into value of type `{target_type}`")
                        .label(self.node_span(expr), "")
                        .label(self.node_span(target), "expected a slice or array")),
                }
            }
            Node::SliceCapacity(target, start, end, cap) => {
                macro_rules! check_integer {
                    ($index:expr, $typ:expr) => {{
                        let core = super::underlying_type(self.db, $typ).await?;
                        if core.lookup(self.db).is_integer() {
                            Ok(())
                        } else {
                            Err(error!("expected an integer index")
                                .label(
                                    self.node_span($index),
                                    format!("this is of type `{}`", $typ),
                                )
                                .label(self.node_span(expr), "in this slice operation"))
                        }
                    }};
                }

                let target_type = self.infer_expr(target).await?;
                let mut core_type = super::underlying_type(self.db, target_type).await?;

                if let &TypeKind::Pointer(inner) = core_type.lookup(self.db) {
                    let inner_core = super::underlying_type(self.db, inner).await?;
                    if let TypeKind::Array(_, _) = inner_core.lookup(self.db) {
                        core_type = inner_core;
                    }
                }

                let core_kind = core_type.lookup(self.db);
                match core_kind {
                    &TypeKind::Array(_, inner) => {
                        if let Some(start) = start {
                            let typ = self.infer_expr(start).await?;
                            check_integer!(start, typ)?;
                        }

                        let typ = self.infer_expr(end).await?;
                        check_integer!(end, typ)?;

                        let typ = self.infer_expr(cap).await?;
                        check_integer!(end, typ)?;

                        Ok(Value(TypeKind::Slice(inner).insert(self.db)))
                    }
                    TypeKind::Slice(_) => {
                        if let Some(start) = start {
                            let typ = self.infer_expr(start).await?;
                            check_integer!(start, typ)?;
                        }

                        let typ = self.infer_expr(end).await?;
                        check_integer!(end, typ)?;

                        let typ = self.infer_expr(cap).await?;
                        check_integer!(end, typ)?;

                        Ok(Value(target_type))
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
        let core = super::underlying_type(self.db, arg_type).await?;
        match core.lookup(self.db) {
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

        let base_type = self.infer_expr_any(ExprId::new(base)).await?;

        let selection = super::resolve_selector(self.db, base_type.inner(), name).await?;

        if let Some(selection) = selection {
            match base_type {
                InferredType::Value(_) => match selection {
                    super::Selection::Field(typ) | super::Selection::Method(typ) => {
                        Ok(InferredType::Value(typ))
                    }
                },
                InferredType::Type(typ) => match selection {
                    super::Selection::Method(method) => match method.lookup(self.db) {
                        TypeKind::Function(func) => {
                            let signature = func.with_receiever(typ);
                            let output = TypeKind::Function(signature).insert(self.db);
                            Ok(InferredType::Value(output))
                        }
                        _ => unreachable!("methods have function type"),
                    },
                    super::Selection::Field(_) => {
                        Err(error!("expected a method, but found a field")
                            .label(self.node_span(expr), "expected a method"))
                    }
                },
            }
        } else {
            Err(error!(
                "no field or method `{name}` found for `{}`",
                base_type.inner()
            )
            .label(self.node_span(expr), ""))
        }
    }

    async fn infer_expr_name(&mut self, expr: ExprId, name: Option<Text>) -> Result<InferredType> {
        if name.is_none() {
            return Err(error!("blank name not allowed in expression context")
                .label(self.node_span(expr), ""));
        }

        match self.lookup_node(expr.node).await? {
            Some(typ) => Ok(typ),
            None => {
                let name = name.map(|t| t.get(self.db)).unwrap_or("_");
                Err(error!(
                    "missing typed declaration `{name}` ({:?})",
                    self.references.get(&expr.node)
                )
                .label(self.node_span(expr), ""))
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
                let lhs_core = super::underlying_type(self.db, lhs).await?;
                let rhs_core = super::underlying_type(self.db, rhs).await?;

                if lhs_core.lookup(self.db).is_bool() && rhs_core.lookup(self.db).is_bool() {
                    let lhs_class = lhs.lookup(self.db).class();
                    let rhs_class = rhs.lookup(self.db).class();

                    if lhs_class.is_untyped() && rhs_class.is_untyped() {
                        return Ok(Type::untyped_bool(self.db));
                    } else if lhs_class.is_untyped() {
                        return Ok(rhs);
                    } else {
                        return Ok(lhs);
                    }
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

                Err(error!("incompatible types for `{op}`")
                    .label(op_span(self), "both operands must be of the same type")
                    .label(
                        lhs_span(self),
                        format!("this is found to be of type `{lhs}`"),
                    )
                    .label(
                        rhs_span(self),
                        format!("this is found to be of type `{rhs}`"),
                    ))
            }

            BinOp::ShiftLeft | BinOp::ShiftRight => {
                let lhs_class = lhs.lookup(self.db).underlying_class(self.db).await?;
                let rhs_class = rhs.lookup(self.db).underlying_class(self.db).await?;

                if lhs_class.is_integer() && rhs_class.is_integer() {
                    return Ok(lhs);
                }

                Err(error!("incompatible types for `{op}`")
                    .label(op_span(self), "both operands must be integers")
                    .label(
                        lhs_span(self),
                        format!("this is found to be of type `{lhs}`"),
                    )
                    .label(
                        rhs_span(self),
                        format!("this is found to be of type `{rhs}`"),
                    ))
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
        let core_type = super::underlying_type(self.db, typ).await?;
        match *core_type.lookup(self.db) {
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
        let typ = self.infer_expr(target).await?;
        let mut core_type = super::underlying_type(self.db, typ).await?;

        if let &TypeKind::Pointer(inner) = core_type.lookup(self.db) {
            let inner_core = super::underlying_type(self.db, inner).await?;
            if let TypeKind::Array(_, _) = inner_core.lookup(self.db) {
                core_type = inner_core;
            }
        }

        let typ = match core_type.lookup(self.db) {
            TypeKind::Slice(inner) => self.check_array_index(*inner, None, index).await?,
            TypeKind::Array(len, inner) => {
                self.check_array_index(*inner, Some(*len), index).await?
            }
            TypeKind::String | TypeKind::Untyped(ConstantKind::String) => {
                let inner = TypeKind::Uint8.insert(self.db);
                self.check_array_index(inner, None, index).await?
            }

            TypeKind::Map(key, value) => {
                self.check_expr(index, *key).await?;
                return Ok((*value, Some(TypeKind::Bool.insert(self.db))));
            }

            _ => {
                return Err(error!("cannot index into value of type `{typ}`").label(
                    self.node_span(target),
                    "expected an array, slice, string or map",
                ))
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
        let core = super::underlying_type(self.db, index_type).await?;
        match core.lookup(self.db) {
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
            TypeKind::Untyped(_) => {
                let value = self.evaluate_integer(index).await?;
                if let Some(len) = len {
                    if value < 0 || value as u64 >= len {
                        return Err(error!("index {value} out of bounds")
                            .label(self.node_span(index), format!("array has length {len}")));
                    }
                }
                return Ok(inner);
            }
            _ => {}
        }

        Err(error!("cannot index into an array using `{index_type}`")
            .label(self.node_span(index), "not representable by an `int`"))
    }

    async fn evaluate_integer(&mut self, expr: ExprId) -> Result<i64> {
        match self.evaluate(expr).await?.as_integer() {
            Some(value) => match value.to_i64() {
                Some(value) => Ok(value),
                None => {
                    Err(error!("integer is too large: {value}").label(self.node_span(expr), ""))
                }
            },
            _ => Err(error!("cannot be represented as an integer").label(self.node_span(expr), "")),
        }
    }

    async fn evaluate_float(&mut self, expr: ExprId) -> Result<f64> {
        match self.evaluate(expr).await? {
            ConstValue::Number(value) => {
                if value.imag().is_zero() {
                    Ok(value.real().to_f64())
                } else {
                    Err(error!("cannot be represented as a float").label(self.node_span(expr), ""))
                }
            }
            _ => Err(error!("cannot be represented as a float").label(self.node_span(expr), "")),
        }
    }

    async fn evaluate(&mut self, expr: ExprId) -> Result<ConstValue> {
        if !self.types.nodes.contains_key(&expr.node) {
            self.infer_expr(expr).await?;
        }

        let value = match self.nodes.kind(expr) {
            Node::IntegerSmall(value) => ConstValue::number(value),
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
                        if is_byte_slice
                            && src
                                .lookup(self.db)
                                .underlying_class(self.db)
                                .await?
                                .is_string()
                        {
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
                                let arg_core = super::underlying_type(self.db, arg_type).await?;
                                if is_byte_slice && arg_core.lookup(self.db).is_string() {
                                    // ok
                                } else {
                                    self.check_assignable(slice, arg_core, arg).await?;
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
                        if let Some(cap_typ) = core.lookup(self.db).capacity(self.db).await? {
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
                        if let Some(len_typ) = core.lookup(self.db).length(self.db).await? {
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

                    super::BuiltinFunction::Print | super::BuiltinFunction::Println => {
                        for expr in arg_exprs {
                            self.infer_expr(*expr).await?;
                        }
                        Ok(smallvec![])
                    }
                }
            }
            TypeKind::Function(func) => {
                if spread.is_some() && !func.variadic {
                    return Err(error!(
                        "spread oprator (...) may only be used for variadic functions"
                    )
                    .label(self.node_span(call_expr), ""));
                }

                if args.len() == 1 && spread.is_none() && (func.inputs > 1 || func.variadic) {
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

                let last_index = arg_exprs.len().saturating_sub(1);

                for (index, (expected, &arg)) in func.inputs().zip(arg_exprs).enumerate() {
                    if spread.is_some() && index == last_index {
                        self.check_expr(arg, TypeKind::Slice(expected).insert(self.db))
                            .await?;
                    } else {
                        self.check_expr(arg, expected).await?;
                    }
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
            return Err(error!("invalid conversion")
                .label(
                    self.node_span(entire_expr),
                    format!("cannot convert `{source_type}` into `{target_type}`"),
                )
                .label(
                    self.node_span(entire_expr),
                    format!(
                        "cannot convert `{}` into `{}`",
                        super::underlying_type(self.db, source_type).await?,
                        super::underlying_type(self.db, target_type).await?
                    ),
                ));
        }

        Ok(target_type)
    }

    /// Determines if the two types are comparable.
    async fn is_comparable(&self, lhs: Type, rhs: Type) -> Result<bool> {
        if self.is_assignable(lhs, rhs).await?.is_ok() {
            if rhs.lookup(self.db).is_nil() && lhs.lookup(self.db).is_nillable(self.db).await? {
                return Ok(true);
            }
            return super::comparable(self.db, lhs).await;
        } else if self.is_assignable(rhs, lhs).await?.is_ok() {
            if lhs.lookup(self.db).is_nil() && rhs.lookup(self.db).is_nillable(self.db).await? {
                return Ok(true);
            }
            return super::comparable(self.db, rhs).await;
        }

        // not assignable
        Ok(false)
    }

    /// Can `source` be assigned to a destination of type `target`?
    async fn is_assignable(&self, target: Type, source: Type) -> Result<AssignResult> {
        if target == source {
            return Ok(AssignResult::Ok);
        }

        let target_kind = target.lookup(self.db);
        let source_kind = source.lookup(self.db);

        let target_core = super::underlying_type(self.db, target).await?;
        let target_core_kind = target_core.lookup(self.db);

        Ok(match (target_core_kind, source_kind) {
            (target, TypeKind::Untyped(ConstantKind::Boolean)) if target.is_bool() => {
                AssignResult::Ok
            }
            (target, TypeKind::Untyped(ConstantKind::Integer)) if target.is_integer() => {
                AssignResult::Ok
            }
            (target, TypeKind::Untyped(ConstantKind::Rune)) if target.is_integer() => {
                AssignResult::Ok
            }
            (target, TypeKind::Untyped(ConstantKind::Float)) if target.is_float() => {
                AssignResult::Ok
            }
            (target, TypeKind::Untyped(ConstantKind::Complex)) if target.is_complex() => {
                AssignResult::Ok
            }
            (target, TypeKind::Untyped(ConstantKind::String)) if target.is_string() => {
                AssignResult::Ok
            }
            (target, TypeKind::Untyped(ConstantKind::Nil))
                if target.is_nillable(self.db).await? =>
            {
                AssignResult::Ok
            }

            (_, TypeKind::Untyped(_)) if self.is_representable(target, source).await? => {
                AssignResult::Ok
            }
            (
                &TypeKind::Channel(target_dir, target_inner),
                &TypeKind::Channel(source_dir, source_inner),
            ) if target_inner == source_inner && target_dir.is_subset_of(source_dir) => {
                AssignResult::Ok
            }

            _ => {
                if self.is_arbitrary_type(target_kind).await? {
                    return Ok(AssignResult::Ok);
                }

                if let &TypeKind::Declared(decl) = target_kind {
                    if super::inner_type_for_decl(self.db, decl).await? == source {
                        return Ok(AssignResult::Ok);
                    }
                }

                if let TypeKind::Interface(interface) = target_core_kind {
                    match self.is_interface_satisfied(interface, source).await? {
                        Ok(()) => return Ok(AssignResult::Ok),
                        Err(error) => return Ok(AssignResult::Interface(error)),
                    }
                }

                if let &TypeKind::Pointer(inner) = target_core_kind {
                    if let TypeKind::Interface(interface) = inner.lookup(self.db) {
                        match self.is_interface_satisfied(interface, source).await? {
                            Ok(()) => return Ok(AssignResult::Ok),
                            Err(error) => return Ok(AssignResult::Interface(error)),
                        }
                    }

                    if self.is_arbitrary_type(inner.lookup(self.db)).await?
                        && matches!(source_kind, TypeKind::Pointer(_))
                    {
                        return Ok(AssignResult::Ok);
                    }
                }

                if let &TypeKind::Slice(inner) = target_core_kind {
                    if self.is_arbitrary_type(inner.lookup(self.db)).await?
                        && matches!(source_kind, TypeKind::Slice(_))
                    {
                        return Ok(AssignResult::Ok);
                    }
                }

                if let &TypeKind::Pointer(inner) = source_kind {
                    if self.is_arbitrary_type(inner.lookup(self.db)).await?
                        && matches!(target_core_kind, TypeKind::Pointer(_))
                    {
                        return Ok(AssignResult::Ok);
                    }
                }

                if let &TypeKind::Slice(inner) = source_kind {
                    if self.is_arbitrary_type(inner.lookup(self.db)).await?
                        && matches!(target_core_kind, TypeKind::Slice(_))
                    {
                        return Ok(AssignResult::Ok);
                    }
                }

                if !target_kind.is_declared() || !source_kind.is_declared() {
                    let source_core = super::underlying_type(self.db, source).await?;
                    if target_core == source_core {
                        return Ok(AssignResult::Ok);
                    }
                }

                AssignResult::Incompatible
            }
        })
    }

    async fn check_interface_satisfied(
        &self,
        target: Type,
        interface: &InterfaceType,
        source: Type,
    ) -> Result<()> {
        match self.is_interface_satisfied(interface, source).await? {
            Ok(()) => Ok(()),
            Err(error) => Err(error!(
                "`{source}` does not implement the interface `{target}`: {error}"
            )),
        }
    }

    async fn is_interface_satisfied(
        &self,
        interface: &InterfaceType,
        source: Type,
    ) -> Result<Result<(), InterfaceError>> {
        if interface.is_empty() {
            // all types trivially implement the empty interface
            return Ok(Ok(()));
        }

        super::satisfies_interface(self.db, source, interface).await
    }

    async fn is_arbitrary_type(&self, kind: &TypeKind) -> Result<bool> {
        let TypeKind::Declared(decl) = kind else { return Ok(false) };
        super::is_unsafe_decl(self.db, *decl, "ArbitraryType").await
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
        if self.is_assignable(lhs, rhs).await?.is_ok() {
            return super::ordered(self.db, lhs).await;
        } else if self.is_assignable(rhs, lhs).await?.is_ok() {
            return super::ordered(self.db, rhs).await;
        }

        // not assignable
        Ok(false)
    }

    async fn can_convert(&mut self, target: Type, source: Type) -> Result<bool> {
        if self.is_assignable(target, source).await?.is_ok()
            || self.is_representable(target, source).await?
        {
            return Ok(true);
        }

        let target_core = super::underlying_type(self.db, target).await?;
        let source_core = super::underlying_type(self.db, source).await?;

        if target_core
            .structurally_equivalent(self.db, source_core)
            .await?
        {
            return Ok(true);
        }

        let target_kind = target_core.lookup(self.db);
        let source_kind = source_core.lookup(self.db);

        let target_class = target_kind.class();
        let source_class = source_kind.class();

        if target_class.intersects(TypeClass::NUMERIC)
            && source_class.intersects(TypeClass::NUMERIC)
        {
            return Ok(true);
        }

        if source_class.is_integer() {
            if matches!(target_kind, TypeKind::String) {
                return Ok(true);
            }
        }

        match source_kind {
            TypeKind::String | TypeKind::Untyped(ConstantKind::String) => match target_kind {
                TypeKind::Slice(inner) => Ok(matches!(
                    inner.lookup(self.db),
                    TypeKind::Uint8 | TypeKind::Int32
                )),
                _ => Ok(false),
            },
            &TypeKind::Slice(inner) => match inner.lookup(self.db) {
                TypeKind::Uint8 | TypeKind::Int32 if matches!(target_kind, TypeKind::String) => {
                    Ok(true)
                }
                _ => {
                    if let TypeKind::Pointer(pointer) = target_kind {
                        match pointer.lookup(self.db) {
                            &TypeKind::Array(_, element) if element == inner => return Ok(true),
                            _ => {}
                        }
                    }

                    if self.is_arbitrary_type(inner.lookup(self.db)).await? {
                        if let TypeKind::String = target_kind {
                            return Ok(true);
                        }
                    }

                    Ok(false)
                }
            },
            TypeKind::Pointer(source_inner) => {
                if let TypeKind::Pointer(target_inner) = target_kind {
                    if self.is_arbitrary_type(target_inner.lookup(self.db)).await? {
                        return Ok(true);
                    }

                    if super::underlying_type(self.db, *source_inner).await?
                        == super::underlying_type(self.db, *target_inner).await?
                    {
                        return Ok(true);
                    }
                }
                if self.is_arbitrary_type(source_inner.lookup(self.db)).await? {
                    if matches!(*target_kind, TypeKind::Uintptr | TypeKind::Pointer(_)) {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            TypeKind::Uintptr => {
                if let TypeKind::Pointer(inner) = target_kind {
                    if self.is_arbitrary_type(inner.lookup(self.db)).await? {
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

                Node::TypeDef(spec) | Node::TypeAlias(spec) => {
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

                        for (&target, value_type) in target_exprs.iter().zip(value_types) {
                            if let Node::Name(None) = self.nodes.kind(target) {
                                continue;
                            } else {
                                let target_type = self.infer_expr(target).await?;
                                self.check_assignable(target_type, value_type, target)
                                    .await?;
                            }
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

                        for (&target, &value) in target_exprs.iter().zip(value_exprs) {
                            if let Node::Name(None) = self.nodes.kind(target) {
                                self.infer_expr(value).await?;
                            } else {
                                let target_type = self.infer_expr(target).await?;
                                self.check_expr(value, target_type).await?;
                            }
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
                    let list_type = self.infer_expr(list).await?;
                    let list_core = super::underlying_type(self.db, list_type).await?;

                    let Some((first_expected, second_expected)) = self.range_bindings(list_core).await? else {
                        return Err(error!("cannot iterate over `{list_type}`")
                            .label(self.node_span(list), "expected array, slice, string, map or channel"))
                    };

                    self.check_range_bindings(first_expected, second_expected, first, second)
                        .await?;

                    self.check_block_boxed(block).await
                }

                Node::ForRange(_first, second, syntax::AssignOrDefine::Define, list, block) => {
                    let list_type = self.infer_expr(list).await?;
                    let list_core = super::underlying_type(self.db, list_type).await?;

                    let Some((first_type, second_type)) = self.range_bindings(list_core).await? else {
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
                    if self.range_bindings(list_core).await?.is_none() {
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
                        if let Node::TypeSwitch(_name, inner) = self.nodes.kind(cond) {
                            return self.check_type_switch(cond, inner, cases).await;
                        } else {
                            self.infer_expr(cond)
                                .await?
                                .value_type(self.db)
                                .map_err(|error| error.label(self.node_span(cond), ""))?
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

                        self.check_switch_case_boxed(block).await?;
                    }

                    Ok(())
                }
                Node::Fallthrough => Err(error!(
                    "fallthrough statements only allowed last in a switch case"
                )
                .label(self.node_span(stmt), "")),

                Node::Label(_label, None) => Ok(()),
                Node::Label(_label, Some(inner)) => {
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

                Node::Send(send) => self.check_channel_send(send).await,

                Node::Select(cases) => {
                    for &case in self.nodes.indirect(cases) {
                        let block = match self.nodes.kind(case) {
                            Node::SelectSend(send, block) => {
                                self.check_channel_send(send).await?;
                                block
                            }

                            Node::SelectRecv(bindings, kind, channel, block) => {
                                let (_kind, inner) = self.infer_recv_channel(channel).await?;

                                match kind {
                                    Some(AssignOrDefine::Assign) => {
                                        let bindings = bindings.unwrap();
                                        self.check_expr(bindings.value, inner).await?;
                                        if let Some(success) = bindings.success {
                                            let boolean = TypeKind::Bool.insert(self.db);
                                            self.check_expr(success, boolean).await?;
                                        }
                                    }
                                    Some(AssignOrDefine::Define) => {
                                        let bindings = bindings.unwrap();

                                        let value = naming::Local {
                                            node: case,
                                            index: 0,
                                        };
                                        self.types.locals.insert(value, InferredType::Value(inner));
                                        if bindings.success.is_some() {
                                            let success = naming::Local {
                                                node: case,
                                                index: 1,
                                            };
                                            let boolean = TypeKind::Bool.insert(self.db);
                                            self.types
                                                .locals
                                                .insert(success, InferredType::Value(boolean));
                                        }
                                    }
                                    None => {}
                                }

                                block
                            }

                            Node::SelectDefault(block) => block,

                            _ => unreachable!("only cases allowed within `select`"),
                        };

                        self.check_block_boxed(block).await?
                    }
                    Ok(())
                }

                kind => Err(bug!("not a statement: {:?}", kind)
                    .label(self.node_span(stmt), "expected a statement")),
            };
        }
    }

    async fn check_channel_send(&mut self, send: syntax::SendStmt) -> Result<()> {
        let channel_type = self.infer_expr(send.channel).await?;
        let core_type = super::underlying_type(self.db, channel_type).await?;
        let &TypeKind::Channel(kind, inner) = core_type.lookup(self.db) else {
            return Err(error!("can only send to channels")
                .label(self.node_span(send.channel), format!("`{channel_type}` is not a channel")))
        };
        if !kind.is_send() {
            return Err(error!("cannot send on a recieve-only channel").label(
                self.node_span(send.channel),
                "expected `chan` or `chan<-`, but found `<-chan`",
            ));
        }
        self.check_expr(send.value, inner).await
    }

    async fn check_type_switch(
        &mut self,
        type_switch: ExprId,
        inner: ExprId,
        cases: NodeRange,
    ) -> Result<()> {
        let inner_type = self.infer_expr(inner).await?;
        let core_type = super::underlying_type(self.db, inner_type).await?;
        let TypeKind::Interface(interface) = core_type.lookup(self.db) else {
            return Err(error!("argument in type switch must be an `interface`")
                .label(self.node_span(inner), "expected an interface"))
        };

        for (case_index, &case) in self.nodes.indirect(cases).iter().enumerate() {
            let Node::SwitchCase(types, block) = self.nodes.kind(case) else {
                unreachable!("switch must only contain switch-cases")
            };

            let types = types
                .map(|types| self.nodes.indirect(TypeRange::new(types.nodes)))
                .unwrap_or(&[]);

            let mut first_type = None;
            for &node in types {
                if let Node::Name(Some(name)) = self.nodes.kind(node) {
                    if name.get(self.db) == "nil" {
                        continue;
                    }
                }

                let typ = self.resolve_type(node).await?;
                first_type = first_type.or(Some(typ));

                let core = super::underlying_type(self.db, typ).await?;
                if !matches!(core.lookup(self.db), TypeKind::Interface(_)) {
                    if let Err(error) = self.is_interface_satisfied(interface, typ).await? {
                        return Err(error!(
                            "`{typ}` does not implement the interface `{inner_type}`"
                        )
                        .label(self.node_span(node), error.to_string())
                        .label(self.node_span(inner), "required because of this interface"));
                    }
                }
            }

            let binding_type = if types.len() == 1 && first_type.is_some() {
                first_type.unwrap()
            } else {
                inner_type
            };

            let local = naming::Local {
                node: type_switch.node,
                index: case_index as u16,
            };
            self.types
                .locals
                .insert(local, InferredType::Value(binding_type));

            self.check_block_boxed(block).await?;
        }

        Ok(())
    }

    async fn range_bindings(&mut self, list_type: Type) -> Result<Option<(Type, Option<Type>)>> {
        Ok(Some(match list_type.lookup(self.db) {
            TypeKind::String | TypeKind::Untyped(ConstantKind::String) => (
                TypeKind::Int.insert(self.db),
                Some(TypeKind::Int32.insert(self.db)),
            ),
            &TypeKind::Slice(inner) | &TypeKind::Array(_, inner) => {
                (TypeKind::Int.insert(self.db), Some(inner))
            }
            &TypeKind::Pointer(inner) => {
                let inner_core = super::underlying_type(self.db, inner).await?;
                if let &TypeKind::Array(_, inner) = inner_core.lookup(self.db) {
                    (TypeKind::Int.insert(self.db), Some(inner))
                } else {
                    return Ok(None);
                }
            }
            &TypeKind::Map(key, value) => (key, Some(value)),
            &TypeKind::Channel(_, inner) => (inner, None),
            _ => return Ok(None),
        }))
    }

    async fn check_range_bindings(
        &mut self,
        first_value: Type,
        second_value: Option<Type>,
        first: ExprId,
        second: Option<ExprId>,
    ) -> Result<()> {
        if self.nodes.kind(first) != Node::Name(None) {
            let first_type = self.infer_expr(first).await?;
            self.check_assignable(first_type, first_value, first)
                .await?;
        }

        if let Some(second) = second {
            let Some(second_value) = second_value else {
                return Err(error!("range only yields one value")
                    .label(self.node_span(second), "unexpected binding"))
            };

            if self.nodes.kind(second) != Node::Name(None) {
                let second_type = self.infer_expr(second).await?;
                self.check_assignable(second_type, second_value, second)
                    .await?;
            }
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
        let mut max_names = None;
        let mut values = Vec::new();

        let types = if let Some(typ) = typ {
            let expected = self.resolve_type(typ).await?;
            if let Some(exprs) = exprs {
                max_names = Some(exprs.len());
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
                let types = self.infer_assignment(*single).await?;

                if types.len() == 1 && constant && types[0].lookup(self.db).is_untyped() {
                    values.push(self.evaluate(*single).await?);
                }

                required_names = 1;
                max_names = Some(types.len());
                types
            } else {
                let mut types = TypeList::with_capacity(exprs.len());
                for &expr in exprs {
                    let typ = self.infer_expr(expr).await?;
                    types.push(typ);
                    if constant && typ.lookup(self.db).is_untyped() {
                        values.push(self.evaluate(expr).await?);
                    }
                }
                max_names = Some(exprs.len());
                required_names = exprs.len();
                types
            }
        };

        if let Some(max) = max_names {
            if names.len() > max {
                return Err(error!("too many bindings in expression")
                    .label(
                        self.range_span(names).unwrap(),
                        format!("found {} names", names.len()),
                    )
                    .label(
                        self.range_span(exprs.unwrap()).unwrap(),
                        format!("but expression provides {} values", types.len()),
                    ));
            }
        }

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

        let value_iter = values
            .into_iter()
            .map(Some)
            .chain(std::iter::repeat_with(|| None));

        let name_nodes = self.nodes.indirect(names);

        for (((index, name), mut typ), value) in (0..).zip(name_nodes).zip(types).zip(value_iter) {
            if !constant {
                typ = typ.value_type(self.db).map_err(|error| {
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
            let mut id = local;

            if let Some(naming::Symbol::Local(redecl)) = self.references.get(name) {
                let old_type = self.types.locals[redecl].value();
                let old_core = super::underlying_type(self.db, old_type).await?;
                let new_core = super::underlying_type(self.db, typ).await?;
                if old_core == new_core {
                    typ = old_type;
                    id = *self.types.redeclarations.get(redecl).unwrap_or(redecl);
                    self.types.redeclarations.insert(local, id);
                }
            }

            self.types.locals.insert(local, InferredType::Value(typ));

            if let Some(value) = value {
                self.types.constants.insert(id, value);
            }
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

            if types.len() != output_types.len() {
                return Err(error!("invalid number of return arguments")
                    .label(
                        self.node_span(exprs[0]),
                        format!("found {}", crate::util::fmt_tuple(&types)),
                    )
                    .label(
                        self.range_span(output_nodes).unwrap(),
                        format!("expected {}", crate::util::fmt_tuple(&output_types)),
                    ));
            }

            for (&found, &expected) in types.iter().zip(&output_types) {
                self.check_assignable(expected, found, exprs[0]).await?;
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

    fn check_switch_case_boxed(&mut self, block: syntax::Block) -> BoxFuture<Result<()>> {
        self.check_switch_case(block).boxed()
    }

    async fn check_switch_case(&mut self, block: syntax::Block) -> Result<()> {
        let last_index = block.statements.len().saturating_sub(1);
        for (i, &stmt) in self.nodes.indirect(block.statements).iter().enumerate() {
            if i == last_index && self.nodes.kind(stmt) == Node::Fallthrough {
                continue;
            }
            self.check_stmt(stmt).await?;
        }
        Ok(())
    }
}

enum AssignResult {
    Ok,
    Incompatible,
    Interface(InterfaceError),
}

impl AssignResult {
    /// Returns `true` if the assign result is [`Ok`].
    ///
    /// [`Ok`]: AssignResult::Ok
    #[must_use]
    fn is_ok(&self) -> bool {
        matches!(self, Self::Ok)
    }
}
