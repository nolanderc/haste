use crate::{
    error,
    naming::{self, DeclId, DeclPath},
    syntax::{self, ChannelKind, ExprId, Node, NodeId, NodeView},
    typing::Field,
    Diagnostic, HashMap, Result,
};

use super::{FunctionType, InterfaceMethod, InterfaceType, StructType, Type, TypeKind, TypeList};

pub(super) struct TypingContext<'db> {
    pub db: &'db dyn crate::Db,
    pub ast: &'db syntax::File,
    pub references: &'db HashMap<NodeId, naming::Symbol>,
    pub nodes: &'db NodeView,

    pub path: DeclPath,

    /// The types of all references to global symbols.
    pub resolved: HashMap<naming::GlobalSymbol, Type>,

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
            resolved: HashMap::default(),
            local_types: HashMap::default(),
        })
    }

    /// Resolve the given type, but only fetch the needed dependencies.
    pub async fn resolve_precise(&mut self, typ: syntax::TypeId) -> Result<Type> {
        self.fetch_external_references([typ.node]).await?;
        self.resolve_type(typ)
    }

    /// Fetches the types of external references
    pub async fn fetch_external_references(
        &mut self,
        nodes: impl IntoIterator<Item = impl Into<NodeId>>,
    ) -> Result<()> {
        let mut external = HashMap::default();

        for node in nodes {
            self.nodes.visit_children(node, |node| {
                if let Some(&naming::Symbol::Global(global)) = self.references.get(&node) {
                    external
                        .entry(global)
                        .or_insert_with(|| super::symbol_type(self.db, global));
                }
            });
        }

        let mut errors = Vec::new();
        self.resolved.reserve(external.len());

        for (global, pending_type) in external {
            match pending_type.await {
                Ok(typ) => {
                    self.resolved.insert(global, typ);
                }
                Err(error) => errors.push(error),
            }
        }

        if !errors.is_empty() {
            return Err(Diagnostic::combine(errors));
        }

        Ok(())
    }

    pub async fn fetch_all_external_references(&mut self) -> Result<()> {
        let mut external = HashMap::default();

        for symbol in self.references.values().copied() {
            if let naming::Symbol::Global(global) = symbol {
                external
                    .entry(global)
                    .or_insert_with(|| super::symbol_type(self.db, global));
            }
        }

        let mut errors = Vec::new();
        self.resolved.reserve(external.len());

        for (global, pending_type) in external {
            match pending_type.await {
                Ok(typ) => {
                    self.resolved.insert(global, typ);
                }
                Err(error) => errors.push(error),
            }
        }

        if !errors.is_empty() {
            return Err(Diagnostic::combine(errors));
        }

        Ok(())
    }

    /// Get the type represented by the given syntax tree.
    fn resolve_type(&mut self, typ: syntax::TypeId) -> Result<Type> {
        let node = typ.node;
        match self.nodes.kind(node) {
            Node::Name(_) => match self.references[&node] {
                naming::Symbol::Local(local) => Ok(self.local_types[&local]),
                naming::Symbol::Global(global) => Ok(self.resolved[&global]),
            },
            Node::Selector(_, _) => {
                if let Some(naming::Symbol::Global(global)) = self.references.get(&node) {
                    return Ok(self.resolved[global]);
                }

                Err(error!("expression not valid in type context")
                    .label(self.ast.node_span(self.path.index, node), "expected a type"))
            }
            Node::Pointer(inner) => {
                let inner = self.resolve_type(inner)?;
                Ok(TypeKind::Pointer(inner).insert(self.db))
            }
            Node::Array(len, _inner) => {
                if let Some(_len) = len {
                    todo!("compute array length")
                } else {
                    Err(error!("cannot infer length of array").label(self.node_span(node), ""))
                }
            }
            Node::Slice(inner) => {
                let inner = self.resolve_type(inner)?;
                Ok(TypeKind::Slice(inner).insert(self.db))
            }
            Node::Map(key, value) => {
                let key = self.resolve_type(key)?;
                let value = self.resolve_type(value)?;
                Ok(TypeKind::Map(key, value).insert(self.db))
            }
            Node::Channel(kind, typ) => {
                let inner = self.resolve_type(typ)?;
                Ok(TypeKind::Channel(kind, inner).insert(self.db))
            }
            Node::FunctionType(signature) => {
                let func = self.resolve_signature(signature)?;
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

                            let typ = self.resolve_type(typ)?;
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

                            let signature = self.resolve_signature(signature)?;
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

    pub fn resolve_signature(&mut self, signature: syntax::Signature) -> Result<FunctionType> {
        let mut types = TypeList::with_capacity(signature.inputs_and_outputs().len());

        for node in self.nodes.indirect(signature.inputs_and_outputs()) {
            let param = self.nodes.parameter(*node);
            types.push(self.resolve_type(param.typ)?);
        }

        Ok(FunctionType {
            types,
            inputs: signature.inputs().len(),
        })
    }

    pub fn node_span(&mut self, node: impl Into<NodeId>) -> crate::span::Span {
        self.ast.node_span(self.path.index, node)
    }

    pub fn infer_assignment(&mut self, expr: ExprId) -> Result<TypeList> {
        let mut list = TypeList::new();

        match self.nodes.kind(expr) {
            Node::Unary(syntax::UnaryOperator::Recv, channel) => {
                let (_kind, inner) = self.infer_recv_channel(channel)?;
                list.push(inner);
                list.push(TypeKind::Bool.insert(self.db));
            }
            Node::Index(target, index) => {
                let (output, extra) = self.infer_index_type(target, index)?;
                list.push(output);
                if let Some(extra) = extra {
                    list.push(extra);
                }
            }
            Node::Call(target, args, spread) => {
                todo!("multi-value call")
            }
            Node::TypeAssertion(expr, typ) => {
                todo!("multi-value type assertion")
            }
            _ => list.push(self.infer_expr(expr)?),
        }

        Ok(list)
    }

    /// Check that the given expression is valid for the given type
    pub fn check_expr(&mut self, expr: ExprId, expected: Type) -> Result<()> {
        let inferred = self.infer_expr(expr)?;

        if let Err(error) = self.check_assignable(inferred, expected) {
            let span = self.node_span(expr);
            return Err(error!("{}", error).label(span, format!("expected `{expected}`")));
        }

        Ok(())
    }

    fn check_assignable(&mut self, found: Type, expected: Type) -> Result<(), String> {
        if found == expected {
            return Ok(());
        }

        Err(format!("incompatible types `{found}` and `{expected}`"))
    }

    pub fn infer_expr(&mut self, expr: ExprId) -> Result<Type> {
        match self.nodes.kind(expr) {
            Node::Name(_) => match self.references[&expr.node] {
                naming::Symbol::Local(local) => Ok(self.local_types[&local]),
                naming::Symbol::Global(global) => Ok(self.resolved[&global]),
            },
            Node::Selector(_, _) => todo!(),
            Node::Parameter(_) => todo!(),
            Node::Pointer(_) => todo!(),
            Node::Array(_, _) => todo!(),
            Node::Slice(_) => todo!(),
            Node::Map(_, _) => todo!(),
            Node::Channel(_, _) => todo!(),
            Node::FunctionType(_) => todo!(),
            Node::Struct(_) => todo!(),
            Node::Field(_, _, _) => todo!(),
            Node::EmbeddedField(_, _, _) => todo!(),
            Node::Interface(_) => todo!(),
            Node::MethodElement(_, _) => todo!(),
            Node::IntegerSmall(_) => todo!(),
            Node::FloatSmall(_) => todo!(),
            Node::ImaginarySmall(_) => todo!(),
            Node::Rune(_) => todo!(),
            Node::String(_) => todo!(),
            Node::Call(_, _, _) => todo!(),
            Node::Composite(_, _) => todo!(),
            Node::CompositeLiteral(_) => todo!(),
            Node::TypeAssertion(_, _) => todo!(),
            Node::Unary(_, _) => todo!(),
            Node::Binary(_) => todo!(),
            Node::BinaryOp(_) => todo!(),
            Node::Function(_, _) => todo!(),
            Node::Index(_, _) => todo!(),
            Node::SliceIndex(_, _, _) => todo!(),
            Node::SliceCapacity(_, _, _, _) => todo!(),
            Node::TypeDef(_) => todo!(),
            Node::TypeAlias(_) => todo!(),
            Node::TypeList(_) => todo!(),
            Node::ConstDecl(_, _, _) => todo!(),
            Node::ConstList(_) => todo!(),
            Node::VarDecl(_, _, _) => todo!(),
            Node::VarList(_) => todo!(),
            Node::Block(_) => todo!(),
            Node::Label(_, _) => todo!(),
            Node::Return(_) => todo!(),
            Node::ReturnMulti(_) => todo!(),
            Node::Assign(_, _) => todo!(),
            Node::AssignOp(_, _, _) => todo!(),
            Node::Increment(_) => todo!(),
            Node::Decrement(_) => todo!(),
            Node::Send(_) => todo!(),
            Node::Go(_) => todo!(),
            Node::Defer(_) => todo!(),
            Node::Break(_) => todo!(),
            Node::Continue(_) => todo!(),
            Node::Goto(_) => todo!(),
            Node::If(_, _, _, _) => todo!(),
            Node::Select(_) => todo!(),
            Node::SelectSend(_, _) => todo!(),
            Node::SelectRecv(_, _, _, _) => todo!(),
            Node::SelectDefault(_) => todo!(),
            Node::Switch(_, _, _) => todo!(),
            Node::TypeSwitch(_, _) => todo!(),
            Node::SwitchCase(_, _) => todo!(),
            Node::Fallthrough => todo!(),
            Node::For(_, _, _, _) => todo!(),
            Node::ForRangePlain(_, _) => todo!(),
            Node::ForRange(_, _, _, _, _) => todo!(),
        }
    }

    fn infer_recv_channel(&mut self, channel: ExprId) -> Result<(ChannelKind, Type)> {
        let typ = self.infer_expr(channel)?;
        match *typ.lookup(self.db) {
            TypeKind::Channel(kind, typ) if kind.is_recv() => Ok((kind, typ)),
            _ => Err(error!("unexpected type `{typ}`")
                .label(self.node_span(channel), "expected a receive channel")),
        }
    }

    fn infer_index_type(&mut self, target: ExprId, index: ExprId) -> Result<(Type, Option<Type>)> {
        let mut target_type = self.infer_expr(target)?;

        let typ = loop {
            match target_type.lookup(self.db) {
                TypeKind::Pointer(inner) => target_type = *inner,
                TypeKind::Slice(inner) => break self.check_array_index(*inner, None, index)?,
                TypeKind::Array(len, inner) => {
                    break self.check_array_index(*inner, Some(*len), index)?
                }
                TypeKind::String => {
                    let inner = TypeKind::Uint8.insert(self.db);
                    break self.check_array_index(inner, None, index)?;
                }

                TypeKind::Map(key, value) => {
                    self.check_expr(index, *key)?;
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

    fn check_array_index(&mut self, inner: Type, len: Option<u32>, index: ExprId) -> Result<Type> {
        let index_type = self.infer_expr(index)?;
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
}
