use smallvec::SmallVec;

use crate::{
    error,
    naming::{self, DeclId, DeclPath},
    syntax::{self, NodeId, NodeView},
    typing::Field,
    Diagnostic, HashMap, Result,
};

use super::{FunctionType, InterfaceMethod, StructType, Type, TypeKind, InterfaceType};

pub(super) struct TypingContext<'db> {
    pub db: &'db dyn crate::Db,
    pub ast: &'db syntax::File,
    pub references: &'db HashMap<NodeId, naming::Symbol>,
    pub nodes: &'db NodeView,

    pub decl: DeclId,
    pub path: DeclPath,

    /// The types of all references to global symbols.
    pub resolved: HashMap<naming::GlobalSymbol, Type>,
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
            decl,
            resolved: HashMap::default(),
        })
    }

    pub async fn resolve_precise(&mut self, typ: syntax::TypeId) -> Result<Type> {
        // collect all external references inside the type
        let mut external = HashMap::default();
        self.nodes.visit_children(typ, |node| {
            if let Some(&naming::Symbol::Global(global)) = self.references.get(&node) {
                external
                    .entry(global)
                    .or_insert_with(|| super::symbol_type(self.db, global));
            }
        });

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

        self.resolve(typ.node)
    }

    #[inline(always)]
    fn resolve(&mut self, node: impl Into<NodeId>) -> Result<Type> {
        self.resolve_impl(node.into())
    }

    #[inline(never)]
    fn resolve_impl(&mut self, node: NodeId) -> Result<Type> {
        match self.nodes.kind(node) {
            syntax::Node::Name(_) => match self.references[&node] {
                naming::Symbol::Local(_) => todo!("get local type"),
                naming::Symbol::Global(global) => Ok(self.resolved[&global]),
            },
            syntax::Node::Selector(_, _) => {
                if let Some(naming::Symbol::Global(global)) = self.references.get(&node) {
                    return Ok(self.resolved[global]);
                }

                Err(error!("expression not valid in type context")
                    .label(self.ast.node_span(self.path.index, node), "expected a type"))
            }
            syntax::Node::Pointer(inner) => {
                let inner = self.resolve(inner)?;
                Ok(TypeKind::Pointer(inner).insert(self.db))
            }
            syntax::Node::Array(len, _inner) => {
                if let Some(_len) = len {
                    todo!("compute array length")
                } else {
                    Err(error!("cannot infer length of array").label(self.node_span(node), ""))
                }
            }
            syntax::Node::Slice(inner) => {
                let inner = self.resolve(inner)?;
                Ok(TypeKind::Slice(inner).insert(self.db))
            }
            syntax::Node::Map(key, value) => {
                let key = self.resolve(key)?;
                let value = self.resolve(value)?;
                Ok(TypeKind::Map(key, value).insert(self.db))
            }
            syntax::Node::Channel(kind, typ) => {
                let inner = self.resolve(typ)?;
                Ok(TypeKind::Channel(kind, inner).insert(self.db))
            }
            syntax::Node::FunctionType(signature) => {
                let func = self.resolve_signature(signature)?;
                Ok(TypeKind::Function(func).insert(self.db))
            }
            syntax::Node::Struct(field_nodes) => {
                let mut fields = Vec::with_capacity(field_nodes.len());

                for &node in self.nodes.indirect(field_nodes) {
                    let kind = self.nodes.kind(node);
                    match kind {
                        syntax::Node::Field(name, typ, tag)
                        | syntax::Node::EmbeddedField(name, typ, tag) => {
                            let typ = self.resolve(typ)?;
                            fields.push(Field {
                                name: name.text,
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
            syntax::Node::Interface(elements) => {
                let mut methods = Vec::with_capacity(elements.len());

                for &node in self.nodes.indirect(elements) {
                    let kind = self.nodes.kind(node);
                    match kind {
                        syntax::Node::MethodElement(name, signature) => {
                            let Some(name) = name.text else {
                                return Err(error!("method names may not be blank")
                                    .label(self.ast.span(Some(self.path.index), name.span), "invalid method name"))
                            };
                            let signature = self.resolve_signature(signature)?;
                            methods.push(InterfaceMethod { name, signature });
                        }
                        _ => unreachable!("not a field"),
                    }
                }

                let methods = methods.into_boxed_slice();
                Ok(TypeKind::Interface(InterfaceType { methods }).insert(self.db))
            }

            kind => unreachable!("not a type: {:?}", kind),
        }
    }

    fn resolve_signature(&mut self, signature: syntax::Signature) -> Result<FunctionType> {
        let mut types = SmallVec::with_capacity(signature.inputs_and_outputs().len());

        for node in self.nodes.indirect(signature.inputs_and_outputs()) {
            types.push(self.resolve(*node)?);
        }

        Ok(FunctionType {
            types,
            inputs: signature.inputs().len(),
        })
    }

    fn node_span(&mut self, node: impl Into<NodeId>) -> crate::span::Span {
        self.ast.node_span(self.path.index, node)
    }
}
