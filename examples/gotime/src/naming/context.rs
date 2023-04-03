use smallvec::SmallVec;

use crate::common::Text;
use crate::index_map::IndexMap;
use crate::key::Key;
use crate::span::Span;
use crate::syntax::{self, ExprId, Node, NodeId, SpanId, StmtId};
use crate::{error, Diagnostic, HashMap, Result};

use super::{
    Builtin, DeclId, DeclName, DeclPath, FileMember, GlobalSymbol, Local, PackageId, Symbol,
};

pub struct NamingContext<'db> {
    db: &'db dyn crate::Db,
    ast: &'db syntax::File,
    decl: Key<syntax::Decl>,
    nodes: &'db syntax::NodeView,
    package: PackageId,

    local_scope: LocalScope,
    file_scope: &'db IndexMap<DeclName, FileMember>,
    package_scope: &'db IndexMap<DeclName, DeclPath>,

    diagnostics: Option<Diagnostic>,
    resolved: IndexMap<NodeId, Symbol>,
    labels: HashMap<Text, StmtId>,
}

impl<'db> NamingContext<'db> {
    pub async fn new(
        db: &'db dyn crate::Db,
        ast: &'db crate::syntax::File,
        decl: Key<syntax::Decl>,
        package: PackageId,
    ) -> Result<NamingContext<'db>> {
        let file_scope = super::file_scope(db, ast.source);
        let package_scope = super::package_scope(db, package.files);

        let nodes = &ast.declarations[decl].nodes;

        Ok(Self {
            db,
            ast,
            decl,
            nodes,
            package,

            package_scope: package_scope.await.as_ref()?,
            file_scope: file_scope.await.as_ref()?,
            local_scope: LocalScope::with_capacity(nodes.len()),

            diagnostics: None,
            resolved: IndexMap::with_capacity(nodes.len()),
            labels: HashMap::default(),
        })
    }

    pub fn finish(mut self) -> Result<IndexMap<NodeId, Symbol>> {
        if let Some(diagnostic) = self.diagnostics {
            return Err(diagnostic);
        }

        self.resolved.shrink_to_fit();
        Ok(self.resolved)
    }

    pub fn resolve_func(
        &mut self,
        signature: syntax::Signature,
        body: Option<syntax::FunctionBody>,
    ) {
        self.local_scope.enter();

        let parameters = signature.inputs_and_outputs();
        for &node in self.nodes.indirect(parameters) {
            let param = self.nodes.parameter(node);
            self.resolve_type(param.typ);
        }

        for &node in self.nodes.indirect(parameters) {
            let param = self.nodes.parameter(node);
            if let Some(name) = param.name {
                if let Some(name) = name.text {
                    // bind the name to the function scope
                    self.local_scope.insert_local(name, node, 0);
                }
            }
        }

        if let Some(body) = body {
            let old_labels = std::mem::take(&mut self.labels);

            self.labels.reserve(body.labels.len());
            for &label in self.nodes.indirect(body.labels) {
                match self.nodes.kind(label) {
                    Node::Label(name, _stmt) => {
                        let Some(name) = name.text else {
                            self.emit(error!("labels may not be blank").label(self.span(name.span), ""));
                            continue;
                        };

                        if let Some(previous) = self.labels.insert(name, label) {
                            self.emit(
                                error!("a label with the name `{name}` already exists")
                                    .label(self.node_span(previous), "old definition here")
                                    .label(self.node_span(label), "new definition here"),
                            )
                        }
                    }
                    _ => unreachable!(),
                }
            }

            self.resolve_block(body.block);

            self.labels = old_labels;
        }

        self.local_scope.exit();
    }

    fn resolve_block(&mut self, block: syntax::Block) {
        self.local_scope.enter();
        for stmt in self.nodes.indirect(block.statements) {
            self.resolve_stmt(*stmt);
        }
        self.local_scope.exit();
    }

    fn resolve_stmt(&mut self, stmt: StmtId) {
        self.resolve_node(stmt.node)
    }

    pub fn resolve_type(&mut self, typ: syntax::TypeId) {
        self.resolve_node(typ.node)
    }

    pub fn resolve_expr(&mut self, expr: syntax::ExprId) {
        self.resolve_node(expr.node)
    }

    fn resolve_range(&mut self, nodes: impl Into<syntax::NodeRange>) {
        for &node in self.nodes.indirect(nodes.into()) {
            self.resolve_node(node);
        }
    }

    fn resolve_node(&mut self, node: NodeId) {
        // TODO: don't visit the same nodes twice (for example in multiline const decls)

        match self.nodes.kind(node) {
            Node::Name(None) => {}
            Node::Name(Some(name)) => {
                if let Some(symbol) = self.find_symbol(name) {
                    self.resolved.insert(node, symbol);
                } else {
                    self.emit(
                        error!("undefined reference to `{}`", name).label(self.node_span(node), ""),
                    );
                }
            }
            Node::Selector(base, name) => {
                self.resolve_node(base);

                let Some(name) = name.text else {
                    self.emit(error!("a selector may not be blank").label(self.span(name.span), ""));
                    return;
                };

                let resolved = self.resolved.get(&base);
                if let Some(Symbol::Global(GlobalSymbol::Package(package))) = resolved {
                    if !name.get(self.db).starts_with(char::is_uppercase) {
                        self.emit(
                            error!("`{name}` exists but is private")
                                .label(self.node_span(node), ""),
                        );
                        return;
                    }

                    let decl = DeclId::new_plain(self.db, *package, name);
                    let symbol = Symbol::Global(GlobalSymbol::Decl(decl));
                    self.resolved.insert(node, symbol);
                }
            }

            Node::Parameter(_) => unreachable!(),

            Node::Pointer(typ) => self.resolve_type(typ),
            Node::Array(len, typ) => {
                if let Some(len) = len {
                    self.resolve_expr(len);
                }
                self.resolve_type(typ);
            }
            Node::Slice(typ) => self.resolve_type(typ),
            Node::Map(key, value) => {
                self.resolve_type(key);
                self.resolve_type(value);
            }
            Node::Channel(_kind, typ) => self.resolve_type(typ),
            Node::FunctionType(signature) => self.resolve_func(signature, None),

            Node::Struct(fields) => self.resolve_range(fields),
            Node::Field(_name, typ, _tag) => self.resolve_type(typ),
            Node::EmbeddedField(_name, typ, _tag) => self.resolve_type(typ),

            Node::Interface(elements) => self.resolve_range(elements),
            Node::MethodElement(_name, signature) => self.resolve_func(signature, None),

            Node::IntegerSmall(_)
            | Node::FloatSmall(_)
            | Node::ImaginarySmall(_)
            | Node::Rune(_)
            | Node::String(_) => {}

            Node::Call(target, args, _) => {
                self.resolve_expr(target);
                self.resolve_range(args.nodes);
            }
            Node::Composite(typ, composite) => {
                self.resolve_type(typ);
                self.resolve_composite(composite);
            }
            Node::CompositeLiteral(composite) => self.resolve_composite(composite),
            Node::TypeAssertion(expr, typ) => {
                self.resolve_expr(expr);
                if let Some(typ) = typ {
                    self.resolve_type(typ);
                }
            }
            Node::Unary(_op, expr) => self.resolve_expr(expr),

            Node::Binary(interleaved) => {
                for expr in self.nodes.indirect(interleaved).iter().step_by(2) {
                    self.resolve_expr(*expr);
                }
            }
            Node::BinaryOp(_op) => {}

            Node::Function(signature, body) => self.resolve_func(signature, Some(body)),
            Node::Index(array, index) => {
                self.resolve_expr(array);
                self.resolve_expr(index);
            }
            Node::SliceIndex(array, start, end) => {
                self.resolve_expr(array);
                if let Some(start) = start {
                    self.resolve_expr(start);
                }
                if let Some(end) = end {
                    self.resolve_expr(end);
                }
            }
            Node::SliceCapacity(array, start, end, cap) => {
                self.resolve_expr(array);
                if let Some(start) = start {
                    self.resolve_expr(start);
                }
                self.resolve_expr(end);
                self.resolve_expr(cap);
            }
            Node::TypeDef(spec) | Node::TypeAlias(spec) => {
                if let Some(name) = spec.name.text {
                    self.local_scope.insert_local(name, node, 0);
                }
                self.resolve_type(spec.inner);
            }
            Node::ConstDecl(names, typ, exprs) => {
                if let Some(typ) = typ {
                    self.resolve_type(typ);
                }
                self.resolve_range(exprs);
                for (i, &node) in self.nodes.indirect(names).iter().enumerate() {
                    let Node::Name(Some(name)) = self.nodes.kind(node) else { continue };
                    self.local_scope.insert_local(name, node, i as u16);
                }
            }
            Node::VarDecl(names, typ, exprs) => {
                if let Some(typ) = typ {
                    self.resolve_type(typ);
                }
                if let Some(exprs) = exprs {
                    self.resolve_range(exprs);
                }
                for (i, &name_node) in self.nodes.indirect(names).iter().enumerate() {
                    let Node::Name(name) = self.nodes.kind(name_node) else {
                        self.emit(error!("variable declaration must bind to an identifier")
                            .label(self.node_span(node), "expected an identifier"));
                        continue;
                    };
                    let Some(name) = name else { continue };
                    self.local_scope.insert_local(name, node, i as u16);
                }
            }
            Node::ConstList(list) | Node::VarList(list) | Node::TypeList(list) => {
                self.resolve_range(list)
            }

            Node::Block(block) => self.resolve_block(block),
            Node::Label(_name, stmt) => {
                // labels are registered in the function they are defined in
                self.resolve_stmt(stmt);
            }

            // TODO: should we resolve jump targets?
            Node::Return(None) => {}
            Node::Return(Some(expr)) => self.resolve_expr(expr),
            Node::ReturnMulti(exprs) => self.resolve_range(exprs),

            Node::Assign(targets, exprs) => {
                self.resolve_range(targets);
                self.resolve_range(exprs);
            }
            Node::AssignOp(target, _op, expr) => {
                self.resolve_expr(target);
                self.resolve_expr(expr);
            }
            Node::Increment(expr) | Node::Decrement(expr) => self.resolve_expr(expr),

            Node::Send(send) => {
                self.resolve_expr(send.channel);
                self.resolve_expr(send.value);
            }
            Node::Go(expr) => self.resolve_expr(expr),
            Node::Defer(expr) => self.resolve_expr(expr),

            Node::Break(None) | Node::Continue(None) => {}
            Node::Break(Some(label)) | Node::Continue(Some(label)) | Node::Goto(label) => {
                let Some(name) = label.text else {
                    self.emit(error!("the target label may not be blank").label(self.span(label.span), ""));
                    return;
                };
                if !self.labels.contains_key(&name) {
                    self.emit(
                        error!("target label `{name}` not found in scope")
                            .label(self.span(label.span), ""),
                    );
                }
            }

            Node::If(init, cond, block, els) => {
                self.local_scope.enter();
                if let Some(init) = init {
                    self.resolve_stmt(init);
                }
                self.resolve_expr(cond);
                self.resolve_block(block);
                if let Some(els) = els {
                    self.resolve_stmt(els);
                }
                self.local_scope.exit();
            }

            Node::Select(cases) => self.resolve_range(cases),
            Node::SelectSend(send, block) => {
                self.resolve_expr(send.channel);
                self.resolve_expr(send.value);
                self.resolve_block(block);
            }
            Node::SelectRecv(bindings, kind, value, block) => {
                self.resolve_expr(value);

                if let (Some(bindings), Some(kind)) = (bindings, kind) {
                    if kind.is_define() {
                        let mut get_name = |expr: ExprId| {
                            if let Node::Name(name) = self.nodes.kind(expr.node) {
                                name
                            } else {
                                self.emit(
                                    error!("invalid expression for variable declaration")
                                        .label(self.node_span(expr), "expected an identifier"),
                                );
                                None
                            }
                        };

                        let value = get_name(bindings.value);
                        let success = bindings.success.and_then(get_name);

                        self.local_scope.enter();

                        if let Some(value) = value {
                            self.local_scope.insert_local(value, node, 0)
                        }
                        if let Some(success) = success {
                            self.local_scope.insert_local(success, node, 1)
                        }
                        self.resolve_block(block);

                        self.local_scope.exit();
                    } else {
                        self.resolve_expr(bindings.value);
                        if let Some(success) = bindings.success {
                            self.resolve_expr(success);
                        }

                        self.resolve_block(block);
                    }
                }
            }
            Node::SelectDefault(block) => self.resolve_block(block),

            Node::Switch(init, expr, cases) => {
                self.local_scope.enter();
                if let Some(init) = init {
                    self.resolve_stmt(init);
                }
                if let Some(expr) = expr {
                    self.resolve_expr(expr);
                }
                self.resolve_range(cases);
                self.local_scope.exit();
            }
            Node::TypeSwitch(name, expr) => {
                self.resolve_expr(expr);
                if let Some(name) = name {
                    if let Some(text) = name.text {
                        // this will insert the binding into the parent switch's scope
                        self.local_scope.insert_local(text, node, 0);
                    }
                }
            }
            Node::SwitchCase(exprs, block) => {
                if let Some(exprs) = exprs {
                    self.resolve_range(exprs);
                }
                self.resolve_block(block);
            }
            Node::Fallthrough => {}

            Node::For(init, cond, post, block) => {
                self.local_scope.enter();
                if let Some(init) = init {
                    self.resolve_stmt(init);
                }
                if let Some(cond) = cond {
                    self.resolve_expr(cond);
                }
                if let Some(post) = post {
                    self.resolve_stmt(post);
                }
                self.resolve_block(block);
                self.local_scope.exit();
            }
            Node::ForRangePlain(list, block) => {
                self.resolve_expr(list);
                self.resolve_block(block);
            }
            Node::ForRange(index, value, kind, list, block) => {
                self.resolve_expr(list);

                if kind.is_define() {
                    let mut get_name = |expr: ExprId| {
                        if let Node::Name(name) = self.nodes.kind(expr) {
                            name
                        } else {
                            self.emit(
                                error!("invalid expression for variable declaration")
                                    .label(self.node_span(expr), "expected an identifier"),
                            );
                            None
                        }
                    };

                    let index = get_name(index);
                    let value = value.and_then(get_name);

                    self.local_scope.enter();
                    if let Some(name) = index {
                        self.local_scope.insert_local(name, node, 0)
                    }
                    if let Some(name) = value {
                        self.local_scope.insert_local(name, node, 1)
                    }
                    self.resolve_block(block);
                    self.local_scope.exit();
                } else {
                    self.resolve_expr(index);
                    if let Some(success) = value {
                        self.resolve_expr(success);
                    }
                    self.resolve_block(block);
                }
            }
        }
    }

    fn resolve_composite(&mut self, composite: syntax::CompositeRange) {
        for key in composite.keys(self.nodes) {
            if let Node::Name(Some(name)) = self.nodes.kind(key) {
                // this might be the name of a field, so might not exist in the current scope.
                if let Some(symbol) = self.find_symbol(name) {
                    self.resolved.insert(key.node, symbol);
                }
            } else {
                self.resolve_expr(key);
            }
        }

        for value in composite.values(self.nodes) {
            self.resolve_expr(value);
        }
    }

    fn find_symbol(&mut self, name: Text) -> Option<Symbol> {
        if let Some(node) = self.local_scope.get(name) {
            return Some(Symbol::Local(node));
        }

        let decl_name = DeclName::plain(name);

        if let Some(member) = self.file_scope.get(&decl_name) {
            let symbol = match *member {
                FileMember::Import(package, _) => GlobalSymbol::Package(package),
                FileMember::Decl(id) => GlobalSymbol::Decl(id),
            };
            return Some(Symbol::Global(symbol));
        }

        if self.package_scope.contains_key(&decl_name) {
            return Some(Symbol::Global(GlobalSymbol::Decl(DeclId::new(
                self.db,
                self.package,
                decl_name,
            ))));
        }

        if let Some(builtin) = Builtin::lookup(name.get(self.db)) {
            return Some(Symbol::Global(GlobalSymbol::Builtin(builtin)));
        }

        None
    }

    fn span(&self, id: SpanId) -> Span {
        self.ast.span(Some(self.decl), id)
    }

    fn node_span(&self, node: impl Into<NodeId>) -> Span {
        self.span(self.nodes.span(node))
    }

    fn emit(&mut self, diagnostic: Diagnostic) {
        if let Some(old) = &mut self.diagnostics {
            old.push(diagnostic);
        } else {
            self.diagnostics = Some(diagnostic);
        }
    }
}

struct LocalScope {
    slots: HashMap<Text, LocalSlot>,
    /// List of scopes which are currently active
    active: SmallVec<[ScopeId; 32]>,
    /// The most recent scope.
    next: ScopeId,
}

type ScopeId = u16;

pub struct LocalSlot {
    /// Index of the scope this symbols belongs to.
    scope: ScopeId,
    /// The actual symbol.
    local: Local,
    /// A shadowed symbol (if any).
    shadowed: Option<Box<LocalSlot>>,
}

impl LocalScope {
    fn with_capacity(cap: usize) -> Self {
        let mut symbols = HashMap::default();
        symbols.reserve(cap);
        Self {
            slots: symbols,
            active: SmallVec::default(),
            next: 0,
        }
    }

    fn get(&mut self, name: Text) -> Option<Local> {
        let symbol = self.slots.get_mut(&name)?;
        loop {
            if self.active.contains(&symbol.scope) {
                return Some(symbol.local);
            }

            *symbol = *symbol.shadowed.take()?;
        }
    }

    /// Register a symbol in the local scope.
    fn insert_local(&mut self, name: Text, node: NodeId, index: u16) {
        let scope = *self.active.last().unwrap();
        self.insert(name, Local { node, index }, scope)
    }

    fn insert(&mut self, name: Text, local: Local, scope: ScopeId) {
        let new = LocalSlot {
            scope,
            local,
            shadowed: None,
        };

        match self.slots.entry(name) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(new);
            }
            std::collections::hash_map::Entry::Occupied(mut entry) => {
                let slot = entry.get_mut();
                let old = std::mem::replace(slot, new);
                // the old slot could come back into scope:
                slot.shadowed = Some(Box::new(old));
            }
        }
    }

    /// Start a new scope.
    fn enter(&mut self) {
        self.active.push(self.next);
        self.next += 1;
    }

    /// Exit the current scope.
    fn exit(&mut self) {
        self.active.pop();
    }
}
