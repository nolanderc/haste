use haste::DatabaseExt;

use super::*;

use std::fmt::Write;

pub struct PrettyWriter<W> {
    writer: W,
    indent: usize,
    needs_indent: bool,
}

impl<W> PrettyWriter<W> {
    pub fn new(writer: W) -> Self {
        Self {
            writer,
            indent: 0,
            needs_indent: true,
        }
    }

    fn indented<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.indent += 4;
        let output = f(self);
        self.indent -= 4;
        output
    }

    fn dedented<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let previous = self.indent;
        self.indent = previous.saturating_sub(4);
        let output = f(self);
        self.indent = previous;
        output
    }
}

impl<W: Write> PrettyWriter<W> {
    fn write_indent(&mut self) -> std::fmt::Result {
        static SPACES: &str = match std::str::from_utf8(&[b' '; 256]) {
            Ok(text) => text,
            Err(_) => unreachable!(),
        };

        let mut count = self.indent;
        while count > 0 {
            let now = count.min(SPACES.len());
            let spaces = &SPACES[..now];
            self.writer.write_str(spaces)?;
            count -= now;
        }

        Ok(())
    }
}

impl<W> Write for PrettyWriter<W>
where
    W: Write,
{
    fn write_str(&mut self, mut text: &str) -> std::fmt::Result {
        while !text.is_empty() {
            if self.needs_indent {
                self.needs_indent = false;
                self.write_indent()?;
            }

            let Some(line_end) = text.find('\n') else {
                self.writer.write_str(text)?;
                break;
            };

            let (line, rest) = text.split_at(line_end + 1);
            self.writer.write_str(line)?;
            self.needs_indent = true;
            text = rest;
        }

        Ok(())
    }
}

impl File {
    pub fn display_pretty<'a>(&'a self, db: &'a dyn crate::Db) -> impl std::fmt::Display + 'a {
        db.fmt(crate::util::display_fn(move |f| {
            let mut writer = PrettyWriter::new(f);
            self.write_pretty(&mut writer)
        }))
    }

    fn write_pretty(&self, out: &mut PrettyWriter<impl Write>) -> std::fmt::Result {
        writeln!(out, "package {}", self.package)?;
        if self.imports.len() > 1 {
            writeln!(out)?;
            writeln!(out, "import (")?;
            out.indented(|out| {
                for import in self.imports.iter() {
                    write!(out, "{}", import)?;
                }
                Ok(())
            })?;
            writeln!(out, ")")?;
        } else if let Some(import) = self.imports.iter().next() {
            writeln!(out)?;
            write!(out, "import {}", import)?;
        }

        for decl in self.declarations.iter() {
            writeln!(out)?;
            decl.write_pretty(out)?;
            writeln!(out)?;
        }

        Ok(())
    }
}

impl std::fmt::Display for Import {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.name {
            PackageName::Inherit => {}
            PackageName::Implicit => write!(f, ". ")?,
            PackageName::Name(name) => write!(f, "{name} ")?,
        }
        writeln!(f, "{:?}", self.path.text)
    }
}

impl Decl {
    fn write_pretty(&self, out: &mut PrettyWriter<impl Write>) -> std::fmt::Result {
        match &self.kind {
            DeclKind::Function(func) => func.write_pretty(out, &self.nodes, false),
            DeclKind::Method(func) => func.write_pretty(out, &self.nodes, true),
            DeclKind::Type(decl) => write_node(out, &self.nodes, *decl),
            DeclKind::Const(decl) => write_node(out, &self.nodes, *decl),
            DeclKind::Var(decl) => write_node(out, &self.nodes, *decl),
        }
    }
}

impl FuncDecl {
    fn write_pretty(
        &self,
        out: &mut print::PrettyWriter<impl Write>,
        nodes: &NodeView,
        is_method: bool,
    ) -> std::fmt::Result {
        let inputs = nodes.indirect(self.signature.inputs());
        let outputs = nodes.indirect(self.signature.outputs());

        write!(out, "func ")?;
        if is_method {
            let receiver = nodes.parameter(inputs[0]);
            write!(out, "(")?;
            if let Some(name) = receiver.name {
                write!(out, "{name} ")?;
            }
            write_node(out, nodes, receiver.typ.node)?;
            write!(out, ") ")?;
        }

        write!(out, "{}", self.name)?;
        write_signature(out, nodes, &inputs[is_method as usize..], outputs)?;

        if let Some(body) = self.body {
            write!(out, " ")?;
            write_block(out, nodes, body.block)?;
        }

        Ok(())
    }
}

fn write_signature(
    out: &mut PrettyWriter<impl Write>,
    nodes: &NodeView,
    inputs: &[NodeId],
    outputs: &[NodeId],
) -> std::fmt::Result {
    write!(out, "(")?;
    write_list(out, inputs, |out, &input| {
        write_parameter(out, nodes, nodes.parameter(input))
    })?;
    write!(out, ")")?;

    if !outputs.is_empty() {
        write!(out, " ")?;
        if outputs.len() == 1 {
            let output = nodes.parameter(outputs[0]);
            if output.name.is_none() {
                write_node(out, nodes, output.typ.node)?;
            } else {
                write!(out, "(")?;
                write_parameter(out, nodes, output)?;
                write!(out, ")")?;
            }
        } else {
            write!(out, "(")?;
            write_list(out, outputs, |out, &output| {
                write_parameter(out, nodes, nodes.parameter(output))
            })?;
            write!(out, ")")?;
        }
    }

    Ok(())
}

fn write_parameter(
    out: &mut PrettyWriter<impl Write>,
    nodes: &NodeView,
    param: Parameter,
) -> std::fmt::Result {
    if let Some(name) = param.name {
        write!(out, "{name} ")?;
    }
    write_node(out, nodes, param.typ.node)
}

fn write_list<W: Write, T>(
    out: &mut PrettyWriter<W>,
    items: impl IntoIterator<Item = T>,
    mut f: impl FnMut(&mut PrettyWriter<W>, T) -> std::fmt::Result,
) -> std::fmt::Result {
    for (i, item) in items.into_iter().enumerate() {
        if i != 0 {
            write!(out, ", ")?;
        }
        f(out, item)?;
    }

    Ok(())
}

fn write_node_list<W: Write>(
    out: &mut PrettyWriter<W>,
    nodes: &NodeView,
    range: NodeRange,
) -> std::fmt::Result {
    let list = nodes.indirect(range);
    write_list(out, list, |out, node| write_node(out, nodes, *node))
}

fn write_block(
    out: &mut PrettyWriter<impl Write>,
    nodes: &NodeView,
    block: Block,
) -> std::fmt::Result {
    let statements = nodes.indirect(block.statements.nodes);
    match statements {
        [] => write!(out, "{{}}"),
        _ => {
            writeln!(out, "{{")?;
            out.indented(|out| {
                for statement in statements {
                    write_node(out, nodes, *statement)?;
                    writeln!(out)?;
                }
                Ok(())
            })?;
            write!(out, "}}")?;
            Ok(())
        }
    }
}

fn write_case_statements(
    out: &mut PrettyWriter<impl Write>,
    nodes: &NodeView,
    block: Block,
) -> std::fmt::Result {
    let statements = nodes.indirect(block.statements.nodes);
    match statements {
        [] => Ok(()),
        [single] => {
            write!(out, " ")?;
            write_node(out, nodes, *single)?;
            Ok(())
        }
        _ => {
            out.indented(|out| {
                for statement in statements {
                    writeln!(out)?;
                    write_node(out, nodes, *statement)?;
                }
                writeln!(out)?;
                Ok(())
            })?;
            Ok(())
        }
    }
}

fn write_node(
    out: &mut PrettyWriter<impl Write>,
    nodes: &NodeView,
    mut node: NodeId,
) -> std::fmt::Result {
    macro_rules! recurse {
        ($next_node:expr) => {{
            node = $next_node;
            continue;
        }};
    }

    loop {
        break match nodes.kind(node) {
            Node::Name(None) => write!(out, "_"),
            Node::Name(Some(name)) => write!(out, "{name}"),

            Node::Selector(node, name) => {
                write_node(out, nodes, node)?;
                write!(out, ".{name}")
            }

            Node::Pointer(inner) => {
                write!(out, "*")?;
                recurse!(inner.node);
            }

            Node::FunctionType(signature) => {
                let inputs = nodes.indirect(signature.inputs());
                let outputs = nodes.indirect(signature.outputs());
                write!(out, "func")?;
                write_signature(out, nodes, inputs, outputs)
            }
            Node::Function(signature, body) => {
                let inputs = nodes.indirect(signature.inputs());
                let outputs = nodes.indirect(signature.outputs());
                write!(out, "func")?;
                write_signature(out, nodes, inputs, outputs)?;
                write!(out, " ")?;
                write_block(out, nodes, body.block)
            }
            Node::Parameter(param) => write_parameter(out, nodes, param),

            Node::TypeDef(spec) => {
                write!(out, "type ")?;
                write_type_spec(out, nodes, spec, false)
            }
            Node::TypeAlias(spec) => {
                write!(out, "type ")?;
                write_type_spec(out, nodes, spec, true)
            }
            Node::TypeList(list) => {
                writeln!(out, "type (")?;
                out.indented(|out| {
                    for &item in nodes.indirect(list) {
                        match nodes.kind(item) {
                            Node::TypeDef(spec) => write_type_spec(out, nodes, spec, false)?,
                            Node::TypeAlias(spec) => write_type_spec(out, nodes, spec, true)?,
                            _ => unreachable!(),
                        }
                        writeln!(out)?;
                    }
                    Ok(())
                })?;
                write!(out, ")")?;
                Ok(())
            }

            Node::ConstDecl(names, typ, values) => {
                write!(out, "const ")?;
                write_const_spec(out, nodes, names, typ, values, None)
            }
            Node::ConstList(list) => {
                writeln!(out, "const (")?;
                out.indented(|out| {
                    let mut previous = None;
                    for &item in nodes.indirect(list) {
                        let Node::ConstDecl(names, typ, values) = nodes.kind(item) else {
                            unreachable!()
                        };
                        write_const_spec(out, nodes, names, typ, values, previous)?;
                        previous = Some(values);
                        writeln!(out)?;
                    }
                    Ok(())
                })?;
                write!(out, ")")?;
                Ok(())
            }

            Node::VarDecl(names, typ, values) => {
                write!(out, "var ")?;
                write_var_spec(out, nodes, names, typ, values)
            }
            Node::VarList(list) => {
                writeln!(out, "const (")?;
                out.indented(|out| {
                    for &item in nodes.indirect(list) {
                        let Node::VarDecl(names, typ, values) = nodes.kind(item) else {
                            unreachable!()
                        };
                        write_var_spec(out, nodes, names, typ, values)?;
                        writeln!(out)?;
                    }
                    Ok(())
                })?;
                write!(out, ")")?;
                Ok(())
            }

            Node::Interface(elements) => {
                write!(out, "interface {{")?;
                out.indented(|out| {
                    for &element in nodes.indirect(elements) {
                        writeln!(out)?;
                        write_node(out, nodes, element)?;
                    }
                    Ok(())
                })?;
                if !elements.is_empty() {
                    writeln!(out)?;
                }
                write!(out, "}}")?;
                Ok(())
            }
            Node::MethodElement(name, signature) => {
                let inputs = nodes.indirect(signature.inputs());
                let outputs = nodes.indirect(signature.outputs());
                write!(out, "{name}")?;
                write_signature(out, nodes, inputs, outputs)
            }

            Node::Struct(fields) => {
                write!(out, "struct {{")?;
                out.indented(|out| {
                    for &field in nodes.indirect(fields) {
                        writeln!(out)?;
                        write_node(out, nodes, field)?;
                    }
                    Ok(())
                })?;
                if !fields.is_empty() {
                    writeln!(out)?;
                }
                write!(out, "}}")?;
                Ok(())
            }
            Node::Field(name, typ, tag) => {
                write!(out, "{name} ")?;
                write_node(out, nodes, typ.node)?;
                if let Some(tag) = tag {
                    write!(out, " {tag:?}")?;
                }
                Ok(())
            }
            Node::EmbeddedField(_name, typ, tag) => {
                write_node(out, nodes, typ.node)?;
                if let Some(tag) = tag {
                    write!(out, " {tag:?}")?;
                }
                Ok(())
            }

            Node::Channel(kind, typ) => {
                match kind {
                    ChannelKind::SendRecv => write!(out, "chan")?,
                    ChannelKind::Send => write!(out, "chan<-")?,
                    ChannelKind::Recv => write!(out, "<-chan")?,
                }
                write!(out, " ")?;
                recurse!(typ.node);
            }

            Node::Call(target, arguments, spread) => {
                write_node(out, nodes, target.node)?;

                let arguments = nodes.indirect(arguments.nodes);
                let last = arguments.last();
                write!(out, "(")?;
                write_list(out, arguments, |out, argument| {
                    if Some(argument) == last && spread.is_some() {
                        write!(out, "...")?;
                    }
                    write_node(out, nodes, *argument)
                })?;
                write!(out, ")")?;
                Ok(())
            }

            Node::Rune(rune) => {
                write!(out, "{:?}", rune)
            }
            Node::String(range) => {
                let text = &nodes.string(range);
                write!(out, "{:?}", text)
            }
            Node::IntegerSmall(value) => write!(out, "{}", value),
            Node::FloatSmall(value) => write!(out, "{}", value.get()),
            Node::ImaginarySmall(value) => write!(out, "{}i", value.get()),

            Node::Assign(targets, values) => {
                write_node_list(out, nodes, targets.nodes)?;
                write!(out, " = ")?;
                write_node_list(out, nodes, values.nodes)?;
                Ok(())
            }
            Node::AssignOp(target, op, value) => {
                write_node(out, nodes, target.node)?;
                write!(out, " {op}= ")?;
                recurse!(value.node);
            }

            Node::Return(None) => write!(out, "return"),
            Node::Return(Some(value)) => {
                write!(out, "return ")?;
                write_node(out, nodes, value.node)
            }
            Node::ReturnMulti(list) => {
                write!(out, "return ")?;
                write_node_list(out, nodes, list.nodes)
            }

            Node::Unary(op, expr) => {
                write!(out, "{op}")?;
                recurse!(expr.node);
            }

            Node::Binary(interleaved) => {
                let binary_precedence = |interleaved: ExprRange| {
                    let op_node = nodes.indirect(interleaved)[1];
                    let Node::BinaryOp(op) = nodes.kind(op_node) else { unreachable!() };
                    op.precedence()
                };

                let expr_precedence = |expr: ExprId| match nodes.kind(expr) {
                    Node::Binary(others) => binary_precedence(others),
                    _ => 123, // some large number
                };

                let current_precedence = binary_precedence(interleaved);

                for &expr in nodes.indirect(interleaved).iter() {
                    if expr_precedence(expr) < current_precedence {
                        write!(out, "(")?;
                        write_node(out, nodes, expr.node)?;
                        write!(out, ")")?;
                    } else {
                        write_node(out, nodes, expr.node)?;
                    }
                }

                Ok(())
            }
            Node::BinaryOp(op) => write!(out, " {op} "),

            Node::Array(size, inner) => {
                write!(out, "[")?;
                match size {
                    Some(size) => write_node(out, nodes, size.node)?,
                    None => write!(out, "...")?,
                }
                write!(out, "]")?;
                recurse!(inner.node);
            }
            Node::Slice(inner) => {
                write!(out, "[]")?;
                recurse!(inner.node);
            }

            Node::Map(key, value) => {
                write!(out, "map[")?;
                write_node(out, nodes, key.node)?;
                write!(out, "]")?;
                recurse!(value.node);
            }

            Node::Composite(typ, composite) => {
                write_node(out, nodes, typ.node)?;
                write_composite_literal(out, nodes, composite)
            }
            Node::CompositeLiteral(composite) => write_composite_literal(out, nodes, composite),

            Node::Index(array, index) => {
                write_node(out, nodes, array.node)?;
                write!(out, "[")?;
                write_node(out, nodes, index.node)?;
                write!(out, "]")?;
                Ok(())
            }
            Node::SliceIndex(array, start, end) => {
                write_node(out, nodes, array.node)?;
                write!(out, "[")?;
                if let Some(start) = start {
                    write_node(out, nodes, start.node)?;
                }
                write!(out, ":")?;
                if let Some(end) = end {
                    write_node(out, nodes, end.node)?;
                }
                write!(out, "]")?;
                Ok(())
            }
            Node::SliceCapacity(array, start, end, cap) => {
                write_node(out, nodes, array.node)?;
                write!(out, "[")?;
                if let Some(start) = start {
                    write_node(out, nodes, start.node)?;
                }
                write!(out, ":")?;
                write_node(out, nodes, end.node)?;
                write!(out, ":")?;
                write_node(out, nodes, cap.node)?;
                write!(out, "]")?;
                Ok(())
            }

            Node::If(init, condition, block, els) => {
                write!(out, "if ")?;
                if let Some(init) = init {
                    write_node(out, nodes, init.node)?;
                    write!(out, "; ")?;
                }
                write_node(out, nodes, condition.node)?;
                write!(out, " ")?;
                write_block(out, nodes, block)?;

                if let Some(els) = els {
                    write!(out, " else ")?;
                    recurse!(els.node);
                }

                Ok(())
            }

            Node::Block(block) => write_block(out, nodes, block),

            Node::Switch(init, expr, cases) => {
                write!(out, "switch ")?;
                if let Some(init) = init {
                    write_node(out, nodes, init.node)?;
                    write!(out, "; ")?;
                }
                if let Some(expr) = expr {
                    write_node(out, nodes, expr.node)?;
                    write!(out, " ")?;
                }

                writeln!(out, "{{")?;
                for &case in nodes.indirect(cases) {
                    write_node(out, nodes, case)?;
                    writeln!(out)?;
                }
                write!(out, "}}")?;

                Ok(())
            }
            Node::TypeSwitch(binding, expr) => {
                if let Some(binding) = binding {
                    write!(out, "{} := ", binding)?;
                }
                write_node(out, nodes, expr.node)?;
                write!(out, ".(type)")
            }
            Node::SwitchCase(exprs, block) => {
                if let Some(exprs) = exprs {
                    write!(out, "case ")?;
                    write_node_list(out, nodes, exprs.nodes)?;
                    write!(out, ":")?;
                } else {
                    write!(out, "default:")?;
                }

                write_case_statements(out, nodes, block)?;

                Ok(())
            }

            Node::TypeAssertion(expr, typ) => {
                write_node(out, nodes, expr.node)?;
                write!(out, ".(")?;
                if let Some(typ) = typ {
                    write_node(out, nodes, typ.node)?;
                } else {
                    write!(out, "type")?;
                }
                write!(out, ")")?;
                Ok(())
            }

            Node::For(init, cond, post, block) => {
                write!(out, "for ")?;

                if init.is_none() && post.is_none() {
                    if let Some(cond) = cond {
                        write_node(out, nodes, cond.node)?;
                        write!(out, " ")?;
                    }
                } else {
                    if let Some(init) = init {
                        write_node(out, nodes, init.node)?;
                    }
                    write!(out, ";")?;
                    if let Some(cond) = cond {
                        write!(out, " ")?;
                        write_node(out, nodes, cond.node)?;
                    }
                    write!(out, ";")?;
                    if let Some(post) = post {
                        write!(out, " ")?;
                        write_node(out, nodes, post.node)?;
                        write!(out, " ")?;
                    }
                }

                write_block(out, nodes, block)?;

                Ok(())
            }
            Node::ForRangePlain(expr, block) => {
                write!(out, "for range ")?;
                write_node(out, nodes, expr.node)?;
                write!(out, " ")?;
                write_block(out, nodes, block)
            }
            Node::ForRange(first, second, assign_or_define, expr, block) => {
                write!(out, "for ")?;
                write_node(out, nodes, first.node)?;
                if let Some(second) = second {
                    write!(out, ", ")?;
                    write_node(out, nodes, second.node)?;
                }
                match assign_or_define {
                    AssignOrDefine::Assign => write!(out, " = ")?,
                    AssignOrDefine::Define => write!(out, " := ")?,
                }

                write!(out, "range ")?;
                write_node(out, nodes, expr.node)?;
                write!(out, " ")?;
                write_block(out, nodes, block)
            }

            Node::Increment(expr) => {
                write_node(out, nodes, expr.node)?;
                write!(out, "++")
            }
            Node::Decrement(expr) => {
                write_node(out, nodes, expr.node)?;
                write!(out, "--")
            }

            Node::Break(None) => write!(out, "break"),
            Node::Break(Some(label)) => write!(out, "break {label}"),
            Node::Continue(None) => write!(out, "continue"),
            Node::Continue(Some(label)) => write!(out, "continue {label}"),
            Node::Goto(label) => write!(out, "goto {label}"),
            Node::Fallthrough => write!(out, "fallthrough"),

            Node::Label(name, stmt) => {
                out.dedented(|out| writeln!(out, "{name}:"))?;
                recurse!(stmt.node);
            }

            Node::Defer(expr) => {
                write!(out, "defer ")?;
                recurse!(expr.node);
            }
            Node::Go(expr) => {
                write!(out, "go ")?;
                recurse!(expr.node);
            }

            Node::Send(send) => {
                write_node(out, nodes, send.channel.node)?;
                write!(out, " <- ")?;
                recurse!(send.value.node)
            }

            Node::Select(cases) => {
                writeln!(out, "switch {{")?;
                for &case in nodes.indirect(cases) {
                    write_node(out, nodes, case)?;
                    writeln!(out)?;
                }
                write!(out, "}}")?;

                Ok(())
            }
            Node::SelectRecv(bindings, kind, channel, block) => {
                write!(out, "case ")?;

                match (bindings, kind) {
                    (Some(bindings), Some(kind)) => {
                        write_node(out, nodes, bindings.value.node)?;
                        if let Some(success) = bindings.success {
                            write!(out, ", ")?;
                            write_node(out, nodes, success.node)?;
                        }
                        match kind {
                            AssignOrDefine::Assign => write!(out, " = ")?,
                            AssignOrDefine::Define => write!(out, " := ")?,
                        }
                    }
                    (None, None) => {}
                    _ => unreachable!(),
                }

                write_node(out, nodes, channel.node)?;
                write!(out, ":")?;
                write_case_statements(out, nodes, block)
            }
            Node::SelectSend(send, block) => {
                write!(out, "case ")?;
                write_node(out, nodes, send.channel.node)?;
                write!(out, " <- ")?;
                write_node(out, nodes, send.value.node)?;
                write!(out, ":")?;
                write_case_statements(out, nodes, block)
            }
            Node::SelectDefault(block) => {
                write!(out, "default:")?;
                write_case_statements(out, nodes, block)
            }
        };
    }
}

fn write_composite_literal(
    out: &mut PrettyWriter<impl Write>,
    nodes: &NodeView,
    composite: CompositeRange,
) -> std::fmt::Result {
    write!(out, "{{")?;
    match composite {
        CompositeRange::Value(values) => write_node_list(out, nodes, values.nodes)?,
        CompositeRange::KeyValue(range) => {
            let list = nodes.indirect(range.nodes);
            let pairs = list.iter().step_by(2).zip(list.iter().skip(1).step_by(2));
            write_list(out, pairs, |out, (key, value)| {
                write_node(out, nodes, *key)?;
                write!(out, ": ")?;
                write_node(out, nodes, *value)?;
                Ok(())
            })?;
        }
    }
    write!(out, "}}")?;
    Ok(())
}

impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.text {
            Some(text) => write!(f, "{}", text),
            None => write!(f, "_"),
        }
    }
}

fn write_type_spec(
    out: &mut PrettyWriter<impl Write>,
    nodes: &NodeView,
    spec: TypeSpec,
    alias: bool,
) -> std::fmt::Result {
    write!(out, "{} ", spec.name)?;
    if alias {
        write!(out, "= ")?;
    }
    write_node(out, nodes, spec.inner.node)
}

fn write_const_spec(
    out: &mut PrettyWriter<impl Write>,
    nodes: &NodeView,
    names: NodeRange,
    typ: Option<TypeId>,
    values: ExprRange,
    previous_values: Option<ExprRange>,
) -> std::fmt::Result {
    write_node_list(out, nodes, names)?;
    if let Some(typ) = typ {
        write!(out, " ")?;
        write_node(out, nodes, typ.node)?;
    }
    if Some(values) != previous_values {
        write!(out, " = ")?;
        write_node_list(out, nodes, values.nodes)?;
    }
    Ok(())
}

fn write_var_spec(
    out: &mut PrettyWriter<impl Write>,
    nodes: &NodeView,
    names: NodeRange,
    typ: Option<TypeId>,
    values: Option<ExprRange>,
) -> std::fmt::Result {
    write_node_list(out, nodes, names)?;
    if let Some(typ) = typ {
        write!(out, " ")?;
        write_node(out, nodes, typ.node)?;
    }
    if let Some(values) = values {
        write!(out, " = ")?;
        write_node_list(out, nodes, values.nodes)?;
    }
    Ok(())
}
