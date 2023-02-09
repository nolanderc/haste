use haste::DatabaseExt;

use super::*;

use std::fmt::Write;

pub struct PrettyWriter<'db, W> {
    db: &'db dyn crate::Db,
    writer: W,
    indent: usize,
    needs_indent: bool,
}

impl<'db, W> PrettyWriter<'db, W> {
    pub fn new(db: &'db dyn crate::Db, writer: W) -> Self {
        Self {
            db,
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
}

impl<W: Write> PrettyWriter<'_, W> {
    fn write_indent(&mut self) -> std::fmt::Result {
        static SPACES: [u8; 256] = [b' '; 256];
        let mut count = self.indent;
        while count > 0 {
            let now = count.min(SPACES.len());
            let spaces = unsafe { std::str::from_utf8_unchecked(&SPACES[..now]) };
            self.writer.write_str(spaces)?;
            count -= now;
        }
        Ok(())
    }
}

impl<W> Write for PrettyWriter<'_, W>
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
            let mut writer = PrettyWriter::new(db, f);
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
            writeln!(out, "import {}", import)?;
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
        nodes: &NodeStorage,
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

        Ok(())
    }
}

fn write_signature(
    out: &mut PrettyWriter<impl Write>,
    nodes: &NodeStorage,
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

fn write_parameter(
    out: &mut PrettyWriter<impl Write>,
    nodes: &NodeStorage,
    param: Parameter,
) -> std::fmt::Result {
    if let Some(name) = param.name {
        write!(out, "{name} ")?;
    }
    write_node(out, nodes, param.typ.node)
}

fn write_node(
    out: &mut PrettyWriter<impl Write>,
    nodes: &NodeStorage,
    node: NodeId,
) -> std::fmt::Result {
    match nodes.kinds[node] {
        Node::Name(None) => write!(out, "_"),
        Node::Name(Some(name)) => write!(out, "{name}"),

        Node::Selector(node, name) => {
            write_node(out, nodes, node)?;
            write!(out, ".{name}")
        }

        Node::Pointer(inner) => {
            write!(out, "*")?;
            write_node(out, nodes, inner.node)
        }

        Node::FunctionType(signature) => {
            let inputs = nodes.indirect(signature.inputs());
            let outputs = nodes.indirect(signature.outputs());
            write!(out, "func")?;
            write_signature(out, nodes, inputs, outputs)
        }

        Node::TypeDef(spec) => {
            write!(out, "type {} ", spec.name)?;
            write_node(out, nodes, spec.inner.node)
        }
        Node::TypeAlias(spec) => {
            write!(out, "type {} = ", spec.name)?;
            write_node(out, nodes, spec.inner.node)
        }
        Node::TypeList(list) => {
            writeln!(out, "type (")?;
            out.indented(|out| {
                for &item in nodes.indirect(list) {
                    match nodes.kinds[item] {
                        Node::TypeDef(spec) => {
                            write!(out, "{} ", spec.name)?;
                            write_node(out, nodes, spec.inner.node)?;
                        }
                        Node::TypeAlias(spec) => {
                            write!(out, "{} = ", spec.name)?;
                            write_node(out, nodes, spec.inner.node)?;
                        }
                        _ => unreachable!(),
                    }
                    writeln!(out)?;
                }
                Ok(())
            })?;
            writeln!(out, ")")?;
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
                write!(out, " ")?;
                write_node(out, nodes, tag.node)?;
            }
            Ok(())
        }
        Node::EmbeddedField(_name, typ, tag) => {
            write_node(out, nodes, typ.node)?;
            if let Some(tag) = tag {
                write!(out, " ")?;
                write_node(out, nodes, tag.node)?;
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
            write_node(out, nodes, typ.node)
        }

        node => todo!("write node: {node:?}"),
    }
}

impl std::fmt::Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.text {
            Some(text) => write!(f, "{}", text),
            None => write!(f, "_"),
        }
    }
}
