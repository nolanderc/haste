use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    sync::Arc,
};

use smallvec::SmallVec;

use crate::{
    source::{line_starts, source_text, SourcePath},
    span::Span,
};

pub type Result<T, E = Diagnostic> = std::result::Result<T, E>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Diagnostic {
    inner: Arc<Inner>,
}

impl From<&Diagnostic> for Diagnostic {
    fn from(value: &Diagnostic) -> Self {
        value.clone()
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum Inner {
    /// A simple message.
    Message(Message),
    /// Some additional information attached to some other diagnostic
    Attachment(Diagnostic, SmallVec<[Attachment; 1]>),
    /// Multiple diagnostics combined into one
    Combine(Vec<Diagnostic>),
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct Message {
    severity: Severity,
    text: String,

    /// We optimize for the common case here by including optional attachments inside the main
    /// message. This way we can avoid some allocations, as most diagnostics have at least one
    /// attachment (pointing to the region of code where the error happened).
    attachments: SmallVec<[Attachment; 1]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Severity {
    Error,
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum Attachment {
    Label(Label),
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct Label {
    severity: Option<Severity>,
    span: Span,
    text: String,
}

impl Diagnostic {
    fn new(inner: Inner) -> Self {
        Self {
            inner: Arc::new(inner),
        }
    }

    /// Create a new error message
    pub fn error(text: impl ToString) -> Self {
        Self::new(Inner::Message(Message {
            severity: Severity::Error,
            text: text.to_string(),
            attachments: SmallVec::new(),
        }))
    }

    /// Combine multiple diagnostics into one
    pub fn combine(mut diagnostics: Vec<Diagnostic>) -> Self {
        if diagnostics.len() == 1 {
            diagnostics.swap_remove(0)
        } else {
            Self::new(Inner::Combine(diagnostics))
        }
    }

    pub fn merge(mut self, mut others: Vec<Diagnostic>) -> Self {
        if others.is_empty() {
            return self;
        }

        if let Some(Inner::Combine(list)) = Arc::get_mut(&mut self.inner) {
            list.append(&mut others);
            return self;
        }

        others.push(self);
        Self::new(Inner::Combine(others))
    }

    /// Attach a label to the diagnostic
    pub fn label(self, span: Span, text: impl ToString) -> Self {
        self.attach(Attachment::Label(Label {
            severity: None,
            span,
            text: text.to_string(),
        }))
    }

    fn attach(mut self, attachment: Attachment) -> Self {
        if let Some(inner) = Arc::get_mut(&mut self.inner) {
            match inner {
                Inner::Message(message) => {
                    message.attachments.push(attachment);
                    return self;
                }
                Inner::Attachment(_, attachments) => {
                    attachments.push(attachment);
                    return self;
                }
                Inner::Combine(_) => {}
            }
        }

        Diagnostic::new(Inner::Attachment(self, [attachment].into()))
    }
}

type FmtResult<T> = Result<T, std::fmt::Error>;

impl Diagnostic {
    pub async fn write(&self, db: &dyn crate::Db, out: &mut impl Write) -> std::fmt::Result {
        // for each source file: get its text and line numbers
        let sources = self.get_source_infos(db).await;
        self.format(&sources, out)?;

        Ok(())
    }

    fn format(&self, sources: &SourceSet, out: &mut impl Write) -> FmtResult<Severity> {
        match &*self.inner {
            Inner::Message(message) => {
                let severity_text = match message.severity {
                    Severity::Error => "error",
                };
                writeln!(out, "{}: {}", severity_text, message.text)?;

                for attachment in message.attachments.iter() {
                    attachment.format(message.severity, sources, out)?;
                }

                Ok(message.severity)
            }
            Inner::Attachment(parent, attachments) => {
                let parent_severity = parent.format(sources, out)?;

                for attachment in attachments.iter() {
                    attachment.format(parent_severity, sources, out)?;
                }

                Ok(parent_severity)
            }
            Inner::Combine(_) => todo!(),
        }
    }
}

impl Attachment {
    fn format(
        &self,
        parent_severity: Severity,
        sources: &HashMap<SourcePath, SourceFileInfo>,
        out: &mut impl Write,
    ) -> FmtResult<()> {
        match self {
            Attachment::Label(label) => label.format(parent_severity, sources, out),
        }
    }
}

impl Label {
    fn format(
        &self,
        parent_severity: Severity,
        sources: &HashMap<SourcePath, SourceFileInfo>,
        out: &mut impl Write,
    ) -> FmtResult<()> {
        let range = self.span.range;
        let source = &sources[&self.span.path];
        let line = source.line_index(range.start.get());
        let line_range = source.line_range(line);
        let line_text = source.text[line_range.clone()].trim_end();

        let gutter_width = 1 + (1 + line).ilog10() as usize;
        let gutter = " ".repeat(gutter_width);

        let column = range.start.get() as usize - line_range.start;
        let underline_offset = " ".repeat(column);

        let underline_width = (range.end.get() - range.start.get()) as usize;
        let underline = "^".repeat(underline_width);

        writeln!(out, "{}--> {}", gutter, source.display_path)?;
        writeln!(out, "{} |", gutter)?;
        writeln!(out, "{} | {}", line + 1, line_text)?;
        write!(out, "{} | {}{}", gutter, underline_offset, underline)?;
        if self.text.is_empty() {
            writeln!(out)?;
        } else {
            writeln!(out, " {}", self.text)?;
        }

        Ok(())
    }
}

#[derive(Debug)]
struct SourceFileInfo<'db> {
    text: &'db str,
    line_starts: &'db [u32],
    display_path: String,
}

impl SourceFileInfo<'_> {
    /// Given a byte offset into the file, returns the byte offset of the first character on that
    /// line
    fn line_index(&self, offset: u32) -> usize {
        match self.line_starts.binary_search(&offset) {
            // found the first character of a line, so the line number is the index of the line + 1
            Ok(index) => index,

            // We landed between two line starts, so the returned index will be one more than the
            // index of the line start. Since the first line always starts at offset 0, this will
            // always be 1 or greater
            Err(index) => index - 1,
        }
    }

    /// Get the range of bytes that correspond to the given line (including the line terminator)
    fn line_range(&self, line: usize) -> std::ops::Range<usize> {
        let start = self.line_starts[line] as usize;
        let end = self
            .line_starts
            .get(line + 1)
            .map(|index| *index as usize)
            .unwrap_or(self.text.len());
        start..end
    }
}

type SourceSet<'db> = HashMap<SourcePath, SourceFileInfo<'db>>;

impl Diagnostic {
    async fn get_source_infos<'db>(&self, db: &'db dyn crate::Db) -> SourceSet<'db> {
        let mut sources = HashSet::new();

        let mut diagnostic_stack = Vec::new();
        let mut next = Some(self);
        while let Some(current) = next.take() {
            let attachments = match &*current.inner {
                Inner::Message(message) => {
                    next = diagnostic_stack.pop();
                    message.attachments.as_slice()
                }
                Inner::Attachment(parent, attachments) => {
                    next = Some(parent);
                    attachments.as_slice()
                }
                Inner::Combine(children) => {
                    let mut children = children.iter();
                    next = children.next_back();
                    diagnostic_stack.extend(children);
                    continue;
                }
            };

            for attachment in attachments {
                let path = match attachment {
                    Attachment::Label(label) => label.span.path,
                };

                if sources.insert(path) {
                    line_starts::prefetch(db, path);
                }
            }
        }

        let mut infos = SourceSet::with_capacity(sources.len());

        for source in sources {
            let text = source_text(db, source)
                .await
                .as_ref()
                .expect("span pointed to path that did not exist")
                .as_str();
            let line_starts = line_starts(db, source).await.as_ref().unwrap().as_slice();

            let display_path = source.display(db).to_string();

            infos.insert(
                source,
                SourceFileInfo {
                    text,
                    line_starts,
                    display_path,
                },
            );
        }

        infos
    }
}
