#[macro_use]
mod macros;

pub(crate) use self::macros::*;

use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    sync::Arc,
};

use bstr::{BStr, ByteSlice};
use haste::DatabaseExt;
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
    /// Multiple diagnostics combined into one.
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

impl Severity {
    fn style(self) -> Style {
        match self {
            Severity::Error => Style::Red,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum Attachment {
    Label(Label),
    Note(String),
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
    pub fn combine<I>(diagnostics: I) -> Self
    where
        I: IntoIterator<Item = Diagnostic>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut diagnostics = diagnostics.into_iter();
        if diagnostics.len() == 1 {
            diagnostics.next().unwrap()
        } else {
            Self::new(Inner::Combine(diagnostics.collect()))
        }
    }

    pub fn push(&mut self, other: Diagnostic) {
        if let Some(Inner::Combine(list)) = Arc::get_mut(&mut self.inner) {
            list.push(other);
            return;
        }

        *self = Self::combine([self.clone(), other])
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

    /// Attach a label to the diagnostic
    pub fn label(self, span: Span, text: impl ToString) -> Self {
        self.attach(Attachment::Label(Label {
            severity: None,
            span,
            text: text.to_string(),
        }))
    }

    pub fn note(self, note: impl ToString) -> Self {
        self.attach(Attachment::Note(note.to_string()))
    }
}

type FmtResult<T> = Result<T, std::fmt::Error>;

#[derive(Default)]
struct VisitedSet {
    formatted: HashSet<*const Inner>,
}

impl Diagnostic {
    pub async fn write(&self, db: &dyn crate::Db, out: &mut impl Write) -> std::fmt::Result {
        // for each source file: get its text and line numbers
        let sources = self.get_source_infos(db).await;

        let mut visited = VisitedSet::default();
        self.format(&sources, &mut Vec::new(), out, &mut visited)?;

        if matches!(&*self.inner, Inner::Message(_)) {
            writeln!(out)?;
        }

        Ok(())
    }

    fn format<'a>(
        &'a self,
        sources: &SourceSet,
        attachments: &mut Vec<&'a Attachment>,
        out: &mut impl Write,
        visited: &mut VisitedSet,
    ) -> FmtResult<bool> {
        let mut formatted = false;

        if !visited.formatted.insert(Arc::as_ptr(&self.inner)) {
            return Ok(formatted);
        }

        match &*self.inner {
            Inner::Message(message) => {
                let severity_text = match message.severity {
                    Severity::Error => "error",
                };
                let severity_style = message.severity.style();
                let bold = Style::Bold;
                let reset = Style::Default;
                writeln!(
                    out,
                    "{bold}{severity_style}{}:{reset} {bold}{}",
                    severity_text, message.text
                )?;

                let self_attachments = message.attachments.iter();
                let other_attachments = attachments.iter().copied().rev();

                let last_message = (message.attachments.len() + attachments.len()).wrapping_sub(1);
                for (i, attachment) in self_attachments.chain(other_attachments).enumerate() {
                    let last = last_message == i;
                    attachment.format(message.severity, sources, last, out)?;
                }

                formatted = true;
            }
            Inner::Attachment(parent, new_attachments) => {
                attachments.extend(new_attachments.iter().rev());
                formatted = parent.format(sources, attachments, out, visited)?;
                attachments.truncate(attachments.len() - new_attachments.len());
            }
            Inner::Combine(combined) => {
                for diagnostic in combined {
                    if diagnostic.format(sources, attachments, out, visited)? {
                        writeln!(out)?;
                        formatted = true;
                    }
                }
            }
        }
        Ok(formatted)
    }
}

impl Attachment {
    fn format(
        &self,
        parent_severity: Severity,
        sources: &HashMap<SourcePath, SourceFileInfo>,
        last: bool,
        out: &mut impl Write,
    ) -> FmtResult<()> {
        use Style::*;
        match self {
            Attachment::Label(label) => label.format(parent_severity, sources, last, out),
            Attachment::Note(note) => {
                writeln!(out, "{Bold}{Green}note: {Default}{Bold}{note}{Default}")
            }
        }
    }
}

impl Label {
    fn format(
        &self,
        parent_severity: Severity,
        sources: &HashMap<SourcePath, SourceFileInfo>,
        last: bool,
        out: &mut impl Write,
    ) -> FmtResult<()> {
        use Style::*;

        let range = self.span.range;
        let source = &sources[&self.span.path];
        let line = source.line_index(range.start.get());
        let line_range = source.line_range(line);
        let line_text = BStr::new(source.text[line_range.clone()].trim_end());

        let gutter_width = 1 + (1 + line).ilog10() as usize;
        let gutter = " ".repeat(gutter_width);

        let column = range.start.get() as usize - line_range.start;
        let underline_offset = line_text[..column]
            .chars()
            .map(|ch| match ch {
                '\t' => "\t",
                _ => " ",
            })
            .collect::<String>();

        let underline_width = (range.end.get() - range.start.get()) as usize;
        let underline = "^".repeat(underline_width.max(1));

        let severity = parent_severity.style();

        writeln!(
            out,
            "{Bold}{Blue}{}-->{Default} {Italic}{Underline}{Dim}{}:{}{Default}",
            gutter,
            source.display_path,
            line + 1
        )?;
        writeln!(out, "{Bold}{Blue}{} |{Default}", gutter)?;
        writeln!(out, "{Bold}{Blue}{} |{Default} {}", line + 1, line_text)?;
        write!(
            out,
            "{Bold}{Blue}{} |{Default} {severity}{}{}",
            gutter, underline_offset, underline
        )?;
        if self.text.is_empty() {
            writeln!(out)?;
        } else {
            writeln!(out, " {}", self.text)?;
        }
        write!(out, "{Default}")?;

        if !last {
            writeln!(out, "{Bold}{Blue}{} |{Default}", gutter)?;
        }

        Ok(())
    }
}

#[allow(dead_code)]
enum Style {
    Default,

    Red,
    Yellow,
    Blue,
    Cyan,
    Gray,
    Green,

    Bold,
    Italic,
    Underline,
    Dim,
}

impl std::fmt::Display for Style {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Style::Default => write!(f, "\x1b[m"),
            Style::Red => write!(f, "\x1b[31m"),
            Style::Green => write!(f, "\x1b[32m"),
            Style::Yellow => write!(f, "\x1b[33m"),
            Style::Blue => write!(f, "\x1b[34m"),
            Style::Cyan => write!(f, "\x1b[36m"),
            Style::Gray => write!(f, "\x1b[37m"),
            Style::Bold => write!(f, "\x1b[1m"),
            Style::Italic => write!(f, "\x1b[3m"),
            Style::Underline => write!(f, "\x1b[4m"),
            Style::Dim => write!(f, "\x1b[2m"),
        }
    }
}

#[derive(Debug)]
struct SourceFileInfo<'db> {
    text: Arc<BStr>,
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
                    Attachment::Note(_) => continue,
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
                .expect("span pointed to path that did not exist");
            let line_starts = line_starts(db, source).await.as_ref().unwrap().as_slice();

            let display_path = db.fmt(source).to_string();

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
