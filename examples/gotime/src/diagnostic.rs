#[macro_use]
mod macros;

pub(crate) use self::macros::*;

use std::{fmt::Write, sync::Arc};

use bstr::{BStr, ByteSlice};
use haste::DatabaseExt;
use smallvec::SmallVec;

use crate::{
    path::NormalPath,
    source::{line_starts, source_text},
    span::Span,
    HashMap, HashSet,
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
    Combine(SmallVec<[Diagnostic; 2]>),
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
    Bug,
}

impl Severity {
    fn style(self) -> Style {
        match self {
            Severity::Error => Style::Red,
            Severity::Bug => Style::Purple,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum Attachment {
    Label(Label),
    Note(String),
    Help(String),
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
    #[cold]
    pub fn error(text: impl ToString) -> Self {
        Self::new(Inner::Message(Message {
            severity: Severity::Error,
            text: text.to_string(),
            attachments: SmallVec::new(),
        }))
    }

    /// Create a new bug message
    #[cold]
    pub fn bug(text: impl ToString) -> Self {
        Self::new(Inner::Message(Message {
            severity: Severity::Bug,
            text: text.to_string(),
            attachments: SmallVec::new(),
        }))
    }

    /// Combine multiple diagnostics into one
    #[cold]
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

    #[cold]
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

    pub fn help(self, help: impl ToString) -> Self {
        self.attach(Attachment::Help(help.to_string()))
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

        Ok(())
    }

    fn format<'a>(
        &'a self,
        sources: &SourceSet,
        attachments: &mut Vec<&'a Attachment>,
        out: &mut impl Write,
        visited: &mut VisitedSet,
    ) -> FmtResult<()> {
        if !visited.formatted.insert(Arc::as_ptr(&self.inner)) {
            return Ok(());
        }

        match &*self.inner {
            Inner::Message(message) => {
                let severity_text = match message.severity {
                    Severity::Error => "error",
                    Severity::Bug => "bug",
                };
                let severity_style = message.severity.style();
                let bold = Style::Bold;
                let reset = Style::Default;
                writeln!(
                    out,
                    "{bold}{severity_style}{}:{reset} {bold}{}{reset}",
                    severity_text, message.text
                )?;

                let self_attachments = message.attachments.iter();
                let other_attachments = attachments.iter().copied().rev();

                let last_message = (message.attachments.len() + attachments.len()).wrapping_sub(1);
                for (i, attachment) in self_attachments.chain(other_attachments).enumerate() {
                    let last = last_message == i;
                    attachment.format(message.severity, sources, last, out)?;
                }
            }
            Inner::Attachment(parent, new_attachments) => {
                attachments.extend(new_attachments.iter().rev());
                parent.format(sources, attachments, out, visited)?;
                attachments.truncate(attachments.len() - new_attachments.len());
            }
            Inner::Combine(combined) => {
                for diagnostic in combined {
                    diagnostic.format(sources, attachments, out, visited)?;
                }
            }
        }

        Ok(())
    }
}

impl Attachment {
    fn format(
        &self,
        parent_severity: Severity,
        sources: &HashMap<NormalPath, SourceFileInfo>,
        last: bool,
        out: &mut impl Write,
    ) -> FmtResult<()> {
        use Style::*;
        match self {
            Attachment::Label(label) => label.format(parent_severity, sources, last, out),
            Attachment::Note(text) => {
                writeln!(out, "{Bold}{Cyan}note: {Default}{Bold}{text}{Default}")
            }
            Attachment::Help(text) => {
                writeln!(out, "{Bold}{Green}help: {Default}{Bold}{text}{Default}")
            }
        }
    }
}

impl Label {
    fn format(
        &self,
        parent_severity: Severity,
        sources: &HashMap<NormalPath, SourceFileInfo>,
        last: bool,
        out: &mut impl Write,
    ) -> FmtResult<()> {
        use Style::*;

        // TODO: support multiline snippets
        let range = self.span.range;
        let source = &sources[&self.span.path];

        let start_line = source.line_index(range.start.get());
        let end_line = source.line_index(range.end.get());

        let start_line_range = source.line_range(start_line);
        let end_line_range = source.line_range(end_line);

        let start_line_text = BStr::new(source.text[start_line_range.clone()].trim_end());
        let end_line_text = BStr::new(source.text[end_line_range.clone()].trim_end());

        let gutter_width = 1 + (1 + end_line).ilog10() as usize;
        let gutter = " ".repeat(gutter_width);

        let start_column = range.start.get() as usize - start_line_range.start;
        let end_column = range.end.get() as usize - end_line_range.start;

        let start_end_column = if start_line == end_line {
            end_column
        } else {
            start_line_text.len()
        };

        let whitespace_map = |ch: char| match ch {
            '\t' => "    ",
            _ => " ",
        };
        let underline_map = |ch: char| match ch {
            '\t' => "^^^^",
            _ => "^",
        };

        let start_underline = start_line_text[..start_column]
            .chars()
            .map(whitespace_map)
            .chain(
                start_line_text[start_column..start_end_column]
                    .chars()
                    .map(underline_map),
            )
            .collect::<String>();

        let end_underline = end_line_text[..end_column]
            .chars()
            .map(underline_map)
            .chain(end_line_text[end_column..].chars().map(whitespace_map))
            .collect::<String>();

        let severity = parent_severity.style();

        writeln!(
            out,
            "{Bold}{Blue}{}-->{Default} {Italic}{Underline}{Dim}{}:{}{Default}",
            gutter,
            source.display_path,
            start_line + 1
        )?;
        writeln!(out, "{Bold}{Blue}{} |{Default}", gutter)?;
        writeln!(
            out,
            "{Bold}{Blue}{} |{Default} {}",
            start_line + 1,
            BStr::new(&start_line_text.replace(b"\t", b"    "))
        )?;

        let mid_gutter = if start_line == end_line { '|' } else { ':' };

        write!(
            out,
            "{Bold}{Blue}{} {mid_gutter}{Default} {severity}{}",
            gutter, start_underline
        )?;

        if start_line != end_line {
            writeln!(
                out,
                "\n{Bold}{Blue}{} |{Default} {}",
                end_line + 1,
                BStr::new(&end_line_text.replace(b"\t", b"    "))
            )?;
            write!(
                out,
                "{Bold}{Blue}{} |{Default} {severity}{}",
                gutter, end_underline
            )?;
        }

        if self.text.is_empty() {
            writeln!(out)?;
        } else {
            writeln!(out, " {}", self.text)?;
        }

        if !last {
            writeln!(out, "{Bold}{Blue}{} |{Default}", gutter)?;
        } else {
            writeln!(out, "{Default}")?;
        }

        Ok(())
    }
}

#[allow(dead_code)]
enum Style {
    Default,

    Red,
    Green,
    Yellow,
    Blue,
    Purple,
    Cyan,
    Gray,

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
            Style::Purple => write!(f, "\x1b[35m"),
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

type SourceSet<'db> = HashMap<NormalPath, SourceFileInfo<'db>>;

impl Diagnostic {
    async fn get_source_infos<'db>(&self, db: &'db dyn crate::Db) -> SourceSet<'db> {
        let mut sources = HashSet::default();

        let mut visited = HashSet::default();

        let mut diagnostic_stack = Vec::new();
        let mut next = Some(self);
        while let Some(current) = next.take() {
            if !visited.insert(Arc::as_ptr(&current.inner)) {
                next = diagnostic_stack.pop();
                continue;
            }

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
                    let mut children = children.iter().rev();
                    next = children.next();
                    diagnostic_stack.extend(children);
                    continue;
                }
            };

            for attachment in attachments {
                let path = match attachment {
                    Attachment::Label(label) => label.span.path,
                    Attachment::Note(_) | Attachment::Help(_) => continue,
                };

                if sources.insert(path) {
                    line_starts::prefetch(db, path);
                }
            }
        }

        let mut infos = SourceSet::default();
        infos.reserve(sources.len());

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
