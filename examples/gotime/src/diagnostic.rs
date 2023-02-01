use std::sync::Arc;

use smallvec::SmallVec;

use crate::span::Span;

pub type Result<T, E = Diagnostic> = std::result::Result<T, E>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Diagnostic {
    inner: Arc<Inner>,
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

#[derive(Debug, PartialEq, Eq, Hash)]
enum Severity {
    Error,

    /// Inherit the value of the parent (only valid for attachments).
    Inherit,
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct Attachment {
    severity: Severity,
    span: Option<Span>,
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
        self.attach(Attachment {
            severity: Severity::Inherit,
            span: Some(span),
            text: text.to_string(),
        })
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
