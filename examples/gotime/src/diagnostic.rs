use std::sync::Arc;

pub type Result<T, E = Diagnostic> = std::result::Result<T, E>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Diagnostic {
    inner: Arc<Inner>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct Inner {
    message: String,
}

impl Diagnostic {
    fn new(inner: Inner) -> Self {
        Self {
            inner: Arc::new(inner),
        }
    }

    pub(crate) fn error(message: impl ToString) -> Self {
        Self::new(Inner {
            message: message.to_string(),
        })
    }
}
