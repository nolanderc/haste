#[macro_use]
mod exported {
    macro_rules! error {
        ($($fmt:tt)*) => {
            $crate::Diagnostic::error(format!($($fmt)*))
        };
    }

    macro_rules! bug {
        ($($fmt:tt)*) => {
            $crate::Diagnostic::bug(format!($($fmt)*))
        };
    }
}

pub(crate) use error;
pub(crate) use bug;
