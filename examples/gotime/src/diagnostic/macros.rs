#[macro_use]
mod exported {
    macro_rules! error {
        ($($fmt:tt)*) => {
            $crate::Diagnostic::error(format!($($fmt)*))
        };
    }
}

pub(crate) use error as error;
