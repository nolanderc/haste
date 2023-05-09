#![allow(clippy::single_component_path_imports)]

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

pub(crate) use bug;
pub(crate) use error;
