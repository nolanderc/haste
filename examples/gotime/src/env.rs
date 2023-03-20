/// Default environment variables for various platforms.
pub mod default {
    use std::{ffi::OsString, path::PathBuf};

    /// Get the default value for an environment variable. Returns `None` if its value is unknown.
    pub fn get(name: &str) -> Option<OsString> {
        match name {
            "GOROOT" => crate::env::default::GOROOT.map(Into::into),

            "GOPATH" => crate::env::default::gopath(),

            "GOOS" => {
                macro_rules! match_os {
                    ($($os:literal => $map:literal),* $(,)?) => {
                        $( if cfg!(target_os = $os) { return Some($map.into()); })*
                    }
                }

                match_os! {
                    "linux" => "linux",
                    "android" => "android",
                    "openbsd" => "openbsd",
                    "netbsd" => "netbsd",
                    "macos" => "darwin",
                    "ios" => "ios",
                    "windows" => "windows",
                }

                None
            }

            "GOARCH" => {
                macro_rules! match_arch {
                    ($($arch:literal => $map:literal),* $(,)?) => {
                        $( if cfg!(target_arch = $arch) { return Some($map.into()); })*
                    }
                }

                match_arch! {
                    "x86" => "386",
                    "x86_64" => "amd64",
                    "mips" => "mips",
                    "powerpc" => "ppc",
                    "powerpc64" => "ppc64",
                    "arm" => "arm",
                    "aarch64" => "arm64",
                }

                None
            }

            _ => None,
        }
    }

    pub const GOROOT: Option<&str> = if cfg!(unix) {
        Some("/usr/local/go")
    } else {
        None
    };

    fn gopath() -> Option<OsString> {
        #[cfg(unix)]
        if let Some(home) = std::env::var_os("HOME") {
            if !home.is_empty() {
                let mut path = PathBuf::from(home);
                path.push("go");
                return Some(path.into());
            }
        }

        None
    }
}
