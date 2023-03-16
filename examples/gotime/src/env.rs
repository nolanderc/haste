use std::{ffi::OsString, path::Path};

use crate::{error, Result};

pub async fn go_var_path<'db>(db: &'db dyn crate::Db, name: &'static str) -> Result<&'db Path> {
    let text = go_var(db, name).await.as_ref()?;
    Ok(Path::new(text))
}

#[haste::query]
#[input]
pub async fn go_var(_db: &dyn crate::Db, name: &'static str) -> Result<OsString> {
    // check if the default has been overriden:
    if let Some(var) = std::env::var_os(name) {
        return Ok(var);
    }

    // fast path for common variables:
    #[cfg(target_family = "unix")]
    match name {
        "GOROOT" => return Ok("/usr/local/go".into()),
        "GOPATH" => {
            if let Some(mut home) = std::env::var_os("HOME") {
                if !home.is_empty() {
                    home.push("/go");
                    return Ok(home);
                }
            }
        }
        _ => {}
    }

    // If the variable was not already set, query the reference Go compiler:
    let mut output = tokio::process::Command::new("go")
        .args(["env", name])
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .output()
        .await
        .map_err(|error| error!("could not invoke `go env {name}`: {}", error))?;

    let contents = bstr::ByteSlice::trim_end(&output.stdout[..]);
    output.stdout.truncate(contents.len());

    if !output.status.success() || output.stdout.is_empty() {
        return Err(error!("the environment variable `{name}` is not set"));
    }

    String::from_utf8(output.stdout)
        .map(Into::into)
        .map_err(|error| {
            error!(
                "`{name}` contained invalid UTF-8: {:?}",
                bstr::BStr::new(error.as_bytes())
            )
        })
}
