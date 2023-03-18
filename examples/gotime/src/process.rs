use std::{ffi::OsString, path::Path, sync::Arc};

use bstr::{BStr, ByteSlice};

use crate::{error, Result};

#[haste::storage]
pub struct Storage(command, env_var, go_var);

#[haste::query]
#[input]
pub async fn command(
    _db: &dyn crate::Db,
    command: Arc<str>,
    args: Arc<[Arc<str>]>,
    cwd: Option<Arc<Path>>,
) -> Result<std::process::Output, String> {
    let mut command = tokio::process::Command::new(&*command);
    command.args(args.iter().map(|arg| &**arg));

    if let Some(cwd) = cwd {
        command.current_dir(&*cwd);
    }

    command.stdin(std::process::Stdio::null());
    command.output().await.map_err(|error| error.to_string())
}

pub async fn go(
    db: &dyn crate::Db,
    args: impl IntoIterator<Item = impl Into<Arc<str>>>,
    cwd: Option<Arc<Path>>,
) -> crate::Result<&BStr> {
    let goroot = go_var_path(db, "GOROOT").await?;
    let go_path = goroot.join("bin").join("go");
    let go_path = go_path.to_string_lossy();

    let output = command(
        db,
        Arc::from(go_path),
        args.into_iter().map(Into::into).collect(),
        cwd.map(Into::into),
    )
    .await
    .as_ref()
    .map_err(|error| error!("{}", error))?;

    if !output.status.success() {
        return Err(error!("{}", bstr::BStr::new(output.stderr.trim_end())));
    }

    Ok(BStr::new(&output.stdout))
}

#[haste::query]
#[input]
pub async fn env_var(_db: &dyn crate::Db, name: &'static str) -> Option<OsString> {
    std::env::var_os(name)
}

#[haste::query]
pub async fn go_var(db: &dyn crate::Db, name: &'static str) -> Result<OsString> {
    // check if the default has been overriden:
    if let Some(var) = env_var(db, name).await {
        return Ok(var.clone());
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

    let output = go(db, ["env", name], None)
        .await
        .map_err(|_| error!("the environment variable `{name}` is not set"))?;

    Ok(output.to_os_str_lossy().into())
}

pub async fn go_var_path<'db>(db: &'db dyn crate::Db, name: &'static str) -> Result<&'db Path> {
    let text = go_var(db, name).await.as_ref()?;
    Ok(Path::new(text))
}
