use std::{ffi::OsString, path::Path, sync::Arc};

use bstr::{BStr, ByteSlice};
use haste::Durability;

use crate::{error, path::NormalPath, Result};

#[haste::storage]
pub struct Storage(command, env_var, go_var);

#[haste::query]
#[input]
pub async fn command(
    db: &dyn crate::Db,
    command: Arc<str>,
    args: Arc<[Arc<str>]>,
    cwd: Option<NormalPath>,
) -> Result<std::process::Output, String> {
    let mut command = std::process::Command::new(&*command);
    command.args(args.iter().map(|arg| &**arg));

    if let Some(cwd) = cwd {
        // TODO: don't silently discard this error (even though we don't expect it to ever fail)
        if let Ok(cwd) = cwd.system_path(db).await {
            command.current_dir(cwd);
        }
    }

    command.stdin(std::process::Stdio::null());
    command.stdout(std::process::Stdio::piped());
    command.stderr(std::process::Stdio::piped());
    command.output().map_err(|error| error.to_string())
}

pub async fn go(
    db: &dyn crate::Db,
    args: impl IntoIterator<Item = impl Into<Arc<str>>>,
    cwd: Option<NormalPath>,
) -> crate::Result<&BStr> {
    let goroot = go_var_path(db, "GOROOT").await?;
    let go_path = goroot.join("bin").join("go");
    let go_path = go_path.to_string_lossy();

    let output = command(
        db,
        Arc::from(go_path),
        args.into_iter().map(Into::into).collect(),
        cwd,
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
pub async fn env_var(db: &dyn crate::Db, name: &'static str) -> Option<OsString> {
    // enviroment variables should never change:
    db.runtime().set_durability(Durability::CONSTANT);
    std::env::var_os(name)
}

#[haste::query]
pub async fn go_var(db: &dyn crate::Db, name: &'static str) -> Result<OsString> {
    // check if the default has been overriden:
    if let Some(var) = env_var(db, name).await {
        return Ok(var.clone());
    }

    // fast path for common variables:
    if let Some(default) = crate::env::default::get(name) {
        return Ok(default);
    }

    // otherwise we rely on the reference go compiler:
    let result = go(db, ["env", name], None)
        .await
        .map(|output| output.trim());

    match result {
        Ok(output) if !output.is_empty() => Ok(output.to_os_str_lossy().into()),
        _ => Err(error!("the environment variable `{name}` is not set")),
    }
}

pub async fn go_var_path<'db>(db: &'db dyn crate::Db, name: &'static str) -> Result<&'db Path> {
    let text = go_var(db, name).await.as_ref()?;
    Ok(Path::new(text))
}
