pub struct FromFn<F>(F);

impl<F> std::fmt::Display for FromFn<F>
where
    F: Fn(&mut std::fmt::Formatter<'_>) -> std::fmt::Result,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0(f)
    }
}

impl<F> std::fmt::Debug for FromFn<F>
where
    F: Fn(&mut std::fmt::Formatter<'_>) -> std::fmt::Result,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0(f)
    }
}

pub fn from_fn<F>(f: F) -> FromFn<F>
where
    F: Fn(&mut std::fmt::Formatter<'_>) -> std::fmt::Result,
{
    FromFn(f)
}

/// Format a query in the given database
pub fn query(
    db: &dyn crate::Database,
    path: crate::IngredientPath,
) -> impl std::fmt::Display + std::fmt::Debug + '_ {
    let container = db
        .dyn_storage_path(path.container)
        .and_then(|storage| storage.dyn_container_path(path.container));

    crate::util::fmt::from_fn(move |f| {
        if let Some(container) = container {
            container.fmt(path, f)
        } else {
            write!(f, "{:?}", path)
        }
    })
}
