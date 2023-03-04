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

/// Format an index in the given database
pub fn ingredient(
    db: &dyn crate::Database,
    path: crate::IngredientPath,
) -> impl std::fmt::Display + std::fmt::Debug + '_ {
    crate::util::fmt::from_fn(move |f| db.fmt_index(path, f))
}
