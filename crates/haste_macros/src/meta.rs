use proc_macro2::TokenStream;
use syn::{parse::Parser, punctuated::Punctuated, spanned::Spanned};

pub struct Arguments {
    pub db: syn::Path,
    pub storage: syn::Path,
    pub clone: bool,
}

impl Default for Arguments {
    fn default() -> Self {
        Arguments {
            db: syn::parse_quote!(crate::Db),
            storage: syn::parse_quote!(crate::Storage),
            clone: false,
        }
    }
}

#[derive(Default)]
#[non_exhaustive]
pub struct ArgumentOptions {
    pub db: bool,
    pub storage: bool,
    pub clone: bool,
}

pub fn parse_args(meta: TokenStream, options: ArgumentOptions) -> syn::Result<Arguments> {
    let list = Punctuated::<syn::NestedMeta, syn::Token![,]>::parse_terminated.parse2(meta)?;
    parse_meta_list(list.into_iter(), options)
}

pub fn parse_meta(meta: syn::Meta, options: ArgumentOptions) -> syn::Result<Arguments> {
    match meta {
        syn::Meta::List(list) => parse_meta_list(list.nested.into_iter(), options),
        _ => Err(syn::Error::new(
            meta.span(),
            format!(
                "expected a list: `{}(...)`",
                meta.path().get_ident().unwrap()
            ),
        )),
    }
}

fn parse_meta_list(
    nested: impl Iterator<Item = syn::NestedMeta>,
    options: ArgumentOptions,
) -> syn::Result<Arguments> {
    let check_path = |path: &syn::Path, expected: &str| {
        let enabled = match expected {
            "db" => options.db,
            "storage" => options.storage,
            "clone" => options.clone,
            _ => false,
        };
        enabled && path.is_ident(expected)
    };

    let mut errors = Vec::new();
    let mut args = Arguments::default();
    for nested in nested {
        let syn::NestedMeta::Meta(meta) = nested else {
            errors.push(syn::Error::new(nested.span(), "invalid attribute"));
            continue
        };

        if check_path(meta.path(), "db") {
            args.db = parse_path(&meta)?;
            continue;
        }
        if check_path(meta.path(), "storage") {
            args.storage = parse_path(&meta)?;
            continue;
        }
        if check_path(meta.path(), "clone") {
            args.clone = parse_flag(&meta)?;
            continue;
        }

        errors.push(syn::Error::new(meta.path().span(), "unknown attribute"));
    }

    let mut errors = errors.into_iter();
    if let Some(mut combined) = errors.next() {
        combined.extend(errors);
        return Err(combined);
    }

    Ok(args)
}

fn parse_path(meta: &syn::Meta) -> syn::Result<syn::Path> {
    let error = || {
        let message = format!(
            "expected a path: `{}(<path>)`",
            meta.path().get_ident().unwrap()
        );
        syn::Error::new(meta.span(), message)
    };

    let syn::Meta::List(list) = meta else {
        return Err(error());
    };

    if list.nested.len() != 1 {
        return Err(error());
    }

    let inner = &list.nested[0];
    let syn::NestedMeta::Meta(syn::Meta::Path(path)) = inner else {
        return Err(error());
    };

    Ok(path.clone())
}

fn parse_flag(meta: &syn::Meta) -> syn::Result<bool> {
    match meta {
        syn::Meta::Path(_) => Ok(true),
        _ => Err(syn::Error::new(
            meta.span(),
            format!(
                "expected a simple flag without arguments: `{}`",
                meta.path().get_ident().unwrap()
            ),
        )),
    }
}
