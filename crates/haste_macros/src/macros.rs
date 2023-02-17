use std::cell::RefCell;

use proc_macro::TokenStream;

extern crate proc_macro;

mod common;
mod database;
mod intern;
mod meta;
mod query;
mod storage;

#[proc_macro_attribute]
pub fn database(meta: TokenStream, input: TokenStream) -> TokenStream {
    attribute_macro_handler(database::database_impl, meta.into(), input.into()).into()
}

#[proc_macro_attribute]
pub fn storage(meta: TokenStream, input: TokenStream) -> TokenStream {
    attribute_macro_handler(storage::storage_impl, meta.into(), input.into()).into()
}

#[proc_macro_attribute]
pub fn intern(meta: TokenStream, input: TokenStream) -> TokenStream {
    attribute_macro_handler(intern::intern_impl, meta.into(), input.into()).into()
}

#[proc_macro_attribute]
pub fn query(meta: TokenStream, input: TokenStream) -> TokenStream {
    attribute_macro_handler(query::query_impl, meta.into(), input.into()).into()
}

thread_local! {
    static ERRORS: RefCell<Option<syn::Error>> = RefCell::new(None);
}

pub(crate) fn emit_error(error: syn::Error) {
    ERRORS.with(|errors| {
        let mut slot = errors.borrow_mut();
        match slot.as_mut() {
            None => *slot = Some(error),
            Some(previous) => previous.combine(error),
        }
    })
}

fn attribute_macro_handler(
    f: impl FnOnce(
        proc_macro2::TokenStream,
        proc_macro2::TokenStream,
    ) -> syn::Result<proc_macro2::TokenStream>,
    meta: proc_macro2::TokenStream,
    input: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let mut output = match f(meta, input.clone()) {
        Ok(tokens) => tokens,
        Err(error) => {
            let mut tokens = input;
            tokens.extend(error.into_compile_error());
            tokens
        }
    };

    if let Some(error) = ERRORS.with(|errors| errors.take()) {
        output.extend(error.into_compile_error());
    }

    output
}
