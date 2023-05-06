extern crate proc_macro;

mod query;
mod storage;
mod database;

use std::cell::Cell;

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;

#[proc_macro_attribute]
pub fn query(attr: TokenStream, item: TokenStream) -> TokenStream {
    handle_attribute(attr, item, query::query)
}

#[proc_macro_attribute]
pub fn storage(attr: TokenStream, item: TokenStream) -> TokenStream {
    handle_attribute(attr, item, storage::storage)
}

#[proc_macro_attribute]
pub fn database(attr: TokenStream, item: TokenStream) -> TokenStream {
    handle_attribute(attr, item, database::database)
}

fn handle_attribute(
    attr: TokenStream,
    item: TokenStream,
    func: fn(TokenStream2, TokenStream2) -> syn::Result<TokenStream2>,
) -> TokenStream {
    let attr = TokenStream2::from(attr);
    let item = TokenStream2::from(item);

    let result = func(attr, item.clone());

    let mut output = TokenStream::new();

    if let Some(emitted) = take_errors() {
        output.extend(TokenStream::from(emitted.to_compile_error()));
    }

    match result {
        Ok(tokens) => output.extend(TokenStream::from(tokens)),
        Err(error) => {
            output.extend(TokenStream::from(error.to_compile_error()));
            output.extend(TokenStream::from(item));
        }
    }

    output
}

thread_local! {
    static ERRORS: Cell<Vec<syn::Error>> = Cell::new(Vec::new());
}

#[allow(dead_code)]
fn emit_error(error: syn::Error) {
    ERRORS.with(|errors| {
        let mut list = errors.take();
        list.push(error);
        errors.set(list);
    })
}

fn take_errors() -> Option<syn::Error> {
    ERRORS.with(|errors| {
        let mut errors = errors.take().into_iter();
        let mut combined = errors.next()?;
        for error in errors {
            combined.combine(error);
        }
        Some(combined)
    })
}
