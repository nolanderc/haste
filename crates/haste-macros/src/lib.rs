extern crate proc_macro;

mod database;
mod intern;
mod query;
mod storage;
mod debug_with;

use std::cell::Cell;

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;

#[proc_macro_attribute]
pub fn database(attr: TokenStream, item: TokenStream) -> TokenStream {
    handle_attribute(attr, item, database::database)
}

#[proc_macro_attribute]
pub fn storage(attr: TokenStream, item: TokenStream) -> TokenStream {
    handle_attribute(attr, item, storage::storage)
}

#[proc_macro_attribute]
pub fn query(attr: TokenStream, item: TokenStream) -> TokenStream {
    handle_attribute(attr, item, query::query)
}

#[proc_macro_attribute]
pub fn intern(attr: TokenStream, item: TokenStream) -> TokenStream {
    handle_attribute(attr, item, intern::intern)
}

#[proc_macro_derive(DebugWith)]
pub fn debug_with(input: TokenStream) -> TokenStream {
    handle_derive(input, debug_with::debug_with)
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

fn handle_derive(
    input: TokenStream,
    func: fn(syn::DeriveInput) -> syn::Result<TokenStream2>,
) -> TokenStream {
    let item = syn::parse_macro_input!(input as syn::DeriveInput);
    let result = func(item);

    let mut output = TokenStream::new();

    if let Some(emitted) = take_errors() {
        output.extend(TokenStream::from(emitted.to_compile_error()));
    }

    match result {
        Ok(tokens) => output.extend(TokenStream::from(tokens)),
        Err(error) => output.extend(TokenStream::from(error.to_compile_error())),
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
