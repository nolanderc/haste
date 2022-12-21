use std::borrow::Cow;

use proc_macro2::TokenStream;
use quote::{format_ident, quote, quote_spanned, ToTokens};
use syn::spanned::Spanned;

use crate::meta::ArgumentOptions;

pub fn query_impl(meta: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    if !meta.is_empty() {
        return Err(syn::Error::new(
            meta.span(),
            "unexpected attribute arguments",
        ));
    }

    let mut query_fn = syn::parse2::<syn::ItemFn>(input)?;

    if !query_fn.sig.generics.params.is_empty() {
        return Err(syn::Error::new(
            query_fn.sig.generics.span(),
            "generics not supported",
        ));
    }

    let args = crate::meta::extract_attrs(
        &mut query_fn.attrs,
        ArgumentOptions {
            db: true,
            storage: true,
            clone: true,
            ..Default::default()
        },
    )?;
    let db_path = &args.db;
    let storage_path = &args.storage;

    let vis = &query_fn.vis;
    let ident = &query_fn.sig.ident;

    let InputData {
        db_ident,
        types: input_types,
        spread: input_spread,
        idents: input_idents,
    } = input_type(&query_fn.sig)?;
    let input_type = quote! { (#(#input_types),*) };

    let output_type = match &query_fn.sig.output {
        syn::ReturnType::Default => Cow::Owned(syn::parse_quote! { () }),
        syn::ReturnType::Type(_, ty) => Cow::Borrowed(ty.as_ref()),
    };

    let mut tokens = TokenStream::new();

    tokens.extend(quote_spanned! {ident.span()=>
        #[allow(non_camel_case_types)]
        #vis enum #ident {}

        impl #ident {
            #query_fn
        }

        impl haste::Ingredient for #ident {
            type Container = haste::query_cache::HashQueryCache<Self>;
            type Storage = #storage_path;
            type Database = dyn #db_path;
        }

        impl haste::Query for #ident {
            type Input = #input_type;
            type Output = #output_type;

            fn execute(db: &dyn #db_path, input: #input_type) -> #output_type {
                Self::#ident(db, #input_spread)
            }
        }
    });

    let return_type = if args.clone {
        quote! { #output_type }
    } else {
        quote_spanned! {output_type.span()=> &#output_type }
    };

    let mut execution = quote! {
        haste::DatabaseExt::execute_cached::<#ident>(#db_ident, (#(#input_idents),*))
    };

    if args.clone {
        execution = quote! { <#output_type as std::clone::Clone>::clone(#execution) };
    }

    tokens.extend(quote_spanned! {ident.span()=>
        #vis fn #ident(#db_ident: &dyn #db_path, #(#input_idents: #input_types),*) -> #return_type {
            #execution
        }
    });

    Ok(tokens)
}

struct InputData<'a> {
    db_ident: TokenStream,
    spread: TokenStream,
    idents: Vec<syn::Ident>,
    types: Vec<&'a syn::Type>,
}

fn input_type(signature: &syn::Signature) -> syn::Result<InputData> {
    if signature.inputs.is_empty() {
        return Err(syn::Error::new(
            signature.paren_token.span,
            "queries must have a database as its first argument",
        ));
    }

    if signature.inputs.len() == 1 {
        return Err(syn::Error::new(
            signature.paren_token.span,
            "queries must have at least one input",
        ));
    }

    let mut args = signature.inputs.iter();
    let db = args.next().unwrap();
    let db_ident = match db {
        syn::FnArg::Typed(typed) => typed.pat.to_token_stream(),
        syn::FnArg::Receiver(_) => {
            return Err(syn::Error::new(db.span(), "methods are not supported"))
        }
    };

    let inputs = args.map(|input| match input {
        syn::FnArg::Receiver(_) => unreachable!(),
        syn::FnArg::Typed(typed) => typed,
    });

    let input_count = inputs.len();
    let types = inputs.clone().map(|input| input.ty.as_ref()).collect();

    let spread = if input_count == 1 {
        quote! { input }
    } else {
        let indices = inputs.clone().enumerate().map(|(index, input)| syn::Index {
            index: index as u32,
            span: input.span(),
        });
        quote! { #( input.#indices ),* }
    };

    let idents = inputs
        .enumerate()
        .map(|(index, input)| match input.pat.as_ref() {
            syn::Pat::Ident(ident) => ident.ident.clone(),
            _ => format_ident!("__haste_arg{}", index, span = input.pat.span()),
        })
        .collect();

    Ok(InputData {
        db_ident,
        types,
        spread,
        idents,
    })
}
