use std::borrow::Cow;

use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use syn::spanned::Spanned;

use crate::meta::ArgumentOptions;

pub fn query_impl(meta: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    let mut errors = Vec::new();

    if !meta.is_empty() {
        errors.push(syn::Error::new(
            meta.span(),
            "unexpected attribute arguments",
        ));
    }

    let mut query_fn = syn::parse2::<syn::ItemFn>(input)?;

    if !query_fn.sig.generics.params.is_empty() {
        errors.push(syn::Error::new(
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
            cycle: true,
            input: true,
            ..Default::default()
        },
    );
    let db_path = &args.db;
    let storage_path = &args.storage;

    let vis = &query_fn.vis;
    let ident = &query_fn.sig.ident;

    let InputData {
        db_ident,
        types: input_types,
        spread: input_spread,
        idents: input_idents,
    } = extract_input_data(&query_fn.sig)?;
    let input_type = quote! { (#(#input_types),*) };

    let output_type = match &query_fn.sig.output {
        syn::ReturnType::Default => Cow::Owned(syn::parse_quote! { () }),
        syn::ReturnType::Type(_, ty) => Cow::Borrowed(ty.as_ref()),
    };

    let mut tokens = TokenStream::new();

    let format_string = if input_idents.len() == 1 {
        "{}({:?})"
    } else {
        "{}{:?}"
    };

    let cycle_strategy = match args.cycle {
        None => quote! { haste::CycleStrategy::Panic },
        Some(_) => quote! { haste::CycleStrategy::Recover },
    };

    let cycle_recovery = match args.cycle {
        None => quote! { async move {
            let db = haste::Database::as_dyn(db);
            panic!("unexpected dependency cycle: {:#}", cycle.fmt(db)) }
        },
        Some(recovery_fn) => quote! { #recovery_fn(db, cycle, #input_spread) },
    };

    tokens.extend(quote! {
        #[allow(non_camel_case_types)]
        #vis enum #ident {}

        impl #ident {
            #query_fn
        }

        impl haste::Ingredient for #ident {
            type Container = haste::query_cache::HashQueryCache<Self>;
            type Storage = #storage_path;
        }

        impl haste::Query for #ident {
            type Input = #input_type;
            type Output = #output_type;
            type Future<'db> = impl std::future::Future<Output = Self::Output> + 'db;
            type RecoverFuture<'db> = impl std::future::Future<Output = Self::Output> + 'db;

            fn fmt(input: &Self::Input, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let name = std::any::type_name::<Self>();
                write!(f, #format_string, name, input)
            }

            fn execute<'db>(db: &'db dyn #db_path, input: #input_type) -> Self::Future<'db> {
                Self::#ident(db, #input_spread)
            }

            const CYCLE_STRATEGY: haste::CycleStrategy = #cycle_strategy;

            fn recover_cycle<'db>(
                db: &'db dyn #db_path,
                cycle: haste::Cycle,
                input: #input_type,
            ) -> Self::RecoverFuture<'db> {
                #cycle_recovery
            }
        }
    });

    if args.input {
        tokens.extend(quote! {
            impl haste::Input for #ident {}
        });
    }

    let return_type = if args.clone {
        quote! { #output_type }
    } else {
        quote! { &'db #output_type }
    };

    let clone = if args.clone {
        quote! { <#output_type as std::clone::Clone>::clone }
    } else {
        quote! {}
    };

    tokens.extend(quote! {
        #[allow(unused)]
        #vis async fn #ident<'db>(#db_ident: &'db dyn #db_path, #(#input_idents: #input_types),*) -> #return_type {
            #clone (haste::DatabaseExt::spawn::<#ident>(#db_ident, (#(#input_idents),*)).await)
        }

        impl #ident {
            #[allow(unused)]
            #vis fn prefetch(#db_ident: &dyn #db_path, #(#input_idents: #input_types),*) {
                haste::DatabaseExt::prefetch::<#ident>(#db_ident, (#(#input_idents),*));
            }

            #[allow(unused)]
            #vis async fn inline<'db>(#db_ident: &'db dyn #db_path, #(#input_idents: #input_types),*) -> #return_type {
                #clone (haste::DatabaseExt::execute_inline::<#ident>(#db_ident, (#(#input_idents),*)).await)
            }
        }
    });

    for error in errors {
        tokens.extend(error.to_compile_error());
    }

    Ok(tokens)
}

struct InputData<'a> {
    db_ident: TokenStream,
    spread: TokenStream,
    idents: Vec<syn::Ident>,
    types: Vec<&'a syn::Type>,
}

fn extract_input_data(signature: &syn::Signature) -> syn::Result<InputData> {
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
