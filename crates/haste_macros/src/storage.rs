use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::spanned::Spanned;

use crate::meta::ArgumentOptions;

pub fn storage_impl(meta: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    let args = crate::meta::parse_args(
        meta,
        ArgumentOptions {
            db: true,
            ..Default::default()
        },
    )?;

    let mut strukt = syn::parse2::<syn::ItemStruct>(input)?;

    if !strukt.generics.params.is_empty() {
        return Err(syn::Error::new(
            strukt.generics.span(),
            "generics not supported",
        ));
    }

    let ident = strukt.ident.clone();
    let db_path = args.db;

    let mut impls = quote! {
        impl haste::Storage for #ident {
            type DynDatabase = dyn #db_path;
        }
    };

    for (index, field) in strukt.fields.iter_mut().enumerate() {
        let field_member = match &field.ident {
            Some(ident) => syn::Member::Named(ident.clone()),
            None => syn::Member::Unnamed(syn::Index {
                index: index as _,
                span: field.span(),
            }),
        };
        let ty = &field.ty;
        let container_type = quote_spanned! {ty.span()=>
            <#ty as haste::Ingredient>::Container
        };

        impls.extend(quote! {
            impl haste::HasIngredient<#ty> for Storage {
                fn container(&self) -> &#container_type {
                    &self.#field_member
                }
            }
        });

        field.ty = syn::parse2(container_type)?;
    }

    let mut tokens = strukt.to_token_stream();
    tokens.extend(impls);
    Ok(tokens)
}
