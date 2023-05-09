use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{spanned::Spanned, Result};

pub fn debug_with(input: syn::DeriveInput) -> Result<TokenStream> {
    let mut tokens = TokenStream::new();

    let db_type = quote! { <Storage as haste::Storage>::Database<'_> };
    let ident = &input.ident;

    let mut patterns = TokenStream::new();

    match input.data {
        syn::Data::Union(_) => {
            return Err(syn::Error::new_spanned(
                input.ident,
                "cannot derive for unions",
            ))
        }
        syn::Data::Struct(strukt) => {
            patterns = debug_fields(&input.ident, &strukt.fields, &db_type);
        }
        syn::Data::Enum(enumm) => {
            for variant in enumm.variants.iter() {
                patterns.extend(quote! { Self:: });
                patterns.extend(debug_fields(&variant.ident, &variant.fields, &db_type));
            }
        }
    }

    let (impl_generics, type_generics, where_clause) = input.generics.split_for_impl();

    tokens.extend(quote! {
        impl #impl_generics haste::DebugWith<#db_type> for #ident #type_generics #where_clause {
            fn fmt(&self, __db: &#db_type, __f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                use haste::fmt::macro_helper::DebugFallback as _;
                match self {
                    #patterns
                }
            }
        }
    });

    Ok(tokens)
}

fn debug_fields(ident: &syn::Ident, fields: &syn::Fields, db_type: &TokenStream) -> TokenStream {
    let name = ident.to_string();

    let idents: Vec<_> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            field
                .ident
                .clone()
                .unwrap_or_else(|| format_ident!("_{i}", span = field.ty.span()))
        })
        .collect();

    let names = idents.iter().map(|ident| ident.to_string());
    let types = fields.iter().map(|field| &field.ty);

    let debugs = idents.iter().zip(types).map(|(ident, typ)| {
        quote! {
            haste::fmt::macro_helper::HasteDebug::<#typ, #db_type>::haste_debug(
                #ident,
                __db,
            )
        }
    });

    match &fields {
        syn::Fields::Named(_) => {
            quote! {
                #ident { #(#idents),* } => {
                    __f.debug_struct(#name)
                        #(.field(#names, &#debugs))*
                        .finish()
                }
            }
        }
        syn::Fields::Unnamed(_) => {
            quote! {
                #ident ( #(#idents),* ) => {
                    __f.debug_tuple(#name)
                        #(.field(&#debugs))*
                        .finish()
                }
            }
        }
        syn::Fields::Unit => {
            quote! {
                #ident => std::write!(__f, #name),
            }
        }
    }
}
