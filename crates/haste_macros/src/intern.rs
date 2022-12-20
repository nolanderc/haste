use proc_macro2::TokenStream;
use quote::{format_ident, quote, quote_spanned, ToTokens};
use syn::spanned::Spanned;

use crate::meta::{ArgumentOptions, Arguments};

pub fn intern_impl(meta: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    let args = crate::meta::parse_args(
        meta,
        ArgumentOptions {
            db: true,
            storage: true,
            ..Default::default()
        },
    )?;

    let input = syn::parse2::<syn::DeriveInput>(input)?;

    if !input.generics.params.is_empty() {
        return Err(syn::Error::new(
            input.generics.span(),
            "generics not supported",
        ));
    }

    match input.data {
        syn::Data::Struct(_) => derive_struct(args, input),
        syn::Data::Enum(_) => todo!("derive for enum"),
        syn::Data::Union(uni) => Err(syn::Error::new(
            uni.union_token.span,
            "only structs and enums are supported",
        )),
    }
}

fn derive_struct(args: Arguments, mut input: syn::DeriveInput) -> syn::Result<TokenStream> {
    let db_path = args.db;
    let storage_path = args.storage;
    let syn::Data::Struct(data) = &mut input.data else { unreachable!() };
    let ident = input.ident.clone();

    let id_fields = syn::parse_quote!((haste::Id));
    let data_fields = std::mem::replace(&mut data.fields, syn::Fields::Unnamed(id_fields));
    let fields = crate::common::field_info(&data_fields)?;
    let field_types = fields.iter().map(|field| field.ty);

    let data_type = quote! {
        (#(#field_types),*)
    };

    let mut impls = quote! {
        impl haste::Ingredient for #ident {
            type Container = haste::interner::ArenaInterner<#data_type>;
            type Storage = #storage_path;
            type Database = dyn #db_path;
        }

        impl haste::Intern for #ident {
            type Value = #data_type;

            fn from_id(id: haste::Id) -> Self {
                Self(id)
            }

            fn id(self) -> haste::Id {
                self.0
            }
        }

        impl #ident {
            pub fn new(db: &dyn #db_path, data: #data_type) -> Self {
                haste::DatabaseExt::intern(db, data)
            }
        }
    };

    let field_count = fields.len();
    for field in fields {
        let getter = match &field.member {
            syn::Member::Named(ident) => ident.clone(),
            syn::Member::Unnamed(index) => {
                if index.index == 0 {
                    format_ident!("get", span = index.span)
                } else {
                    format_ident!("get_{}", index.index, span = index.span)
                }
            }
        };

        let field_type = field.ty;
        let span = field.member.span();
        if field_count == 1 {
            impls.extend(quote_spanned! {span=>
                impl #ident {
                    pub fn #getter(self, db: &dyn #db_path) -> &#field_type {
                        haste::DatabaseExt::intern_lookup(db, self)
                    }
                }
            });
        } else {
            let index = field.index;
            impls.extend(quote_spanned! {span=>
                impl #ident {
                    pub fn #getter(self, db: &dyn #db_path) -> &#field_type {
                        let data = haste::DatabaseExt::intern_lookup(db, self);
                        &data.#index
                    }
                }
            });
        }
    }

    let mut tokens = input.to_token_stream();
    tokens.extend(impls);
    Ok(tokens)
}
