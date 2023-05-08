use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{spanned::Spanned, Result};

pub fn storage(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    if !attr.is_empty() {
        return Err(syn::Error::new_spanned(attr, "unexpected arguments"));
    }

    let mut input = syn::parse2::<syn::DeriveInput>(item)?;

    let strukt = match &mut input.data {
        syn::Data::Struct(strukt) => strukt,
        syn::Data::Enum(_) | syn::Data::Union(_) => {
            return Err(syn::Error::new_spanned(input.ident, "expected a struct"))
        }
    };

    let mut members = Vec::with_capacity(strukt.fields.len());
    let mut types = Vec::with_capacity(strukt.fields.len());

    for (i, field) in strukt.fields.iter().enumerate() {
        members.push(match &field.ident {
            Some(ident) => syn::Member::Named(ident.clone()),
            None => syn::Member::Unnamed(syn::Index {
                index: i as u32,
                span: field.ty.span(),
            }),
        });
        types.push(&field.ty);
    }

    let mut tokens = TokenStream::new();

    let ident = &input.ident;

    tokens.extend(quote! {
        impl haste::Storage for #ident {
            type Database = dyn crate::Db;

            fn new<DB>(router: &mut haste::StorageRouter<DB>) -> Self
            where
                DB: haste::WithStorage<Self>,
            {
                Self {
                    #(
                        #members: <<#types as haste::Element>::Container as haste::Container>::new(
                            router.push(|db| &db.storage().#members),
                        ),
                    )*
                }
            }
        }

        #(
            impl haste::WithElement<#types> for Storage {
                fn container(&self) -> &<#types as haste::Element>::Container {
                    &self.#members
                }

                fn container_mut(&mut self) -> &mut <#types as haste::Element>::Container {
                    &mut self.#members
                }
            }
        )*
    });

    for field in strukt.fields.iter_mut() {
        let old = &field.ty;
        field.ty = syn::Type::Verbatim(quote! {
            <#old as haste::Element>::Container
        });
    }

    input.to_tokens(&mut tokens);

    Ok(tokens)
}
