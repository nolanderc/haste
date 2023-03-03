use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::spanned::Spanned;

use crate::meta::ArgumentOptions;

pub fn storage_impl(meta: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    if !meta.is_empty() {
        return Err(syn::Error::new(
            meta.span(),
            "unexpected attribute arguments",
        ));
    }

    let mut strukt = syn::parse2::<syn::ItemStruct>(input)?;

    let args = crate::meta::extract_attrs(
        &mut strukt.attrs,
        ArgumentOptions {
            db: true,
            ..Default::default()
        },
    );

    if !strukt.generics.params.is_empty() {
        return Err(syn::Error::new(
            strukt.generics.span(),
            "generics not supported",
        ));
    }

    let ident = strukt.ident.clone();
    let db_path = args.db;

    let mut impls = TokenStream::new();

    let mut field_members = Vec::with_capacity(strukt.fields.len());
    for (index, field) in strukt.fields.iter_mut().enumerate() {
        let field_member = match &field.ident {
            Some(ident) => syn::Member::Named(ident.clone()),
            None => syn::Member::Unnamed(syn::Index {
                index: index as _,
                span: field.span(),
            }),
        };

        let ty = &field.ty;
        let container_type = quote! {
            <#ty as haste::Ingredient>::Container
        };

        impls.extend(quote! {
            impl haste::HasIngredient<#ty> for Storage {
                fn container(&self) -> &#container_type {
                    &self.#field_member
                }

                fn container_mut(&mut self) -> &mut #container_type {
                    &mut self.#field_member
                }
            }
        });

        field.ty = syn::parse2(container_type)?;
        field_members.push(field_member);
    }

    let container_types = strukt.fields.iter().map(|field| &field.ty);

    impls.extend(quote! {
        impl haste::Storage for #ident {
            type DynDatabase = dyn #db_path;

            fn new<DB>(router: &mut haste::StorageRouter<DB>) -> Self
                where DB: haste::WithStorage<Self>
            {
                Self {
                    #(
                        #field_members: <#container_types as haste::StaticContainer>::new(
                            router.push(|db| &db.storage().#field_members)
                        ),
                    )*
                }
            }

            fn begin(&mut self, current: haste::Revision) {
                #( haste::StaticContainer::begin(&mut self.#field_members, current); )*
            }

            fn end(&mut self) {
                #( haste::StaticContainer::end(&mut self.#field_members); )*
            }
        }
    });

    let mut tokens = strukt.to_token_stream();
    tokens.extend(impls);
    Ok(tokens)
}
