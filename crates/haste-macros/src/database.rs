use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse::Parser, punctuated::Punctuated, spanned::Spanned, Result, Token};

pub fn database(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    let storages = Punctuated::<syn::Path, Token![,]>::parse_terminated
        .parse2(attr)?
        .into_iter()
        .collect::<Vec<_>>();

    let input = syn::parse2::<syn::DeriveInput>(item)?;

    let mut tokens = TokenStream::new();

    let ident = &input.ident;

    let indices = storages
        .iter()
        .enumerate()
        .map(|(i, storage)| syn::Index {
            index: i as u32,
            span: storage.span(),
        })
        .collect::<Vec<_>>();

    tokens.extend(quote! {
        impl haste::StaticDatabase for #ident {
            type StorageList = (#(#storages,)*);
        }

        impl haste::Database for #ident {
            fn runtime(&self) -> &haste::Runtime {
                self.storage.runtime()
            }

            fn runtime_mut(&mut self) -> &mut haste::Runtime {
                self.storage.runtime_mut()
            }
        }

        #(
            impl haste::WithStorage<#storages> for #ident {
                fn storage(&self) -> &#storages {
                    &self.storage.storages().#indices
                }

                fn storage_mut(&mut self) -> (&mut #storages, &mut haste::Runtime) {
                    let (list, runtime) = self.storage.storages_mut();
                    (&mut list.#indices, runtime)
                }

                fn cast_database(&self) -> &<#storages as haste::Storage>::Database {
                    self
                }
            }
        )*
    });

    input.to_tokens(&mut tokens);

    Ok(tokens)
}
