use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse::Parser, spanned::Spanned};

pub fn database_impl(meta: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    let strukt = syn::parse2::<syn::ItemStruct>(input)?;

    let storages =
        syn::punctuated::Punctuated::<syn::Path, syn::Token![,]>::parse_terminated.parse2(meta)?;

    if !strukt.generics.params.is_empty() {
        return Err(syn::Error::new(
            strukt.generics.span(),
            "generics not supported",
        ));
    }

    let ident = &strukt.ident;

    let mut impls = TokenStream::new();

    {
        let storage_paths = storages.iter();
        impls.extend(quote! {
            impl haste::Database for #ident {
                fn runtime(&self) -> &haste::Runtime {
                    &self.runtime
                }

                fn runtime_mut(&mut self) -> &mut haste::Runtime {
                    &mut self.runtime
                }
            }

            impl haste::WithStorages for #ident {
                type StorageList = (#(#storage_paths,)*);
            }
        });
    }

    for (index, storage) in storages.iter().enumerate() {
        let index = syn::Index {
            index: index as u32,
            span: storage.span(),
        };
        impls.extend(quote! {
            impl haste::WithStorage<#storage> for Database {
                #[inline(always)]
                fn as_dyn(&self) -> &<#storage as haste::Storage>::DynDatabase {
                    self
                }

                #[inline(always)]
                fn storage(&self) -> &Storage {
                    &self.storage.list().#index
                }

                #[inline(always)]
                fn storage_mut(&mut self) -> &mut Storage {
                    &mut self.storage.list_mut().#index
                }
            }
        });
    }

    let mut tokens = strukt.to_token_stream();
    tokens.extend(impls);
    Ok(tokens)
}
