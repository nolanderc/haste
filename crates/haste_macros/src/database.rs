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
            impl haste::StaticDatabase for #ident {
                type StorageList = (#(#storage_paths,)*);

                fn storage(&self) -> &haste::DatabaseStorage<Self> {
                    &self.storage
                }

                fn storage_mut(&mut self) -> &mut haste::DatabaseStorage<Self> {
                    &mut self.storage
                }
            }

            impl haste::Database for #ident {
                fn as_dyn(&self) -> &dyn haste::Database {
                    self
                }

                fn runtime(&self) -> &haste::Runtime {
                    self.storage.runtime()
                }

                fn storage_list(&self) -> &dyn haste::DynStorageList {
                    self.storage.list()
                }

                fn dyn_storage(&self, id: std::any::TypeId) -> Option<&dyn haste::DynStorage> {
                    haste::DynStorageList::get(self.storage.list(), id)
                }

                fn dyn_storage_path(&self, path: haste::ContainerPath) -> Option<&dyn haste::DynStorage> {
                    haste::DynStorageList::get_path(self.storage.list(), path)
                }

                fn dyn_container_path(&self, path: haste::ContainerPath) -> Option<&dyn haste::DynContainer> {
                    haste::DynStorageList::get_path(self.storage.list(), path)?
                        .dyn_container_path(path)
                }
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
                fn cast_dyn(&self) -> &<#storage as haste::Storage>::DynDatabase {
                    self
                }

                #[inline(always)]
                fn storage(&self) -> &Storage {
                    &self.storage.list().#index
                }
            }
        });
    }

    let mut tokens = strukt.to_token_stream();
    tokens.extend(impls);
    Ok(tokens)
}
