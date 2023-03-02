use proc_macro2::{Span, TokenStream};
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
        let storage_paths = storages.iter().collect::<Vec<_>>();
        let storage_indices = (0..storages.len()).map(|index| syn::Index {
            index: index as u32,
            span: Span::call_site(),
        });

        impls.extend(quote! {
            impl haste::StaticDatabase for #ident {
                type StorageList = (#(#storage_paths,)*);

                fn storage(&self) -> &haste::DatabaseStorage<Self> {
                    &self.storage
                }

                fn storage_mut(&mut self) -> &mut haste::DatabaseStorage<Self> {
                    &mut self.storage
                }

                fn container(&self, path: haste::ContainerPath) -> &dyn haste::Container<Self> {
                    self.storage.get_path(self, path)
                }
            }

            impl haste::Database for #ident {
                fn as_dyn(&self) -> &dyn haste::Database {
                    self
                }

                fn runtime(&self) -> &haste::Runtime {
                    self.storage.runtime()
                }

                /// Determine how an ingredient handles dependency cycles.
                fn cycle_strategy(&self, path: haste::ContainerPath) -> haste::CycleStrategy {
                    haste::StaticDatabase::container(self, path)
                        .as_query_cache().unwrap()
                        .cycle_strategy()
                }

                /// The ingredient is part of a cycle.
                fn set_cycle(&self, path: haste::IngredientPath, cycle: haste::Cycle) {
                    let result = self
                        .storage
                        .get_path(self, path.container)
                        .as_query_cache().unwrap()
                        .set_cycle(path.resource, cycle);

                    if let Err(cycle) = result {
                        panic!(
                            "encountered cycle while recovering from another cycle: {}", 
                            cycle.fmt(self),
                        );
                    }
                }

                fn last_changed(&self, dep: haste::Dependency) -> Option<haste::Revision> {
                    todo!("last_changed({:?})", dep)
                }

                /// Format an ingredient
                fn fmt_index(&self, path: haste::IngredientPath, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    haste::StaticDatabase::container(self, path.container)
                        .fmt(path.resource, f)
                }

                fn get_storage_any(&self, id: std::any::TypeId) -> Option<&dyn std::any::Any> {
                    let list = self.storage.list();
                    #(
                        if id == std::any::TypeId::of::<#storage_paths>() {
                            return Some(&list.#storage_indices);
                        }
                    )*

                    None
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
