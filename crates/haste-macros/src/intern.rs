use proc_macro2::TokenStream;
use quote::quote;
use syn::Result;

pub fn intern(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    let id_ident = syn::parse2::<syn::Ident>(attr)?;

    let data_input = syn::parse2::<syn::DeriveInput>(item.clone())?;

    let mut tokens = TokenStream::new();

    let data_ident = &data_input.ident;
    let vis = data_input.vis;

    tokens.extend(quote! {
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        #vis struct #id_ident(haste::InternId);

        impl haste::Element for #id_ident {
            type Storage = Storage;
            type Container = haste::ValueInterner<#data_ident>;
        }

        impl haste::Intern for #id_ident {
            type Value = #data_ident;

            #[inline]
            fn from_id(id: haste::InternId) -> Self {
                Self(id)
            }

            #[inline]
            fn id(self) -> haste::InternId {
                self.0
            }
        }

        impl #id_ident {
            pub fn insert(db: &haste::ElementDb<Self>, value: #data_ident) -> Self {
                haste::DatabaseExt::intern::<Self>(db, value)
            }

            pub fn lookup<'db>(self, db: &'db haste::ElementDb<Self>) -> &'db #data_ident {
                haste::DatabaseExt::lookup(db, self)
            }
        }

        impl std::fmt::Debug for #id_ident {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::write!(f, "Text({:?})", self.0)
            }
        }

        impl haste::fmt::DebugWith<haste::ElementDb<'_, Self>> for #id_ident {
            fn fmt(&self, db: &haste::ElementDb<Self>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                use haste::macro_helper::DebugFallback as _;
                std::fmt::Debug::fmt(&haste::fmt::macro_helper::HasteDebug::<#data_ident, haste::ElementDb<Self>>::haste_debug(self.lookup(db), db), f)
            }
        }
    });

    tokens.extend(item);

    Ok(tokens)
}
