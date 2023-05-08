use proc_macro2::TokenStream;
use quote::quote;
use syn::{spanned::Spanned, Result};

pub fn intern(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    let id_ident = syn::parse2::<syn::Ident>(attr)?;

    let data_input = syn::parse2::<syn::DeriveInput>(item.clone())?;

    let strukt = match &data_input.data {
        syn::Data::Struct(strukt) => strukt,
        syn::Data::Enum(_) | syn::Data::Union(_) => {
            return Err(syn::Error::new_spanned(
                data_input.ident,
                "expected a struct",
            ))
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

            pub fn lookup(self, db: &haste::ElementDb<Self>) -> &#data_ident {
                haste::DatabaseExt::lookup(db, self)
            }
        }

        impl std::fmt::Debug for #id_ident {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::write!(f, "Text({:?})", self.0)
            }
        }

        impl haste::fmt::DebugWith<haste::ElementDb<Self>> for #id_ident {
            fn fmt(&self, db: &haste::ElementDb<Self>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                use haste::macro_helper::DebugFallback as _;
                std::fmt::Debug::fmt(&haste::fmt::macro_helper::HasteDebug::<#data_ident, haste::ElementDb<Self>>::haste_debug(self.lookup(db), db), f)
            }
        }
    });

    tokens.extend(item);

    Ok(tokens)
}
