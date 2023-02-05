use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::spanned::Spanned;

use crate::meta::ArgumentOptions;

pub fn intern_impl(meta: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    let input = syn::parse2::<syn::DeriveInput>(input)?;

    if !input.generics.params.is_empty() {
        return Err(syn::Error::new(
            input.generics.span(),
            "generics not supported",
        ));
    }

    let name = syn::parse2(meta)?;

    match input.data {
        syn::Data::Struct(_) => derive_struct(name, input),
        syn::Data::Enum(_) => derive_enum(name, input),
        syn::Data::Union(uni) => Err(syn::Error::new(
            uni.union_token.span,
            "only structs and enums are supported",
        )),
    }
}

fn derive_struct(ingredient: syn::Ident, mut input: syn::DeriveInput) -> syn::Result<TokenStream> {
    let syn::Data::Struct(data) = &mut input.data else { unreachable!() };

    let args = crate::meta::extract_attrs(
        &mut input.attrs,
        ArgumentOptions {
            db: true,
            storage: true,
            ..Default::default()
        },
    )?;
    let db_path = &args.db;

    let mut impls = TokenStream::new();

    impls.extend(ingredient_impl(IngredientInfo {
        vis: &input.vis,
        ident: &ingredient,
        data_ident: &input.ident,
        db_path,
        storage_path: &args.storage,
    }));

    let fields = crate::common::FieldInfo::extract(&mut data.fields)?;
    for field in fields {
        let getter = field.getter();
        let member = &field.member;
        let field_type = field.ty;
        let span = field.member.span();

        let mut extractor = quote! {
            &haste::DatabaseExt::lookup(db, self).#member
        };

        let mut output_type = field_type.clone();
        if field.arguments.clone {
            extractor = quote! {
                <#field_type as std::clone::Clone>::clone(#extractor)
            }
        } else {
            output_type = syn::parse_quote! { &#output_type };
        }

        impls.extend(quote_spanned! {span=>
            impl #ingredient {
                #[allow(unused)]
                pub fn #getter(self, db: &dyn #db_path) -> #output_type {
                    #extractor
                }
            }
        });
    }

    let getter = getter_fn(&input, &args);
    impls.extend(quote! {
        impl #ingredient {
            #getter
        }
    });

    let mut tokens = input.to_token_stream();
    tokens.extend(impls);
    Ok(tokens)
}

fn derive_enum(ingredient: syn::Ident, mut input: syn::DeriveInput) -> syn::Result<TokenStream> {
    let syn::Data::Enum(_) = &mut input.data else { unreachable!() };
    let data_ident = &input.ident;

    let args = crate::meta::extract_attrs(
        &mut input.attrs,
        ArgumentOptions {
            db: true,
            storage: true,
            clone: true,
            ..Default::default()
        },
    )?;
    let db_path = &args.db;

    let mut impls = TokenStream::new();

    impls.extend(ingredient_impl(IngredientInfo {
        vis: &input.vis,
        ident: &ingredient,
        data_ident,
        db_path,
        storage_path: &args.storage,
    }));

    let getter = getter_fn(&input, &args);
    impls.extend(quote! {
        impl #ingredient {
            #getter
        }
    });

    let mut tokens = input.to_token_stream();
    tokens.extend(impls);
    Ok(tokens)
}

fn getter_fn(input: &syn::DeriveInput, args: &crate::meta::Arguments) -> TokenStream {
    let data_ident = &input.ident;
    let mut output_type = data_ident.to_token_stream();

    let mut extractor = quote! {
        haste::DatabaseExt::lookup(db, self)
    };

    if args.clone {
        extractor = quote! {
            <#data_ident as std::clone::Clone>::clone(#extractor)
        }
    } else {
        output_type = syn::parse_quote! { &#output_type };
    }

    let db_path = &args.db;
    quote_spanned! {input.ident.span()=>
        #[allow(unused)]
        pub fn get(self, db: &dyn #db_path) -> #output_type {
            #extractor
        }
    }
}

struct IngredientInfo<'a> {
    vis: &'a syn::Visibility,
    ident: &'a syn::Ident,
    data_ident: &'a syn::Ident,
    db_path: &'a syn::Path,
    storage_path: &'a syn::Path,
}

fn ingredient_impl(info: IngredientInfo) -> TokenStream {
    let IngredientInfo {
        vis,
        ident,
        data_ident,
        db_path,
        storage_path,
    } = info;

    let ident_text = ident.to_string();

    quote! {
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        #vis struct #ident(haste::Id);

        impl haste::Ingredient for #ident {
            type Container = haste::interner::ArenaInterner<#data_ident>;
            type Storage = #storage_path;
        }

        impl haste::TrackedReference for #ident {
            fn from_id(id: haste::Id) -> Self {
                Self(id)
            }

            fn id(self) -> haste::Id {
                self.0
            }
        }

        impl haste::Intern for #ident {}

        impl #ident {
            pub fn new(db: &dyn #db_path, data: #data_ident) -> Self {
                haste::DatabaseExt::insert(db, data)
            }
        }

        impl std::fmt::Debug for #ident {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                haste::fmt::with_storage::<#storage_path>(|db| {
                    if let Some(db) = db {
                        let value = haste::DatabaseExt::lookup(db, *self);
                        std::fmt::Debug::fmt(value, f)
                    } else {
                        write!(f, concat!(#ident_text, "({:?})"), self.0)
                    }
                })
            }
        }
    }
}
