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
            &haste::DatabaseExt::intern_lookup(db, self).#member
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
                pub fn #getter(self, db: &dyn #db_path) -> #output_type {
                    #extractor
                }
            }
        });
    }

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

    // create a getter:
    {
        let mut output_type = data_ident.to_token_stream();
        let mut extractor = quote! {
            haste::DatabaseExt::intern_lookup(db, self)
        };

        if args.clone {
            extractor = quote! {
                <#data_ident as std::clone::Clone>::clone(#extractor)
            }
        } else {
            output_type = syn::parse_quote! { &#output_type };
        }

        impls.extend(quote_spanned! {input.ident.span()=>
            impl #ingredient {
                pub fn get(self, db: &dyn #db_path) -> #output_type {
                    #extractor
                }
            }
        });
    }

    let mut tokens = input.to_token_stream();
    tokens.extend(impls);
    Ok(tokens)
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

    quote! {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        #vis struct #ident(haste::Id);

        impl haste::Ingredient for #ident {
            type Container = haste::interner::ArenaInterner<#data_ident>;
            type Storage = #storage_path;
        }

        impl haste::Intern for #ident {
            type Value = #data_ident;

            fn from_id(id: haste::Id) -> Self {
                Self(id)
            }

            fn id(self) -> haste::Id {
                self.0
            }
        }

        impl #ident {
            pub fn new(db: &dyn #db_path, data: #data_ident) -> Self {
                haste::DatabaseExt::intern(db, data)
            }
        }
    }
}
