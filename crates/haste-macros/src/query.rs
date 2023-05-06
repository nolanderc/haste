use proc_macro2::{TokenStream, TokenTree};
use quote::{quote, ToTokens};
use syn::{parse::Parse, punctuated::Punctuated, spanned::Spanned, Result, Token};

pub fn query(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    if !attr.is_empty() {
        return Err(syn::Error::new_spanned(attr, "unexpected arguments"));
    }

    let query_fn = syn::parse2::<QueryFunction>(item)?;
    let signature = &query_fn.signature;
    let parameters = &signature.params;

    if parameters.is_empty() {
        return Err(syn::Error::new(
            query_fn.signature.paren_token.span.span(),
            "expected a database as the first argument",
        ));
    }

    let db = &query_fn.signature.params[0];
    let db_ident = &db.ident;

    let mut input_idents = Vec::with_capacity(parameters.len() - 1);
    let mut input_types = Vec::with_capacity(parameters.len() - 1);
    for param in parameters.iter().skip(1) {
        input_idents.push(&param.ident);
        input_types.push(&param.typ);
    }

    let vis = &query_fn.signature.vis;
    let ident = &query_fn.signature.ident;

    let mut tokens = TokenStream::new();

    let return_type = &query_fn.signature.return_type;
    let attrs = &query_fn.attrs;
    let block = query_fn.block;

    tokens.extend(quote! {
        #[allow(non_camel_case_types)]
        #vis enum #ident {}

        impl #ident {
            #(#attrs)*
            #signature #block
        }

        impl haste::Element for #ident {
            type Storage = Storage;
            type Container = haste::QueryCache<Self>;
        }

        impl haste::Query for #ident {
            type Input = (#(#input_types),*);
            type Output = #return_type;

            #[inline]
            fn execute(
                #db_ident: &haste::ElementDb<Self>,
                (#(#input_idents),*): Self::Input
            ) -> Self::Output {
                #ident::#ident(#db_ident, #(#input_idents),*)
            }
        }

        #signature {
            let output = haste::DatabaseExt::query::<#ident>(#db_ident, (#(#input_idents),*));
            let output = Clone::clone(output);
            output
        }

        impl #ident {
            pub fn spawn<'db>(
                #db_ident: &'db haste::ElementDb<Self>,
                #(#input_idents: #input_types),*
            ) -> haste::QueryHandle<'db, Self> {
                haste::DatabaseExt::spawn::<#ident>(#db_ident, (#(#input_idents),*))
            }
        }
    });

    Ok(tokens)
}

struct QueryFunction {
    attrs: Vec<syn::Attribute>,
    signature: QuerySignature,
    block: TokenTree,
}

impl Parse for QueryFunction {
    fn parse(input: syn::parse::ParseStream) -> Result<Self> {
        let attrs = input.call(syn::Attribute::parse_outer)?;

        let vis = input.parse::<syn::Visibility>()?;
        input.parse::<Token![fn]>()?;
        let ident = input.parse::<syn::Ident>()?;

        let parameters;
        let paren_token = syn::parenthesized!(parameters in input);
        let params = parameters.parse_terminated(QueryParameter::parse, Token![,])?;

        input.parse::<Token![->]>()?;
        let return_type = input.parse::<syn::Type>()?;

        let block = input.parse::<TokenTree>()?;

        Ok(Self {
            attrs,
            signature: QuerySignature {
                vis,
                ident,
                paren_token,
                params,
                return_type,
            },
            block,
        })
    }
}

struct QuerySignature {
    vis: syn::Visibility,
    ident: syn::Ident,
    paren_token: syn::token::Paren,
    params: Punctuated<QueryParameter, Token![,]>,
    return_type: syn::Type,
}

impl ToTokens for QuerySignature {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self {
            vis,
            ident,
            paren_token: _,
            params,
            return_type,
        } = self;

        tokens.extend(quote! {
            #vis fn #ident(#params) -> #return_type
        });
    }
}

struct QueryParameter {
    ident: syn::Ident,
    typ: syn::Type,
}

impl ToTokens for QueryParameter {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self { ident, typ } = self;
        tokens.extend(quote! { #ident: #typ });
    }
}

impl Parse for QueryParameter {
    fn parse(input: syn::parse::ParseStream) -> Result<Self> {
        let ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let typ = input.parse()?;
        Ok(Self { ident, typ })
    }
}
