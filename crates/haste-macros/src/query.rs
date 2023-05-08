use proc_macro2::{TokenStream, TokenTree};
use quote::{quote, ToTokens};
use syn::{parse::Parse, punctuated::Punctuated, spanned::Spanned, Result, Token};

pub fn query(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    let mut is_input = false;

    if !attr.is_empty() {
        let ident = syn::parse2::<syn::Ident>(attr)?;
        if ident != "input" {
            return Err(syn::Error::new_spanned(ident, "expected token `input`"));
        }
        is_input = true;
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

    let mut argument_idents = Vec::with_capacity(parameters.len() - 1);
    let mut argument_types = Vec::with_capacity(parameters.len() - 1);
    for param in parameters.iter().skip(1) {
        argument_idents.push(&param.ident);
        argument_types.push(&param.typ);
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
            type Arguments = (#(#argument_types),*);
            type Output = #return_type;

            #[inline]
            fn execute(
                #db_ident: &haste::ElementDb<Self>,
                (#(#argument_idents),*): Self::Arguments
            ) -> Self::Output {
                #ident::#ident(#db_ident, #(#argument_idents),*)
            }
        }

        #signature {
            let output = haste::DatabaseExt::query::<#ident>(#db_ident, (#(#argument_idents),*));
            let output = Clone::clone(output);
            output
        }

        impl #ident {
            pub fn spawn<'db>(
                #db_ident: &'db haste::ElementDb<Self>,
                #(#argument_idents: #argument_types),*
            ) -> haste::QueryHandle<'db, Self> {
                haste::DatabaseExt::spawn::<#ident>(#db_ident, (#(#argument_idents),*))
            }
        }
    });

    if is_input {
        tokens.extend(quote! {
            impl #ident {
                pub fn set<'db>(
                    #db_ident: &'db haste::ElementDb<Self>,
                    #(#argument_idents: #argument_types),*
                    __output: #return_type,
                    __durability: haste::Durability,
                ) -> haste::QueryHandle<'db, Self> {
                    haste::DatabaseExt::set::<#ident>(
                        #db_ident,
                        (#(#argument_idents),*),
                        __output,
                        __durability,
                    )
                }

                pub fn invalidate<'db>(
                    #db_ident: &'db haste::ElementDb<Self>,
                    #(#argument_idents: #argument_types),*
                ) -> haste::QueryHandle<'db, Self> {
                    haste::DatabaseExt::invalidate::<#ident>(#db_ident, (#(#argument_idents),*))
                }
            }
        });
    }

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
