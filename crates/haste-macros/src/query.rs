use proc_macro2::{TokenStream, TokenTree};
use quote::{quote, quote_spanned, ToTokens};
use syn::{parse::Parse, punctuated::Punctuated, spanned::Spanned, Result, Token};

pub fn query(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    let flags = crate::util::parse_flags(attr, &["input", "clone"])?;

    let input_flag = flags.get_flag("input");
    let clone_flag = flags.get_flag("clone");

    let mut query_fn = syn::parse2::<QueryFunction>(item)?;
    let signature = &mut query_fn.signature;
    let parameters = &signature.params;

    if parameters.is_empty() {
        return Err(syn::Error::new(
            query_fn.signature.paren_token.span.span(),
            "expected a database as the first argument",
        ));
    }

    let db = &signature.params[0];
    let db_ident = &db.ident;
    let db_type = match &db.typ {
        syn::Type::Reference(reference) => &*reference.elem,
        _ => {
            return Err(syn::Error::new_spanned(
                &db.typ,
                "expected a reference to a database",
            ))
        }
    };

    let mut argument_idents = Vec::with_capacity(parameters.len() - 1);
    let mut argument_types = Vec::with_capacity(parameters.len() - 1);
    for param in parameters.iter().skip(1) {
        argument_idents.push(&param.ident);
        argument_types.push(&param.typ);
    }

    let vis = &signature.vis;
    let ident = &signature.ident;

    let mut tokens = TokenStream::new();

    let attrs = &query_fn.attrs;
    let block = query_fn.block;

    let output_type = &signature.output_type;

    let view_type = if clone_flag.is_some() {
        quote! { #output_type }
    } else {
        quote_spanned! { output_type.span()=> &'a #output_type }
    };

    let view_body = if let Some(ident) = clone_flag {
        quote_spanned! { ident.span()=>
            std::clone::Clone::clone(output)
        }
    } else {
        quote! {
            output
        }
    };

    let is_input = input_flag.is_some();
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
            type Output = #output_type;
            type View<'a> = #view_type;

            const IS_INPUT: bool = #is_input;

            #[inline]
            fn execute(
                #db_ident: &haste::ElementDb<Self>,
                (#(#argument_idents),*): Self::Arguments
            ) -> Self::Output {
                #ident::#ident(#db_ident, #(#argument_idents),*)
            }

            fn view(output: &Self::Output) -> Self::View<'_> {
                #view_body
            }
        }

        impl #ident {
            pub fn spawn<'db>(
                #db_ident: &'db #db_type,
                #(#argument_idents: #argument_types),*
            ) -> haste::QueryHandle<'db, Self> {
                haste::DatabaseExt::spawn::<#ident>(#db_ident, (#(#argument_idents),*))
            }
        }
    });

    if input_flag.is_some() {
        tokens.extend(quote! {
            impl haste::Input for #ident {}

            impl #ident {
                pub fn set(
                    #db_ident: &mut #db_type,
                    #(#argument_idents: #argument_types),*,
                    __output: #output_type,
                    __durability: haste::Durability,
                ) {
                    haste::DatabaseExt::set::<#ident>(
                        #db_ident,
                        (#(#argument_idents),*),
                        __output,
                        __durability,
                    )
                }

                pub fn invalidate<'db>(
                    #db_ident: &mut #db_type,
                    #(#argument_idents: #argument_types),*
                ) {
                    haste::DatabaseExt::invalidate::<#ident>(#db_ident, (#(#argument_idents),*))
                }
            }
        });
    }

    signature.output_type = syn::parse2(if clone_flag.is_some() {
        quote! { #output_type }
    } else {
        quote_spanned! { output_type.span()=> &#output_type }
    })?;

    tokens.extend(quote! {
        #signature {
            let output = haste::DatabaseExt::query::<#ident>(#db_ident, (#(#argument_idents),*));
            <#ident as haste::Query>::view(output)
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
                output_type: return_type,
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
    output_type: syn::Type,
}

impl ToTokens for QuerySignature {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self {
            vis,
            ident,
            paren_token: _,
            params,
            output_type: return_type,
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
