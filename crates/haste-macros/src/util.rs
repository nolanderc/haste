use std::collections::{HashMap, HashSet};

use proc_macro2::{TokenStream, TokenTree};
use syn::{
    parse::{Parse, Parser},
    punctuated::Punctuated,
    Result, Token,
};

pub fn parse_flags(attr: TokenStream, expected: &[&'static str]) -> Result<FlagSet> {
    let allowed = expected.iter().copied().collect::<HashSet<_>>();

    let list = Punctuated::<Flag, Token![,]>::parse_terminated.parse2(attr)?;
    let mut flags = HashMap::with_capacity(list.len());

    for flag in list.into_iter() {
        let name = flag.name.to_string();
        if allowed.contains(name.as_str()) {
            flags.insert(name, flag);
        } else {
            crate::emit_error(syn::Error::new_spanned(flag.name, "invalid flag name"))
        }
    }

    Ok(FlagSet { flags })
}

pub struct FlagSet {
    flags: HashMap<String, Flag>,
}

impl FlagSet {
    pub fn get_flag<'a>(&'a self, name: &str) -> Option<&'a syn::Ident> {
        let flag = self.flags.get(name)?;
        if let Some(value) = &flag.value {
            crate::emit_error(syn::Error::new_spanned(value, "unexpected value"));
        }
        Some(&flag.name)
    }
}

pub struct Flag {
    pub name: syn::Ident,
    pub eq_token: Option<Token![=]>,
    pub value: Option<TokenStream>,
}

impl Parse for Flag {
    fn parse(input: syn::parse::ParseStream) -> Result<Self> {
        let name = input.parse()?;
        let mut eq_token = None;
        let mut value = None;

        if input.peek(Token![=]) {
            eq_token = Some(input.parse::<Token![=]>()?);

            let mut tokens = Vec::new();
            while !input.is_empty() && !input.peek(Token![,]) {
                tokens.push(input.parse::<TokenTree>()?);
            }
            value = Some(tokens.into_iter().collect());
        }

        Ok(Self {
            name,
            eq_token,
            value,
        })
    }
}
