use std::collections::HashMap;

use syn::spanned::Spanned;

pub struct Arguments {
    pub db: syn::Path,
    pub storage: syn::Path,
    pub clone: bool,
}

impl Default for Arguments {
    fn default() -> Self {
        Arguments {
            db: syn::parse_quote!(crate::Db),
            storage: syn::parse_quote!(crate::Storage),
            clone: false,
        }
    }
}

#[derive(Default)]
#[non_exhaustive]
pub struct ArgumentOptions {
    pub db: bool,
    pub storage: bool,
    pub clone: bool,
}

pub fn extract_attrs(
    attrs: &mut Vec<syn::Attribute>,
    options: ArgumentOptions,
) -> syn::Result<Arguments> {
    let mut args = Arguments::default();
    let mut parser = AttrParser::default();

    if options.db {
        parser.expect_path("db", |path| args.db = path);
    }
    if options.storage {
        parser.expect_path("storage", |path| args.storage = path);
    }
    if options.clone {
        parser.expect_flag("clone", |enabled| args.clone = enabled);
    }

    parser.parse(attrs)?;

    Ok(args)
}

#[derive(Default)]
pub struct AttrParser<'a> {
    error: Option<syn::Error>,
    parsers: HashMap<&'static str, Option<Parser<'a>>>,
}

type Parser<'a> = Box<dyn FnOnce(&syn::Attribute) -> syn::Result<()> + 'a>;

impl<'a> AttrParser<'a> {
    fn expect(
        &mut self,
        name: &'static str,
        parser: impl FnOnce(&syn::Attribute) -> syn::Result<()> + 'a,
    ) {
        self.parsers.insert(name, Some(Box::new(parser)));
    }

    fn emit_error(&mut self, error: syn::Error) {
        match &mut self.error {
            None => self.error = Some(error),
            Some(combined) => combined.combine(error),
        }
    }

    pub fn expect_path(&mut self, name: &'static str, f: impl FnOnce(syn::Path) + 'a) {
        self.expect(name, move |attr| attr.parse_args().map(f))
    }

    pub fn expect_flag(&mut self, name: &'static str, f: impl FnOnce(bool) + 'a) {
        self.expect(name, move |attr| parse_flag(attr).map(f))
    }

    pub fn parse(mut self, attributes: &mut Vec<syn::Attribute>) -> syn::Result<()> {
        attributes.retain(|attr| {
            let Some(ident) = attr.path.get_ident() else { return true; };
            let name = ident.to_string();
            let Some(parser) = self.parsers.get_mut(name.as_str()) else { return true; };

            match parser.take() {
                Some(parser) => {
                    if let Err(error) = parser(attr) {
                        self.emit_error(error)
                    }
                }
                None => self.emit_error(syn::Error::new(attr.path.span(), "duplicate attribute")),
            }

            return false;
        });

        match self.error {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
}

fn parse_flag(attr: &syn::Attribute) -> syn::Result<bool> {
    if attr.tokens.is_empty() {
        return Ok(true);
    }

    Err(syn::Error::new(
        attr.tokens.span(),
        "unexpected attribute arguments",
    ))
}
