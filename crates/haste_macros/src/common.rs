use quote::format_ident;
use syn::spanned::Spanned;

pub struct FieldInfo<'a> {
    pub arguments: FieldArguments,
    pub index: syn::Index,
    pub vis: &'a syn::Visibility,
    pub member: syn::Member,
    pub ty: &'a syn::Type,
}

#[derive(Default)]
pub struct FieldArguments {
    pub clone: bool,
}

impl<'a> FieldInfo<'a> {
    pub fn getter(&self) -> syn::Ident {
        match &self.member {
            syn::Member::Named(ident) => ident.clone(),
            syn::Member::Unnamed(index) => {
                if index.index == 0 {
                    format_ident!("get", span = index.span)
                } else {
                    format_ident!("get_{}", index.index, span = index.span)
                }
            }
        }
    }

    pub fn extract(fields: &mut syn::Fields) -> syn::Result<Vec<FieldInfo>> {
        let mut info = Vec::with_capacity(fields.len());

        for (index, field) in fields.iter_mut().enumerate() {
            let span = match &field.ident {
                Some(ident) => ident.span(),
                None => field.ty.span(),
            };

            let index = syn::Index {
                index: index as _,
                span,
            };

            let member = match &field.ident {
                Some(ident) => syn::Member::Named(ident.clone()),
                None => syn::Member::Unnamed(index.clone()),
            };

            let arguments = FieldArguments::from_attrs(&mut field.attrs)?;

            info.push(FieldInfo {
                arguments,
                index,
                vis: &field.vis,
                member,
                ty: &field.ty,
            });
        }

        Ok(info)
    }
}

impl FieldArguments {
    fn from_attrs(attrs: &mut Vec<syn::Attribute>) -> syn::Result<Self> {
        let mut args = Self::default();
        let mut parser = crate::meta::AttrParser::default();

        parser.expect_flag("clone", |enable| args.clone = enable);

        parser.parse(attrs)?;

        Ok(args)
    }
}
