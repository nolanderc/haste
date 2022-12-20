use syn::spanned::Spanned;

pub struct Field<'a> {
    pub index: syn::Index,
    pub member: syn::Member,
    pub ty: &'a syn::Type,
}

pub fn field_info(fields: &syn::Fields) -> syn::Result<Vec<Field>> {
    let mut info = Vec::with_capacity(fields.len());

    match fields {
        syn::Fields::Unnamed(_) if fields.len() != 1 => {
            return Err(syn::Error::new(
                fields.span(),
                "may only have a single unnamed field",
            ))
        }
        _ => {}
    }

    for (index, field) in fields.iter().enumerate() {
        let index = syn::Index {
            index: index as _,
            span: field.span(),
        };

        let member = match &field.ident {
            Some(ident) => syn::Member::Named(ident.clone()),
            None => syn::Member::Unnamed(index.clone()),
        };

        info.push(Field {
            index,
            member,
            ty: &field.ty,
        });
    }

    Ok(info)
}
