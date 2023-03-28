mod context;

use smallvec::SmallVec;

use crate::{
    common::Text,
    error,
    import::FileSet,
    naming::{self, AssignmentExpr, Builtin, DeclId},
    syntax::{self, NodeId},
    Result,
};

use self::context::TypingContext;

#[haste::storage]
pub struct Storage(Type, signature, type_check_body);

#[haste::intern(Type)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeKind {
    Untyped(ConstantKind),

    Builtin(BuiltinFunction),

    Bool,

    Int,
    Int8,
    Int16,
    Int32,
    Int64,

    Uint,
    Uint8,
    Uint16,
    Uint32,
    Uint64,

    Uintptr,

    Float32,
    Float64,

    Complex64,
    Complex128,

    Error,
    String,

    Pointer(Type),
    Slice(Type),
    Array(u64, Type),
    Map(Type, Type),
    Channel(syntax::ChannelKind, Type),

    Function(FunctionType),
    Struct(StructType),
    Interface(InterfaceType),

    // A declared type `type Foo <type>`
    Declared(DeclId),
}

bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct TypeClass: u16 {
        const UNTYPED = 0x01;
        const STRING = 0x02;
        const INTEGER = 0x04;
        const RUNE = 0x08;
        const FLOAT = 0x10;
        const COMPLEX = 0x20;
        const NILLABLE = 0x40;
        const SIGNED = 0x80;

        const TRIVIALLY_COMPARABLE = 0x100;
        const TRIVIALLY_ORDERED = 0x200 | Self::TRIVIALLY_COMPARABLE.bits();

        const NUMERIC = Self::INTEGER.bits() | Self::FLOAT.bits() | Self::COMPLEX.bits();
    }
}

impl TypeClass {
    pub fn is_untyped(self) -> bool {
        self.contains(Self::UNTYPED)
    }
    
    pub fn is_integer(self) -> bool {
        self.contains(Self::INTEGER)
    }
}

impl TypeKind {
    pub fn insert(self, db: &dyn crate::Db) -> Type {
        Type::insert(db, self)
    }

    pub fn class(&self) -> TypeClass {
        let untyped = TypeClass::UNTYPED;
        let comparable = TypeClass::TRIVIALLY_COMPARABLE;
        let ordered = TypeClass::TRIVIALLY_ORDERED;
        let nillable = TypeClass::NILLABLE;
        let signed = TypeClass::SIGNED;

        match self {
            TypeKind::Untyped(kind) => match kind {
                ConstantKind::Boolean => untyped | comparable,
                ConstantKind::Rune => TypeClass::RUNE | TypeClass::INTEGER | untyped | ordered,
                ConstantKind::Integer => TypeClass::INTEGER | untyped | ordered | signed,
                ConstantKind::Float => TypeClass::FLOAT | untyped | ordered | signed,
                ConstantKind::Complex => TypeClass::COMPLEX | untyped | comparable | signed,
                ConstantKind::String => TypeClass::STRING | nillable | untyped | ordered,
                ConstantKind::Nil => nillable | untyped | comparable,
            },

            TypeKind::Builtin(_) => TypeClass::empty(),
            TypeKind::Bool => comparable,

            TypeKind::Int
            | TypeKind::Int8
            | TypeKind::Int16
            | TypeKind::Int32
            | TypeKind::Int64 => TypeClass::INTEGER | ordered | signed,

            TypeKind::Uint
            | TypeKind::Uint8
            | TypeKind::Uint16
            | TypeKind::Uint32
            | TypeKind::Uint64
            | TypeKind::Uintptr => TypeClass::INTEGER | ordered,

            TypeKind::Float32 | TypeKind::Float64 => TypeClass::FLOAT | ordered | signed,
            TypeKind::Complex64 | TypeKind::Complex128 => TypeClass::COMPLEX | comparable | signed,

            TypeKind::Error => nillable | comparable,
            TypeKind::String => TypeClass::STRING | nillable | ordered,

            TypeKind::Pointer(_) => nillable | comparable,
            TypeKind::Slice(_) => nillable,
            TypeKind::Map(_, _) => nillable,
            TypeKind::Channel(_, _) => nillable,
            TypeKind::Function(_) => nillable,

            TypeKind::Struct(_) => TypeClass::empty(),
            TypeKind::Array(_, _) => TypeClass::empty(),

            TypeKind::Interface(_) => nillable | comparable,

            TypeKind::Declared(_) => TypeClass::empty(),
        }
    }

    pub fn is_numeric(&self) -> bool {
        self.class().contains(TypeClass::NUMERIC)
    }

    pub fn is_signed(&self) -> bool {
        self.class().contains(TypeClass::SIGNED)
    }

    pub fn is_integer(&self) -> bool {
        self.class().contains(TypeClass::INTEGER)
    }

    pub fn is_float(&self) -> bool {
        self.class().contains(TypeClass::FLOAT)
    }

    pub fn is_complex(&self) -> bool {
        self.class().contains(TypeClass::COMPLEX)
    }

    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Untyped(ConstantKind::Boolean) | Self::Bool)
    }

    pub fn is_string(&self) -> bool {
        matches!(self, Self::Untyped(ConstantKind::String) | Self::String)
    }

    pub fn is_nillable(&self) -> bool {
        self.class().contains(TypeClass::NILLABLE)
    }

    pub fn is_comparable(&self, db: &dyn crate::Db) -> bool {
        if self.class().contains(TypeClass::TRIVIALLY_COMPARABLE) {
            return true;
        }

        match self {
            Self::Array(_, inner) => inner.lookup(db).is_comparable(db),
            Self::Struct(strukt) => {
                for field in strukt.fields.iter() {
                    if !field.typ.lookup(db).is_comparable(db) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }

    pub fn is_ordered(&self, db: &dyn crate::Db) -> bool {
        self.class().contains(TypeClass::TRIVIALLY_ORDERED)
    }

    pub fn is_untyped(&self) -> bool {
        self.class().contains(TypeClass::UNTYPED)
    }
}

impl Type {
    pub fn value_type(self, db: &dyn crate::Db) -> Result<Type> {
        match self.lookup(db) {
            TypeKind::Untyped(constant) => {
                if let Some(typ) = constant.default_type() {
                    Ok(typ.insert(db))
                } else {
                    Err(error!(
                        "type annotations required to determine type of `nil`"
                    ))
                }
            }
            TypeKind::Builtin(builtin) => Err(error!(
                "type annotations required to determine type of built-in function `{builtin}`"
            )),

            _ => Ok(self),
        }
    }

    pub fn untyped_bool(db: &dyn crate::Db) -> Self {
        Self::insert(db, TypeKind::Untyped(ConstantKind::Boolean))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConstantKind {
    Boolean,
    Rune,
    Integer,
    Float,
    Complex,
    String,
    Nil,
}

impl ConstantKind {
    pub fn default_type(self) -> Option<TypeKind> {
        match self {
            ConstantKind::Boolean => Some(TypeKind::Bool),
            ConstantKind::Rune => Some(TypeKind::Int32),
            ConstantKind::Integer => Some(TypeKind::Int),
            ConstantKind::Float => Some(TypeKind::Float64),
            ConstantKind::Complex => Some(TypeKind::Complex128),
            ConstantKind::String => Some(TypeKind::String),
            ConstantKind::Nil => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionType {
    types: TypeList,
    inputs: usize,
    variadic: bool,
}

impl FunctionType {
    pub fn inputs(&self) -> &[Type] {
        &self.types[..self.inputs]
    }

    pub fn outputs(&self) -> &[Type] {
        &self.types[self.inputs..]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructType {
    pub fields: Box<[Field]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Field {
    pub name: Option<Text>,
    pub typ: Type,
    pub tag: Option<Text>,
    pub embedded: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InterfaceType {
    pub methods: Box<[InterfaceMethod]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InterfaceMethod {
    pub name: Text,
    pub signature: FunctionType,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BuiltinFunction {
    Append,
    Cap,
    Close,
    Complex,
    Copy,
    Delete,
    Imag,
    Len,
    Make,
    New,
    Panic,
    Print,
    Println,
    Real,
    Recover,
}

impl std::fmt::Display for BuiltinFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::io::Write;
        let mut buffer = [0u8; 16];
        let mut cursor = std::io::Cursor::new(&mut buffer[..]);
        write!(cursor, "{self:?}").unwrap();
        let end = cursor.position() as usize;
        let written = &mut buffer[..end];
        written[0] = written[0].to_ascii_lowercase();
        bstr::BStr::new(written).fmt(f)
    }
}

pub type TypeList = SmallVec<[Type; 4]>;

impl std::fmt::Display for TypeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeKind::Untyped(untyped) => match untyped.default_type() {
                Some(typ) => typ.fmt(f),
                None => write!(f, "nil"),
            },
            TypeKind::Builtin(builtin) => write!(f, "builtin[{:?}]", builtin),
            TypeKind::Error => write!(f, "error"),
            TypeKind::Bool => write!(f, "bool"),
            TypeKind::Int => write!(f, "int"),
            TypeKind::Int8 => write!(f, "int8"),
            TypeKind::Int16 => write!(f, "int16"),
            TypeKind::Int32 => write!(f, "int32"),
            TypeKind::Int64 => write!(f, "int64"),
            TypeKind::Uint => write!(f, "uint"),
            TypeKind::Uint8 => write!(f, "uint8"),
            TypeKind::Uint16 => write!(f, "uint16"),
            TypeKind::Uint32 => write!(f, "uint32"),
            TypeKind::Uint64 => write!(f, "uint64"),
            TypeKind::Uintptr => write!(f, "uintptr"),
            TypeKind::Float32 => write!(f, "float32"),
            TypeKind::Float64 => write!(f, "float64"),
            TypeKind::Complex64 => write!(f, "complex64"),
            TypeKind::Complex128 => write!(f, "complex128"),
            TypeKind::String => write!(f, "string"),
            TypeKind::Pointer(inner) => write!(f, "*{inner}"),
            TypeKind::Slice(inner) => write!(f, "[]{inner}"),
            TypeKind::Array(len, inner) => write!(f, "[{len}]{inner}"),
            TypeKind::Map(key, value) => write!(f, "map[{key}]{value}"),
            TypeKind::Channel(syntax::ChannelKind::SendRecv, inner) => write!(f, "chan {inner}"),
            TypeKind::Channel(syntax::ChannelKind::Send, inner) => write!(f, "chan<- {inner}"),
            TypeKind::Channel(syntax::ChannelKind::Recv, inner) => write!(f, "<-chan {inner}"),
            TypeKind::Function(func) => func.fmt(f),
            TypeKind::Struct(strukt) => {
                write!(f, "struct {{")?;

                for (i, field) in strukt.fields.iter().enumerate() {
                    if i == 0 {
                        write!(f, " ")?;
                    } else {
                        write!(f, "; ")?;
                    }

                    if field.embedded {
                        write!(f, "{}", field.typ)?;
                    } else if let Some(name) = field.name {
                        write!(f, "{} {}", name, field.typ)?;
                    } else {
                        write!(f, "_ {}", field.typ)?;
                    }

                    if let Some(tag) = field.tag {
                        write!(f, " {:?}", tag)?;
                    }
                }

                if strukt.fields.is_empty() {
                    write!(f, "}}")
                } else {
                    write!(f, " }}")
                }
            }
            TypeKind::Interface(interface) => {
                write!(f, "interface {{")?;

                for (i, method) in interface.methods.iter().enumerate() {
                    if i == 0 {
                        write!(f, " ")?;
                    } else {
                        write!(f, "; ")?;
                    }

                    method.signature.fmt(f)?;
                }

                if interface.methods.is_empty() {
                    write!(f, "}}")
                } else {
                    write!(f, " }}")
                }
            }
            TypeKind::Declared(decl) => write!(f, "{:?}.{}", decl.package, decl.name),
        }
    }
}

impl std::fmt::Display for FunctionType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "func(")?;
        for (i, input) in self.inputs().iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", input)?;
        }
        write!(f, ")")?;

        match self.outputs() {
            [] => {}
            [single] => write!(f, " {single}")?,
            outputs => {
                write!(f, " (")?;
                for (i, output) in outputs.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", output)?;
                }
                write!(f, ")")?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Signature {
    Package(FileSet),
    Type(Type),
    Value(Type),
}

/// Get the type of the given symbol
#[haste::query]
#[clone]
pub async fn signature(db: &dyn crate::Db, symbol: naming::GlobalSymbol) -> Result<Signature> {
    match symbol {
        naming::GlobalSymbol::Package(package) => Ok(Signature::Package(package)),
        naming::GlobalSymbol::Builtin(builtin) => Ok(builtin_signature(db, builtin)),
        naming::GlobalSymbol::Decl(decl) => decl_signature(db, decl).await,
    }
}

async fn decl_signature(db: &dyn crate::Db, decl: DeclId) -> Result<Signature> {
    let mut ctx = TypingContext::new(db, decl).await?;
    let path = ctx.path;

    let declaration = &ctx.ast.declarations[path.index];

    match path.sub.lookup_in(declaration) {
        naming::SingleDecl::TypeDef(_) => {
            let inner = Type::insert(db, TypeKind::Declared(decl));
            Ok(Signature::Type(inner))
        }
        naming::SingleDecl::TypeAlias(spec) => {
            let inner = ctx.resolve_precise(spec.inner).await?;
            Ok(Signature::Type(inner))
        }

        naming::SingleDecl::VarDecl(_, Some(typ), _)
        | naming::SingleDecl::ConstDecl(_, Some(typ), _) => {
            ctx.resolve_precise(typ).await.map(Signature::Value)
        }

        naming::SingleDecl::VarDecl(_, _, Some(AssignmentExpr::Single(expr)))
        | naming::SingleDecl::ConstDecl(_, _, expr) => {
            let typ = ctx.infer_expr(expr).await?;
            match typ.value_type(db) {
                Err(error) => Err(error.label(ctx.node_span(expr), "could not infer type")),
                Ok(typ) => Ok(Signature::Value(typ)),
            }
        }

        naming::SingleDecl::VarDecl(_, _, Some(AssignmentExpr::Destruct(expr))) => {
            let types = ctx.infer_assignment(expr).await?;
            let typ = match types.get(path.sub.col as usize).copied() {
                Some(typ) => typ,
                None => {
                    return Err(error!("too many bindings in variable declaration")
                        .label(
                            path.span_in_ast(ctx.ast),
                            format!("expected {} values", path.sub.col + 1,),
                        )
                        .label(
                            ctx.node_span(expr),
                            format!("expression provides {} values", types.len()),
                        ))
                }
            };

            match typ.value_type(db) {
                Err(error) => Err(error.label(ctx.node_span(expr), "could not infer type")),
                Ok(typ) => Ok(Signature::Value(typ)),
            }
        }

        naming::SingleDecl::VarDecl(_, None, None) => Err(error!(
            "variables must specify a type, a value, or both"
        )
        .label(
            path.span_in_ast(ctx.ast),
            "cannot infer type without type or value",
        )),

        naming::SingleDecl::Function(func) | naming::SingleDecl::Method(func) => {
            let func = ctx.resolve_signature(func.signature).await?;
            Ok(Signature::Value(TypeKind::Function(func).insert(db)))
        }
    }
}

fn builtin_signature(db: &dyn crate::Db, builtin: Builtin) -> Signature {
    let make_type = |inner| Signature::Type(Type::insert(db, inner));
    let make_value = |inner| Signature::Value(Type::insert(db, inner));

    match builtin {
        Builtin::Bool => make_type(TypeKind::Bool),
        Builtin::Byte => make_type(TypeKind::Uint8),
        Builtin::Complex64 => make_type(TypeKind::Complex64),
        Builtin::Complex128 => make_type(TypeKind::Complex128),
        Builtin::Error => make_type(TypeKind::Error),
        Builtin::Float32 => make_type(TypeKind::Float32),
        Builtin::Float64 => make_type(TypeKind::Float64),
        Builtin::Int => make_type(TypeKind::Int),
        Builtin::Int8 => make_type(TypeKind::Int8),
        Builtin::Int16 => make_type(TypeKind::Int16),
        Builtin::Int32 => make_type(TypeKind::Int32),
        Builtin::Int64 => make_type(TypeKind::Int64),
        Builtin::Uint => make_type(TypeKind::Uint),
        Builtin::Uint8 => make_type(TypeKind::Uint8),
        Builtin::Uint16 => make_type(TypeKind::Uint16),
        Builtin::Uint32 => make_type(TypeKind::Uint32),
        Builtin::Uint64 => make_type(TypeKind::Uint64),
        Builtin::Uintptr => make_type(TypeKind::Uintptr),
        Builtin::Rune => make_type(TypeKind::Int32),
        Builtin::String => make_type(TypeKind::String),

        Builtin::True | Builtin::False => make_value(TypeKind::Untyped(ConstantKind::Boolean)),

        Builtin::Iota => make_value(TypeKind::Untyped(ConstantKind::Integer)),

        Builtin::Nil => make_value(TypeKind::Untyped(ConstantKind::Nil)),

        Builtin::Append => make_value(TypeKind::Builtin(BuiltinFunction::Append)),
        Builtin::Cap => make_value(TypeKind::Builtin(BuiltinFunction::Cap)),
        Builtin::Close => make_value(TypeKind::Builtin(BuiltinFunction::Close)),
        Builtin::Complex => make_value(TypeKind::Builtin(BuiltinFunction::Complex)),
        Builtin::Copy => make_value(TypeKind::Builtin(BuiltinFunction::Copy)),
        Builtin::Delete => make_value(TypeKind::Builtin(BuiltinFunction::Delete)),
        Builtin::Imag => make_value(TypeKind::Builtin(BuiltinFunction::Imag)),
        Builtin::Len => make_value(TypeKind::Builtin(BuiltinFunction::Len)),
        Builtin::Make => make_value(TypeKind::Builtin(BuiltinFunction::Make)),
        Builtin::New => make_value(TypeKind::Builtin(BuiltinFunction::New)),
        Builtin::Panic => make_value(TypeKind::Builtin(BuiltinFunction::Panic)),
        Builtin::Print => make_value(TypeKind::Builtin(BuiltinFunction::Print)),
        Builtin::Println => make_value(TypeKind::Builtin(BuiltinFunction::Println)),
        Builtin::Real => make_value(TypeKind::Builtin(BuiltinFunction::Real)),
        Builtin::Recover => make_value(TypeKind::Builtin(BuiltinFunction::Recover)),
    }
}

#[derive(Debug, PartialEq, Eq, Default)]
pub struct TypingInfo {
    /// For each syntax node, its type (only `ExprId` and `TypeId`).
    nodes: crate::HashMap<NodeId, Type>,
    /// The type of local variables.
    locals: crate::HashMap<naming::Local, Type>,
}

/// Type-check the entire symbol, returning the types of all applicable syntax nodes (types and
/// expressions).
#[haste::query]
pub async fn type_check_body(db: &dyn crate::Db, decl: DeclId) -> Result<TypingInfo> {
    let mut ctx = TypingContext::new(db, decl).await?;
    let path = ctx.path;

    let declaration = &ctx.ast.declarations[path.index];

    match path.sub.lookup_in(declaration) {
        naming::SingleDecl::TypeDef(spec) | naming::SingleDecl::TypeAlias(spec) => {
            ctx.resolve_precise(spec.inner).await?;
            ctx.finish()
        }

        naming::SingleDecl::VarDecl(_, typ, Some(AssignmentExpr::Single(expr)))
        | naming::SingleDecl::ConstDecl(_, typ, expr) => {
            if let Some(typ) = typ {
                let actual_type = ctx.resolve_type(typ).await?;
                ctx.check_expr(expr, actual_type).await?;
            } else {
                ctx.infer_expr(expr).await?;
            }
            ctx.finish()
        }

        naming::SingleDecl::VarDecl(_, typ, Some(AssignmentExpr::Destruct(expr))) => {
            let expected = match typ {
                Some(typ) => Some(ctx.resolve_type(typ).await?),
                None => None,
            };

            let types = ctx.infer_assignment(expr).await?;
            let mut found_type = match types.get(path.sub.col as usize).copied() {
                Some(typ) => typ,
                None => {
                    return Err(error!("too many bindings in variable declaration")
                        .label(
                            path.span_in_ast(ctx.ast),
                            format!("expected {} values", path.sub.col + 1,),
                        )
                        .label(
                            ctx.node_span(expr),
                            format!("expression provides {} values", types.len()),
                        ))
                }
            };

            found_type = found_type
                .value_type(db)
                .map_err(|error| error.label(ctx.node_span(expr), "could not infer type"))?;

            if let Some(expected) = expected {
                if expected != found_type {
                    return Err(error!("type mismatch in variable declaration")
                        .label(
                            path.span_in_ast(ctx.ast),
                            format!("expected value of type `{expected}`"),
                        )
                        .label(
                            ctx.node_span(expr),
                            format!("found multi-valued expression of type `{found_type}`"),
                        ));
                }
            }

            ctx.finish()
        }

        naming::SingleDecl::VarDecl(_, Some(typ), None) => {
            ctx.resolve_type(typ).await?;
            ctx.finish()
        }

        naming::SingleDecl::VarDecl(_, None, None) => Err(error!(
            "variables must specify a type, a value, or both"
        )
        .label(
            path.span_in_ast(ctx.ast),
            "cannot infer type without type or value",
        )),

        naming::SingleDecl::Function(func) | naming::SingleDecl::Method(func) => {
            if let Some(body) = func.body {
                ctx.check_function(func.signature, body).await?;
            } else {
                ctx.resolve_signature(func.signature).await?;
            }
            ctx.finish()
        }
    }
}
