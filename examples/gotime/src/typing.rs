mod context;

use smallvec::SmallVec;

use crate::{
    common::Text,
    error,
    import::FileSet,
    naming::{self, AssignmentExpr, Builtin, DeclId},
    syntax, Result,
};

use self::context::TypingContext;

#[haste::storage]
pub struct Storage(Type, symbol_type);

#[haste::intern(Type)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeKind {
    /// The type of types. Only allowed in type contexts. This is an abstract type and cannot be
    /// referenced in code.
    Type(Type),
    /// The type of a package. Only allowed in qualified identifiers.
    Package(FileSet),

    Untyped(ConstantKind),

    Builtin(BuiltinFunction),

    Error,
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

    String,

    Pointer(Type),
    Slice(Type),
    Array(u32, Type),
    Map(Type, Type),
    Channel(syntax::ChannelKind, Type),

    Function(FunctionType),
    Struct(StructType),
    Interface(InterfaceType),

    // A declared type `type Foo <type>`
    Declared(DeclId),
}

impl TypeKind {
    pub fn insert(self, db: &dyn crate::Db) -> Type {
        Type::insert(db, self)
    }
}

impl Type {
    pub fn value_type(self, db: &dyn crate::Db) -> Result<Type> {
        match self.lookup(db) {
            TypeKind::Package(_) => Err(error!("packages are not values")),
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

            TypeKind::Type(_) => Err(error!("types are not values")),

            _ => Ok(self),
        }
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

/// Get the type of the given symbol
#[haste::query]
#[clone]
pub async fn symbol_type(db: &dyn crate::Db, symbol: naming::GlobalSymbol) -> Result<Type> {
    match symbol {
        naming::GlobalSymbol::Package(package) => Ok(Type::insert(db, TypeKind::Package(package))),
        naming::GlobalSymbol::Builtin(builtin) => Ok(builtin_type(db, builtin)),
        naming::GlobalSymbol::Decl(decl) => decl_type(db, decl).await,
    }
}

async fn decl_type(db: &dyn crate::Db, decl: DeclId) -> Result<Type> {
    let mut context = TypingContext::new(db, decl).await?;
    let path = context.path;

    let declaration = &context.ast.declarations[path.index];

    match path.sub.lookup_in(declaration) {
        naming::SingleDecl::TypeDef(_) => {
            let inner = Type::insert(db, TypeKind::Declared(decl));
            Ok(TypeKind::Type(inner).insert(db))
        }
        naming::SingleDecl::TypeAlias(spec) => {
            let inner = context.resolve_precise(spec.inner).await?;
            Ok(TypeKind::Type(inner).insert(db))
        }

        naming::SingleDecl::VarDecl(_, Some(typ), _)
        | naming::SingleDecl::ConstDecl(_, Some(typ), _) => context.resolve_precise(typ).await,

        naming::SingleDecl::VarDecl(_, _, Some(AssignmentExpr::Single(expr)))
        | naming::SingleDecl::ConstDecl(_, _, expr) => {
            context.fetch_external_references([expr]).await?;
            let typ = context.infer_expr(expr)?;
            match typ.value_type(db) {
                Err(error) => Err(error.label(context.node_span(expr), "could not infer type")),
                Ok(typ) => Ok(typ),
            }
        }

        naming::SingleDecl::VarDecl(_, _, Some(AssignmentExpr::Destruct(expr))) => {
            context.fetch_external_references([expr]).await?;
            let types = context.infer_assignment(expr)?;
            let typ = match types.get(path.sub.col as usize).copied() {
                Some(typ) => typ,
                None => {
                    return Err(error!("too many bindings in variable declaration")
                        .label(
                            path.span_in_ast(context.ast),
                            format!("expected {} values", path.sub.col + 1,),
                        )
                        .label(
                            context.node_span(expr),
                            format!("expression provides {} values", types.len()),
                        ))
                }
            };

            match typ.value_type(db) {
                Err(error) => Err(error.label(context.node_span(expr), "could not infer type")),
                Ok(typ) => Ok(typ),
            }
        }

        naming::SingleDecl::VarDecl(_, None, None) => Err(error!(
            "variables must specify a type, a value, or both"
        )
        .label(
            path.span_in_ast(context.ast),
            "cannot infer type without type or value",
        )),

        naming::SingleDecl::Function(func) | naming::SingleDecl::Method(func) => {
            let parameters = context.nodes.indirect(func.signature.inputs_and_outputs());
            context
                .fetch_external_references(parameters.iter().copied())
                .await?;
            let func = context.resolve_signature(func.signature)?;
            Ok(TypeKind::Function(func).insert(db))
        }
    }
}

fn builtin_type(db: &dyn crate::Db, builtin: Builtin) -> Type {
    let builtin_type = |db, inner| TypeKind::Type(Type::insert(db, inner));

    let kind = match builtin {
        Builtin::Bool => builtin_type(db, TypeKind::Bool),
        Builtin::Byte => builtin_type(db, TypeKind::Uint8),
        Builtin::Complex64 => builtin_type(db, TypeKind::Complex64),
        Builtin::Complex128 => builtin_type(db, TypeKind::Complex128),
        Builtin::Error => builtin_type(db, TypeKind::Error),
        Builtin::Float32 => builtin_type(db, TypeKind::Float32),
        Builtin::Float64 => builtin_type(db, TypeKind::Float64),
        Builtin::Int => builtin_type(db, TypeKind::Int),
        Builtin::Int8 => builtin_type(db, TypeKind::Int8),
        Builtin::Int16 => builtin_type(db, TypeKind::Int16),
        Builtin::Int32 => builtin_type(db, TypeKind::Int32),
        Builtin::Int64 => builtin_type(db, TypeKind::Int64),
        Builtin::Uint => builtin_type(db, TypeKind::Uint),
        Builtin::Uint8 => builtin_type(db, TypeKind::Uint8),
        Builtin::Uint16 => builtin_type(db, TypeKind::Uint16),
        Builtin::Uint32 => builtin_type(db, TypeKind::Uint32),
        Builtin::Uint64 => builtin_type(db, TypeKind::Uint64),
        Builtin::Uintptr => builtin_type(db, TypeKind::Uintptr),
        Builtin::Rune => builtin_type(db, TypeKind::Int32),
        Builtin::String => builtin_type(db, TypeKind::String),

        Builtin::True | Builtin::False => TypeKind::Bool,

        Builtin::Iota => TypeKind::Untyped(ConstantKind::Integer),

        Builtin::Nil => TypeKind::Untyped(ConstantKind::Nil),

        Builtin::Append => TypeKind::Builtin(BuiltinFunction::Append),
        Builtin::Cap => TypeKind::Builtin(BuiltinFunction::Cap),
        Builtin::Close => TypeKind::Builtin(BuiltinFunction::Close),
        Builtin::Complex => TypeKind::Builtin(BuiltinFunction::Complex),
        Builtin::Copy => TypeKind::Builtin(BuiltinFunction::Copy),
        Builtin::Delete => TypeKind::Builtin(BuiltinFunction::Delete),
        Builtin::Imag => TypeKind::Builtin(BuiltinFunction::Imag),
        Builtin::Len => TypeKind::Builtin(BuiltinFunction::Len),
        Builtin::Make => TypeKind::Builtin(BuiltinFunction::Make),
        Builtin::New => TypeKind::Builtin(BuiltinFunction::New),
        Builtin::Panic => TypeKind::Builtin(BuiltinFunction::Panic),
        Builtin::Print => TypeKind::Builtin(BuiltinFunction::Print),
        Builtin::Println => TypeKind::Builtin(BuiltinFunction::Println),
        Builtin::Real => TypeKind::Builtin(BuiltinFunction::Real),
        Builtin::Recover => TypeKind::Builtin(BuiltinFunction::Recover),
    };

    Type::insert(db, kind)
}

impl std::fmt::Display for TypeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeKind::Type(_) => write!(f, "type"),
            TypeKind::Package(package) => write!(f, "{package:?}"),
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
