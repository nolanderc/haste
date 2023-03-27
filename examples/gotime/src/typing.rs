mod context;

use smallvec::SmallVec;

use crate::{
    common::Text,
    import::FileSet,
    naming::{self, Builtin, DeclId},
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

    UntypedInteger,
    Nil,

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionType {
    types: SmallVec<[Type; 4]>,
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
        naming::SingleDecl::VarDecl(_, _, _) => todo!(),
        naming::SingleDecl::ConstDecl(_, _, _) => todo!(),
        naming::SingleDecl::Function(_) => todo!(),
        naming::SingleDecl::Method(_) => todo!(),
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

        Builtin::Iota => TypeKind::UntypedInteger,

        Builtin::Nil => TypeKind::Nil,

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
