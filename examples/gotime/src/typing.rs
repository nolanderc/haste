mod context;
mod eval;

use std::sync::Arc;

use bstr::BStr;
use futures::future::BoxFuture;
use smallvec::SmallVec;

use crate::{
    common::Text,
    error,
    index_map::IndexMap,
    naming::{self, AssignmentExpr, Builtin, DeclId, PackageId},
    syntax::{self, NodeId},
    HashMap, HashSet, Result,
};

use self::{context::TypingContext, eval::EvalContext};

#[haste::storage]
pub struct Storage(
    Type,
    decl_signature,
    type_check_body,
    underlying_type_for_decl,
    inner_type_for_decl,
    const_value,
    recursive_members,
    selection_members,
    resolve_selector,
    method_signature,
    comparable,
);

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

    pub fn is_signed(self) -> bool {
        self.contains(Self::SIGNED)
    }

    pub fn is_numeric(self) -> bool {
        self.intersects(Self::NUMERIC)
    }

    pub fn is_nillable(self) -> bool {
        self.intersects(Self::NILLABLE)
    }

    pub fn is_string(self) -> bool {
        self.contains(Self::STRING)
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

            TypeKind::String => TypeClass::STRING | nillable | ordered,

            TypeKind::Pointer(_) => nillable | comparable,
            TypeKind::Slice(_) => nillable,
            TypeKind::Map(_, _) => nillable,
            TypeKind::Channel(_, _) => nillable | comparable,
            TypeKind::Function(_) => nillable,

            TypeKind::Struct(_) => TypeClass::empty(),
            TypeKind::Array(_, _) => TypeClass::empty(),

            TypeKind::Interface(_) => nillable | comparable,

            TypeKind::Declared(_) => TypeClass::empty(),
        }
    }

    pub async fn underlying_class(&self, db: &dyn crate::Db) -> Result<TypeClass> {
        if let Self::Declared(decl) = self {
            Ok(underlying_type_for_decl(db, *decl)
                .await?
                .lookup(db)
                .class())
        } else {
            Ok(self.class())
        }
    }

    pub fn is_numeric(&self) -> bool {
        self.class().intersects(TypeClass::NUMERIC)
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

    pub fn is_declared(&self) -> bool {
        matches!(self, Self::Declared(_))
    }

    pub fn is_nil(&self) -> bool {
        matches!(self, TypeKind::Untyped(ConstantKind::Nil))
    }

    pub async fn is_nillable(&self, db: &dyn crate::Db) -> Result<bool> {
        Ok(self
            .underlying_class(db)
            .await?
            .contains(TypeClass::NILLABLE))
    }

    pub fn is_ordered(&self) -> bool {
        self.class().contains(TypeClass::TRIVIALLY_ORDERED)
    }

    pub fn is_untyped(&self) -> bool {
        self.class().contains(TypeClass::UNTYPED)
    }

    pub async fn length(&self, db: &dyn crate::Db) -> Result<Option<Type>> {
        let mut kind = self;

        if let &TypeKind::Pointer(inner) = kind {
            let inner_core = underlying_type(db, inner).await?;
            let inner_kind = inner_core.lookup(db);
            if let TypeKind::Array(_, _) = inner_kind {
                kind = inner_kind;
            }
        }

        Ok(Some(match kind {
            Self::Array(_, _) => Self::Untyped(ConstantKind::Integer).insert(db),

            Self::Untyped(ConstantKind::String)
            | Self::String
            | Self::Slice(_)
            | Self::Map(_, _)
            | Self::Channel(_, _) => Self::Int.insert(db),

            _ => return Ok(None),
        }))
    }

    pub async fn capacity(&self, db: &dyn crate::Db) -> Result<Option<Type>> {
        let mut kind = self;

        if let &TypeKind::Pointer(inner) = kind {
            let inner_core = underlying_type(db, inner).await?;
            let inner_kind = inner_core.lookup(db);
            if let TypeKind::Array(_, _) = inner_kind {
                kind = inner_kind;
            }
        }

        Ok(Some(match kind {
            Self::Array(_, _) => Self::Untyped(ConstantKind::Integer).insert(db),
            Self::Slice(_) | Self::Channel(_, _) => Self::Int.insert(db),
            _ => return Ok(None),
        }))
    }

    pub fn bits(&self) -> Option<u32> {
        match self {
            TypeKind::Int => Some(64),
            TypeKind::Int8 => Some(8),
            TypeKind::Int16 => Some(16),
            TypeKind::Int32 => Some(32),
            TypeKind::Int64 => Some(64),
            TypeKind::Uint => Some(64),
            TypeKind::Uint8 => Some(8),
            TypeKind::Uint16 => Some(16),
            TypeKind::Uint32 => Some(32),
            TypeKind::Uint64 => Some(64),
            TypeKind::Uintptr => Some(64),
            TypeKind::Float32 => Some(32),
            TypeKind::Float64 => Some(64),
            TypeKind::Complex64 => Some(64),
            TypeKind::Complex128 => Some(128),
            _ => None,
        }
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

    pub fn structural_eq_boxed(self, db: &dyn crate::Db, other: Type) -> BoxFuture<Result<bool>> {
        use futures::FutureExt;
        self.structurally_equivalent(db, other).boxed()
    }

    pub async fn structurally_equivalent(self, db: &dyn crate::Db, other: Type) -> Result<bool> {
        if self == other {
            return Ok(true);
        }

        let mut self_kind = self.lookup(db);
        let mut other_kind = self.lookup(db);

        if let TypeKind::Declared(decl) = self_kind {
            self_kind = underlying_type_for_decl(db, *decl).await?.lookup(db);
        }
        if let TypeKind::Declared(decl) = other_kind {
            other_kind = underlying_type_for_decl(db, *decl).await?.lookup(db);
        }

        match (self_kind, other_kind) {
            (TypeKind::Struct(a), TypeKind::Struct(b)) => {
                if a.fields.len() != b.fields.len() {
                    return Ok(false);
                }

                for (a, b) in a.fields.iter().zip(b.fields.iter()) {
                    if !(a.name == b.name && a.typ.structural_eq_boxed(db, b.typ).await?) {
                        return Ok(false);
                    }
                }

                Ok(true)
            }

            (TypeKind::Pointer(a), TypeKind::Pointer(b)) => a.structural_eq_boxed(db, *b).await,
            (TypeKind::Slice(a), TypeKind::Slice(b)) => a.structural_eq_boxed(db, *b).await,
            (TypeKind::Map(a_key, a_value), TypeKind::Map(b_key, b_value)) => {
                Ok(a_key.structural_eq_boxed(db, *b_key).await?
                    && a_value.structural_eq_boxed(db, *b_value).await?)
            }
            (TypeKind::Channel(a_kind, a), TypeKind::Channel(b_kind, b)) => {
                Ok(a_kind == b_kind && a.structural_eq_boxed(db, *b).await?)
            }
            (TypeKind::Array(a_len, a), TypeKind::Array(b_len, b)) => {
                Ok(a_len == b_len && a.structural_eq_boxed(db, *b).await?)
            }

            _ => Ok(false),
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
    variadic: bool,
}

impl FunctionType {
    pub fn inputs(&self) -> impl Iterator<Item = Type> + '_ {
        let mut i = 0;
        std::iter::from_fn(move || {
            if i < self.inputs {
                let typ = self.types[i];
                i += 1;
                return Some(typ);
            }

            if self.variadic {
                Some(self.types[self.inputs - 1])
            } else {
                None
            }
        })
    }

    pub fn outputs(&self) -> &[Type] {
        &self.types[self.inputs..]
    }

    pub fn required_inputs(&self) -> usize {
        self.inputs - self.variadic as usize
    }

    fn enough_arguments(&self, len: usize) -> bool {
        len >= self.required_inputs()
    }

    fn without_receiver(&self) -> FunctionType {
        FunctionType {
            types: self.types[1..].into(),
            inputs: self.inputs - 1,
            variadic: self.variadic,
        }
    }

    fn with_receiever(&self, typ: Type) -> FunctionType {
        let mut types = TypeList::with_capacity(self.types.len() + 1);
        types.push(typ);
        types.extend_from_slice(&self.types);
        FunctionType {
            types,
            inputs: self.inputs + 1,
            variadic: self.variadic,
        }
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

impl StructType {
    pub fn get_field(&self, name: Text) -> Option<&Field> {
        self.fields.iter().find(|field| field.name == Some(name))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InterfaceType {
    /// List of methods.
    Methods(Box<[InterfaceMethod]>),
    /// The error interface.
    Error,
}

impl InterfaceType {
    fn is_empty(&self) -> bool {
        matches!(self, Self::Methods(methods) if methods.is_empty())
    }

    fn error_method(db: &dyn crate::Db) -> InterfaceMethod {
        InterfaceMethod {
            name: Text::new(db, "Error"),
            signature: FunctionType {
                types: smallvec::smallvec![TypeKind::String.insert(db)],
                inputs: 0,
                variadic: false,
            },
        }
    }

    fn methods<'a>(
        &'a self,
        db: &dyn crate::Db,
        buffer: &'a mut Option<InterfaceMethod>,
    ) -> impl Iterator<Item = &'a InterfaceMethod> {
        let methods: &[_] = match self {
            InterfaceType::Methods(methods) => methods,
            InterfaceType::Error => {
                *buffer = Some(Self::error_method(db));
                std::slice::from_ref(buffer.as_ref().unwrap())
            }
        };
        methods.iter()
    }
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
            TypeKind::Struct(strukt) => strukt.fmt(f),
            TypeKind::Interface(interface) => interface.fmt(f),
            TypeKind::Declared(decl) => decl.fmt(f),
        }
    }
}

impl std::fmt::Display for FunctionType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_with_name(f, None)
    }
}

impl FunctionType {
    fn fmt_with_name(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        name: Option<Text>,
    ) -> std::fmt::Result {
        if let Some(name) = name {
            write!(f, "func {name}(")?;
        } else {
            write!(f, "func(")?;
        }

        for i in 0..self.inputs {
            if i != 0 {
                write!(f, ", ")?;
            }
            if self.variadic && i == self.inputs - 1 {
                write!(f, "...")?;
            }
            write!(f, "{}", self.types[i])?;
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

impl std::fmt::Display for StructType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "struct {{")?;

        for (i, field) in self.fields.iter().enumerate() {
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

        if self.fields.is_empty() {
            write!(f, "}}")
        } else {
            write!(f, " }}")
        }
    }
}

impl std::fmt::Display for InterfaceType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Error => write!(f, "error"),
            Self::Methods(methods) => {
                if methods.is_empty() {
                    return write!(f, "interface{{}}");
                }

                write!(f, "interface {{")?;

                for (i, method) in methods.iter().enumerate() {
                    if i == 0 {
                        write!(f, " ")?;
                    } else {
                        write!(f, "; ")?;
                    }

                    method.signature.fmt_with_name(f, Some(method.name))?;
                }

                write!(f, " }}")
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Signature {
    Package(PackageId),
    Type(Type),
    Value(Type),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InferredType {
    /// The expression is a value.
    Value(Type),
    /// The expression is a type.
    Type(Type),
}

impl InferredType {
    pub fn value(self) -> Type {
        match self {
            InferredType::Value(typ) => typ,
            InferredType::Type(_) => unreachable!("expected a value but found a type"),
        }
    }

    fn inner(self) -> Type {
        match self {
            Self::Value(typ) | Self::Type(typ) => typ,
        }
    }
}

/// Get the type of the given symbol
pub async fn signature(db: &dyn crate::Db, symbol: naming::GlobalSymbol) -> Result<Signature> {
    match symbol {
        naming::GlobalSymbol::Package(package) => Ok(Signature::Package(package)),
        naming::GlobalSymbol::Builtin(builtin) => Ok(builtin_signature(db, builtin)),
        naming::GlobalSymbol::Decl(decl) => decl_signature(db, decl).await,
    }
}

#[haste::query]
#[clone]
#[lookup(haste::query_cache::TrackedStrategy)]
pub async fn decl_signature(db: &dyn crate::Db, decl: DeclId) -> Result<Signature> {
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

        naming::SingleDecl::ConstDecl(_, _, expr) => {
            let typ = match ctx.try_infer_expr_no_check(expr).await? {
                Some(typ) => typ,
                None => {
                    let typing = type_check_body(db, decl).await.as_ref()?;
                    typing.nodes[&expr.node].value()
                }
            };
            Ok(Signature::Value(typ))
        }

        naming::SingleDecl::VarDecl(_, _, Some(AssignmentExpr::Single(expr))) => {
            let typ = match ctx.try_infer_expr_no_check(expr).await? {
                Some(typ) => typ,
                None => {
                    let typing = type_check_body(db, decl).await.as_ref()?;
                    typing.nodes[&expr.node].value()
                }
            };

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
        Builtin::Error => make_type(TypeKind::Interface(InterfaceType::Error)),
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
    nodes: IndexMap<NodeId, InferredType>,
    /// The type of local variables.
    locals: IndexMap<naming::Local, InferredType>,
    /// Value of all constants in the declaration.
    constants: IndexMap<naming::Local, ConstValue>,

    redeclarations: IndexMap<naming::Local, naming::Local>,
}

/// Type-check the entire symbol, returning the types of all applicable syntax nodes (types and
/// expressions).
#[haste::query]
#[lookup(haste::query_cache::TrackedStrategy)]
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

            ctx.types
                .nodes
                .insert(expr.node, InferredType::Value(found_type));

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

async fn underlying_type(db: &dyn crate::Db, typ: Type) -> Result<Type> {
    match typ.lookup(db) {
        &TypeKind::Declared(decl) => underlying_type_for_decl(db, decl).await,
        _ => Ok(typ),
    }
}

#[haste::query]
#[clone]
#[lookup(haste::query_cache::TrackedStrategy)]
async fn underlying_type_for_decl(db: &dyn crate::Db, decl: DeclId) -> Result<Type> {
    let inner = inner_type_for_decl(db, decl).await?;
    underlying_type(db, inner).await
}

#[haste::query]
#[clone]
#[lookup(haste::query_cache::TrackedStrategy)]
async fn inner_type_for_decl(db: &dyn crate::Db, decl: DeclId) -> Result<Type> {
    let mut ctx = TypingContext::new(db, decl).await?;
    let path = ctx.path;

    let declaration = &ctx.ast.declarations[path.index];

    match path.sub.lookup_in(declaration) {
        naming::SingleDecl::TypeDef(spec) | naming::SingleDecl::TypeAlias(spec) => {
            ctx.resolve_precise(spec.inner).await
        }

        _ => Err(error!("expected a type, but found a value")
            .label(path.span_in_ast(ctx.ast), "defined here")),
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConstValue {
    Bool(bool),
    Number(Arc<rug::Complex>),
    String(Arc<BStr>),
}

impl Eq for ConstValue {}

impl std::hash::Hash for ConstValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            ConstValue::Bool(bool) => bool.hash(state),
            ConstValue::Number(number) => number.as_ord().hash(state),
            ConstValue::String(string) => string.hash(state),
        }
    }
}

impl std::fmt::Display for ConstValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstValue::Bool(value) => value.fmt(f),
            ConstValue::Number(value) => value.fmt(f),
            ConstValue::String(value) => write!(f, "{:?}", value),
        }
    }
}

impl ConstValue {
    fn new_complex() -> rug::Complex {
        rug::Complex::new(512)
    }

    pub fn number<T>(value: T) -> Self
    where
        rug::Complex: rug::Assign<T>,
    {
        let mut x = Self::new_complex();
        rug::Assign::assign(&mut x, value);
        Self::Number(Arc::new(x))
    }

    fn bool(&self) -> bool {
        match self {
            ConstValue::Bool(value) => *value,
            _ => unreachable!("expected a boolean but found `{self}`"),
        }
    }

    fn as_integer(&self) -> Option<rug::Integer> {
        match self {
            ConstValue::Number(value) => {
                if value.imag().is_zero() && value.real().is_integer() {
                    value.real().to_integer()
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn try_order(&self, other: &ConstValue) -> std::cmp::Ordering {
        match (self, other) {
            (ConstValue::Number(lhs), ConstValue::Number(rhs)) => lhs.as_ord().cmp(rhs.as_ord()),
            (ConstValue::String(lhs), ConstValue::String(rhs)) => lhs.cmp(rhs),
            _ => unreachable!("cannot compare `{self}` and `{other}`"),
        }
    }
}

#[haste::query]
#[clone]
#[lookup(haste::query_cache::TrackedStrategy)]
async fn const_value(db: &dyn crate::Db, decl: DeclId) -> Result<ConstValue> {
    let mut ctx = EvalContext::new(db, decl).await?;
    let path = ctx.path;
    let declaration = &ctx.ast.declarations[path.index];
    match path.sub.lookup_in(declaration) {
        naming::SingleDecl::ConstDecl(_, _, expr) => ctx.eval(expr).await,

        naming::SingleDecl::TypeDef(_) | naming::SingleDecl::TypeAlias(_) => {
            Err(error!("cannot evaluate constant")
                .label(path.span_in_ast(ctx.ast), "this is a type, not a value"))
        }

        naming::SingleDecl::VarDecl(_, _, _) => Err(error!("cannot evaluate constant")
            .label(path.span_in_ast(ctx.ast), "variables are not constant")),

        naming::SingleDecl::Function(_) | naming::SingleDecl::Method(_) => {
            Err(error!("cannot evaluate constant").label(
                path.span_in_ast(ctx.ast),
                "cannot evaluate during compile-time",
            ))
        }
    }
}

fn is_unsafe_decl(db: &dyn crate::Db, decl: DeclId, name: &str) -> bool {
    use crate::import::FileSetData;
    use std::ffi::OsStr;

    if decl.name(db).base.get(db) != name || decl.package(db).name.get(db) != "unsafe" {
        return false;
    }

    let FileSetData::Directory(dir) = decl.package(db).files.lookup(db) else {return false};

    let Some(suffix) = dir.lookup(db).as_goroot() else { return false };

    if suffix != OsStr::new("src/unsafe") {
        return false;
    }

    true
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Selection {
    /// A struct field.
    Field(Type),
    /// A function type (without the reciever) denoting a defined method function or interface
    /// method.
    Method(Type),
}

type SelectionList = SmallVec<[Selection; 2]>;

#[haste::query]
#[clone]
async fn resolve_selector(db: &dyn crate::Db, typ: Type, name: Text) -> Result<Option<Selection>> {
    let mut inner = typ;

    while let TypeKind::Pointer(pointee) = inner.lookup(db) {
        inner = *pointee;
    }

    let members = recursive_members(db, inner).await.as_ref()?;
    let Some(selection) = members.get(&name) else { return Ok(None) };

    if selection.len() > 1 {
        return Err(error!(
            "ambiguous selection `{typ}.{name}`: multiple alternatives ({:?})",
            selection
        ));
    }

    Ok(selection.get(0).copied())
}

#[haste::query]
async fn recursive_members(db: &dyn crate::Db, typ: Type) -> Result<HashMap<Text, SelectionList>> {
    let mut selections = HashMap::<Text, SelectionList>::default();

    let mut curr_depth = TypeList::new();
    let mut next_depth = TypeList::new();

    let mut visited = HashSet::default();

    visited.insert(typ);
    curr_depth.push(typ);

    while !curr_depth.is_empty() {
        while let Some(mut curr) = curr_depth.pop() {
            if let TypeKind::Pointer(inner) = curr.lookup(db) {
                curr = *inner;
            }
            if let TypeKind::Declared(decl) = curr.lookup(db) {
                let inner = inner_type_for_decl(db, *decl).await?;
                if let TypeKind::Pointer(inner) = inner.lookup(db) {
                    curr_depth.push(*inner);
                }
            }

            let members = selection_members(db, curr).await.as_ref()?;
            for (&name, list) in members.selections.iter() {
                if selections.contains_key(&name) {
                    continue;
                }

                selections.entry(name).or_default().extend_from_slice(list);
            }

            for &embedded in members.embedded.iter() {
                if !visited.contains(&embedded) {
                    next_depth.push(embedded);
                }
            }
        }

        for next in next_depth.drain(..) {
            if visited.insert(next) {
                curr_depth.push(next);
            }
        }
    }

    Ok(selections)
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct SelectionMembers {
    selections: IndexMap<Text, SelectionList>,
    embedded: TypeList,
}

#[haste::query]
async fn selection_members(db: &dyn crate::Db, mut typ: Type) -> Result<SelectionMembers> {
    let mut selections = IndexMap::<Text, SelectionList>::new();
    let mut embedded = TypeList::new();

    let mut add_candidate = |name: Text, selection: Selection| {
        selections
            .get_or_insert_with(name, SelectionList::new)
            .push(selection);
    };

    if let &TypeKind::Declared(decl) = typ.lookup(db) {
        let methods = naming::method_set(db, decl).await?;

        let decl_data = decl.lookup(db);

        for method in methods.iter() {
            let method_decl = DeclId::new(db, decl_data.package, method);

            let decl_type = match decl_signature(db, method_decl).await? {
                Signature::Value(typ) => typ,
                _ => unreachable!("methods must be values"),
            };

            let TypeKind::Function(func) = decl_type.lookup(db) else {
                unreachable!("methods have function type")
            };

            let method_func = func.without_receiver();
            let method_type = TypeKind::Function(method_func).insert(db);
            add_candidate(method.base, Selection::Method(method_type));
        }

        typ = underlying_type_for_decl(db, decl).await?;
    }

    match typ.lookup(db) {
        TypeKind::Struct(strukt) => {
            for field in strukt.fields.iter() {
                let Some(name) = field.name else { continue };
                add_candidate(name, Selection::Field(field.typ));
                if field.embedded {
                    embedded.push(field.typ);
                }
            }
        }
        TypeKind::Interface(interface) => {
            let mut buffer = None;
            for method in interface.methods(db, &mut buffer) {
                let signature = TypeKind::Function(method.signature.clone()).insert(db);
                add_candidate(method.name, Selection::Method(signature));
            }
        }
        _ => {}
    }

    Ok(SelectionMembers {
        selections,
        embedded,
    })
}

pub enum InterfaceError {
    MissingMethod(Text),
    WrongSignature {
        method: Text,
        found: Type,
        expected: Type,
    },
}

impl std::fmt::Display for InterfaceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InterfaceError::MissingMethod(name) => write!(f, "missing method `{name}`"),
            InterfaceError::WrongSignature {
                method,
                found,
                expected,
            } => {
                write!(
                    f,
                    "expected a method `{method}` with signature `{expected}`, but found `{found}`"
                )
            }
        }
    }
}

async fn satisfies_interface(
    db: &dyn crate::Db,
    typ: Type,
    interface: &InterfaceType,
) -> Result<Result<(), InterfaceError>> {
    let mut buffer = None;
    for method in interface.methods(db, &mut buffer) {
        let Some(selection) = resolve_selector(db, typ, method.name).await? else {
            // missing method
            return Ok(Err(InterfaceError::MissingMethod(method.name)));
        };

        match selection {
            Selection::Field(_) => return Ok(Err(InterfaceError::MissingMethod(method.name))),
            Selection::Method(typ) => match typ.lookup(db) {
                TypeKind::Function(func) => {
                    if func != &method.signature {
                        return Ok(Err(InterfaceError::WrongSignature {
                            method: method.name,
                            found: typ,
                            expected: TypeKind::Function(method.signature.clone()).insert(db),
                        }));
                    }
                }
                _ => unreachable!("methods have function type"),
            },
        }
    }

    Ok(Ok(()))
}

#[haste::query]
async fn method_signature(
    db: &dyn crate::Db,
    typ: Type,
    name: Text,
) -> Result<Option<FunctionType>> {
    let core = if let &TypeKind::Declared(decl) = typ.lookup(db) {
        if let Some(method) = declared_method_signature(db, decl, name).await? {
            return Ok(Some(method));
        }

        underlying_type_for_decl(db, decl).await?
    } else {
        typ
    };

    if let TypeKind::Interface(interface) = core.lookup(db) {
        let mut buffer = None;
        for method in interface.methods(db, &mut buffer) {
            if method.name == name {
                return Ok(Some(method.signature.clone()));
            }
        }
    }

    Ok(None)
}

async fn declared_method_signature(
    db: &dyn crate::Db,
    decl: DeclId,
    name: Text,
) -> Result<Option<FunctionType>> {
    let methods = naming::method_set(db, decl).await?;
    let Some(method) = methods.get(name) else { return Ok(None) };

    let method_decl = DeclId::new(db, decl.package(db), method);

    let method_type = match decl_signature(db, method_decl).await? {
        Signature::Value(typ) => typ,
        _ => unreachable!("methods must be values"),
    };

    let TypeKind::Function(func) = method_type.lookup(db) else { unreachable!() };
    Ok(Some(func.without_receiver()))
}

#[haste::query]
#[clone]
async fn comparable(db: &dyn crate::Db, typ: Type) -> Result<bool> {
    let kind = typ.lookup(db);
    if kind.class().contains(TypeClass::TRIVIALLY_COMPARABLE) {
        return Ok(true);
    }

    match kind {
        TypeKind::Array(_, inner) => comparable(db, *inner).await,
        TypeKind::Struct(strukt) => {
            for field in strukt.fields.iter() {
                if !comparable(db, field.typ).await? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        TypeKind::Declared(decl) => {
            let core = underlying_type_for_decl(db, *decl).await?;
            comparable(db, core).await
        }
        _ => Ok(false),
    }
}

async fn ordered(db: &dyn crate::Db, typ: Type) -> Result<bool> {
    let core = underlying_type(db, typ).await?;
    let kind = core.lookup(db);
    Ok(kind.class().contains(TypeClass::TRIVIALLY_ORDERED))
}
