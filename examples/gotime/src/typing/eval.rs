use futures::{future::BoxFuture, FutureExt};

use crate::{
    diagnostic::bug,
    error,
    index_map::IndexMap,
    naming::{self, DeclId, DeclPath, GlobalSymbol, Symbol},
    span::Span,
    syntax::{self, ExprId, Node, NodeId},
    typing::{ConstantKind, TypeKind},
    Result,
};

use super::ConstValue;

pub struct EvalContext<'a> {
    pub decl: DeclId,
    pub path: DeclPath,
    pub db: &'a dyn crate::Db,
    pub ast: &'a syntax::File,
    pub nodes: &'a syntax::NodeView,
    pub references: &'a IndexMap<NodeId, Symbol>,
    pub types: &'a super::TypingInfo,
}

impl<'a> EvalContext<'a> {
    pub async fn new(db: &'a dyn crate::Db, decl: DeclId) -> Result<EvalContext<'a>> {
        let path = decl.path(db).await?;
        let ast = syntax::parse_file(db, path.source).await.as_ref()?;
        let nodes = &ast.declarations[path.index].nodes;
        let references = naming::decl_symbols(db, decl).await.as_ref()?;
        let types = super::type_check_body(db, decl).await.as_ref()?;

        Ok(Self {
            decl,
            path,
            db,
            ast,
            nodes,
            references,
            types,
        })
    }

    fn eval_boxed(&mut self, expr: ExprId) -> BoxFuture<Result<ConstValue>> {
        self.eval(expr).boxed()
    }

    pub async fn eval(&mut self, expr: ExprId) -> Result<ConstValue> {
        match self.nodes.kind(expr) {
            Node::Name(name) | Node::Selector(_, syntax::Identifier { text: name, .. }) => {
                let Some(&symbol) = self.references.get(&expr.node) else {
                    let name = name.map(|t| t.get(self.db)).unwrap_or("_");
                    return Err(error!("undefined reference to `{name}`")
                        .label(self.node_span(expr), ""));
                };
                match symbol {
                    naming::Symbol::Local(local) => {
                        if let Some(value) = self.types.constants.get(&local) {
                            return Ok(value.clone());
                        }
                        Err(error!("cannot evaluate variable at compile-time")
                            .label(self.node_span(expr), ""))
                    }
                    naming::Symbol::Global(global) => match global {
                        GlobalSymbol::Package(_) => unreachable!("not a value"),
                        GlobalSymbol::Builtin(builtin) => match builtin {
                            naming::Builtin::Iota => Ok(ConstValue::number(self.path.sub.row)),
                            naming::Builtin::True => Ok(ConstValue::Bool(true)),
                            naming::Builtin::False => Ok(ConstValue::Bool(false)),
                            _ => Err(error!("the value cannot be known at compile-time")
                                .label(self.node_span(expr), "")),
                        },
                        GlobalSymbol::Decl(decl) => super::const_value(self.db, decl).await,
                    },
                }
            }

            Node::String(text) => {
                let bytes: &[u8] = self.nodes.string(text);
                Ok(ConstValue::String(crate::util::bstr_arc(bytes.into())))
            }

            Node::IntegerSmall(value) => Ok(ConstValue::number(value)),
            Node::Rune(rune) => Ok(ConstValue::number(rune as u32)),

            Node::FloatSmall(value) => Ok(ConstValue::number(value.get())),

            Node::Unary(op, expr) => {
                let value = self.eval_boxed(expr).await?;
                match op {
                    syntax::UnaryOperator::Plus => Ok(value),
                    syntax::UnaryOperator::Minus => match value {
                        ConstValue::Number(value) => Ok(ConstValue::number(-&*value)),
                        _ => unreachable!("cannot negate `{value:?}`"),
                    },
                    syntax::UnaryOperator::Not => Ok(ConstValue::Bool(!value.bool())),
                    syntax::UnaryOperator::Xor => {
                        let typ = self.types.nodes[&expr.node].value();
                        let kind = typ.lookup(self.db);
                        let int = self.as_integer(&value, || self.node_span(expr))?;
                        if kind.is_signed() {
                            Ok(ConstValue::number((-1) ^ int))
                        } else {
                            let bits = kind.bits().unwrap();
                            let mask = (1u128 << bits) - 1;
                            Ok(ConstValue::number(mask ^ int))
                        }
                    }
                    syntax::UnaryOperator::Deref
                    | syntax::UnaryOperator::Ref
                    | syntax::UnaryOperator::Recv => Err(error!("cannot evaluate expression")
                        .label(self.node_span(expr), "not a constant known at compile-time")),
                }
            }

            Node::Binary(exprs) => {
                use syntax::BinaryOperator as BinOp;

                let interleaved = self.nodes.indirect(exprs);
                let mut lhs = self.eval_boxed(interleaved[0]).await?;

                let start = interleaved[0];
                let mut end = interleaved[0];

                for pair in interleaved[1..].chunks_exact(2) {
                    let Node::BinaryOp(op) = self.nodes.kind(pair[0]) else { unreachable!() };
                    let rhs = self.eval_boxed(pair[1]).await?;

                    lhs = match op {
                        BinOp::LogicalOr => ConstValue::Bool(lhs.bool() || rhs.bool()),
                        BinOp::LogicalAnd => ConstValue::Bool(lhs.bool() && rhs.bool()),
                        BinOp::Equal => ConstValue::Bool(lhs == rhs),
                        BinOp::NotEqual => ConstValue::Bool(lhs != rhs),
                        BinOp::Less => ConstValue::Bool(lhs.try_order(&rhs).is_lt()),
                        BinOp::LessEqual => ConstValue::Bool(lhs.try_order(&rhs).is_le()),
                        BinOp::Greater => ConstValue::Bool(lhs.try_order(&rhs).is_gt()),
                        BinOp::GreaterEqual => ConstValue::Bool(lhs.try_order(&rhs).is_ge()),
                        BinOp::Add => match (&lhs, &rhs) {
                            (ConstValue::Number(lhs), ConstValue::Number(rhs)) => {
                                ConstValue::number(&**lhs + &**rhs)
                            }

                            (ConstValue::String(lhs), ConstValue::String(rhs)) => {
                                let mut buffer = Vec::with_capacity(lhs.len() + rhs.len());
                                buffer.extend_from_slice(lhs);
                                buffer.extend_from_slice(rhs);
                                ConstValue::String(crate::util::bstr_arc(buffer.into()))
                            }
                            _ => unreachable!("cannot add `{lhs}` and `{rhs}`"),
                        },
                        BinOp::Sub => match (&lhs, &rhs) {
                            (ConstValue::Number(lhs), ConstValue::Number(rhs)) => {
                                ConstValue::number(&**lhs - &**rhs)
                            }
                            _ => unreachable!("cannot subtract `{lhs}` and `{rhs}`"),
                        },
                        BinOp::Mul => match (&lhs, &rhs) {
                            (ConstValue::Number(lhs), ConstValue::Number(rhs)) => {
                                ConstValue::number(&**lhs * &**rhs)
                            }
                            _ => unreachable!("cannot multiply `{lhs}` and `{rhs}`"),
                        },
                        BinOp::Div => match (&lhs, &rhs) {
                            (ConstValue::Number(lhs), ConstValue::Number(rhs)) => {
                                if rhs.real().is_zero() && rhs.imag().is_zero() {
                                    return Err(error!("divison by zero")
                                        .label(self.node_span(pair[0]), "in this division")
                                        .label(self.node_span(pair[1]), "this was zero"));
                                }
                                let result = ConstValue::number(&**lhs / &**rhs);

                                if self.types.nodes[&pair[1].node]
                                    .inner()
                                    .lookup(self.db)
                                    .is_integer()
                                {
                                    let ConstValue::Number(value) = result else { unreachable!() };
                                    ConstValue::number(value.real().trunc_ref())
                                } else {
                                    result
                                }
                            }
                            _ => unreachable!("cannot divide `{lhs}` and `{rhs}`"),
                        },
                        BinOp::Rem => {
                            let lhs = self.as_integer(&lhs, || self.join_span(start, end))?;
                            let rhs = self.as_integer(&rhs, || self.node_span(pair[1]))?;
                            if rhs == 0 {
                                return Err(error!("divison by zero")
                                    .label(self.node_span(pair[0]), "in this remainder")
                                    .label(self.node_span(pair[1]), "this was zero"));
                            }
                            ConstValue::number(lhs % rhs)
                        }
                        BinOp::ShiftLeft => {
                            let lhs = self.as_integer(&lhs, || self.join_span(start, end))?;
                            let rhs = self.as_integer(&rhs, || self.node_span(pair[1]))?;
                            if rhs < 0 || rhs > (1 << 10) {
                                return Err(error!("invalid shift amount")
                                    .label(self.node_span(pair[0]), "in this left shift")
                                    .label(self.node_span(pair[1]), format!("this was {rhs}")));
                            }
                            let rhs = rhs.to_u32().unwrap();
                            ConstValue::number(lhs << rhs)
                        }
                        BinOp::ShiftRight => {
                            let lhs = self.as_integer(&lhs, || self.join_span(start, end))?;
                            let rhs = self.as_integer(&rhs, || self.node_span(pair[1]))?;
                            if rhs < 0 || rhs > (1 << 10) {
                                return Err(error!("invalid shift amount")
                                    .label(self.node_span(pair[0]), "in this right shift")
                                    .label(self.node_span(pair[1]), format!("this was {rhs}")));
                            }
                            let rhs = rhs.to_u32().unwrap();
                            ConstValue::number(lhs >> rhs)
                        }

                        BinOp::BitOr => {
                            let lhs = self.as_integer(&lhs, || self.join_span(start, end))?;
                            let rhs = self.as_integer(&rhs, || self.node_span(pair[1]))?;
                            ConstValue::number(lhs | rhs)
                        }
                        BinOp::BitXor => {
                            let lhs = self.as_integer(&lhs, || self.join_span(start, end))?;
                            let rhs = self.as_integer(&rhs, || self.node_span(pair[1]))?;
                            ConstValue::number(lhs ^ rhs)
                        }
                        BinOp::BitAnd => {
                            let lhs = self.as_integer(&lhs, || self.join_span(start, end))?;
                            let rhs = self.as_integer(&rhs, || self.node_span(pair[1]))?;
                            ConstValue::number(lhs & rhs)
                        }
                        BinOp::BitNand => {
                            let lhs = self.as_integer(&lhs, || self.join_span(start, end))?;
                            let rhs = self.as_integer(&rhs, || self.node_span(pair[1]))?;
                            ConstValue::number(lhs & !rhs)
                        }
                    };

                    end = pair[1];
                }

                Ok(lhs)
            }

            Node::Call(target, args, None) => {
                enum ConstFunc {
                    IntCast,
                    Sizeof,
                    Offsetof,
                    Len,
                    Cap,
                    Real,
                    Imag,
                    Complex,
                }

                let func = match self.nodes.kind(target) {
                    Node::Name(_) | Node::Selector(_, _) => match self.references.get(&target.node)
                    {
                        Some(Symbol::Global(GlobalSymbol::Builtin(builtin))) => match builtin {
                            naming::Builtin::Complex => Some(ConstFunc::Complex),
                            naming::Builtin::Imag => Some(ConstFunc::Imag),
                            naming::Builtin::Real => Some(ConstFunc::Real),
                            naming::Builtin::Len => Some(ConstFunc::Len),
                            naming::Builtin::Cap => Some(ConstFunc::Cap),
                            naming::Builtin::Int
                            | naming::Builtin::Int8
                            | naming::Builtin::Int16
                            | naming::Builtin::Int32
                            | naming::Builtin::Int64
                            | naming::Builtin::Uint
                            | naming::Builtin::Uint8
                            | naming::Builtin::Uint16
                            | naming::Builtin::Uint32
                            | naming::Builtin::Uint64
                            | naming::Builtin::Uintptr => Some(ConstFunc::IntCast),
                            _ => None,
                        },
                        Some(Symbol::Global(GlobalSymbol::Decl(decl))) => {
                            if super::is_unsafe_decl(self.db, *decl, "Sizeof") {
                                Some(ConstFunc::Sizeof)
                            } else if super::is_unsafe_decl(self.db, *decl, "Offsetof") {
                                Some(ConstFunc::Offsetof)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    },
                    _ => None,
                };

                let Some(func) = func else {
                    return Err(error!("function cannot be evaluated at compile-time")
                        .label(self.node_span(expr), ""))
                };

                let exprs = self.nodes.indirect(args);

                let value = match func {
                    ConstFunc::IntCast => match self.eval_boxed(exprs[0]).await? {
                        ConstValue::Number(value) if value.imag().is_zero() => {
                            ConstValue::number(value.real().trunc_ref())
                        }
                        value => {
                            return Err(error!("cannot perform cast").label(
                                self.node_span(exprs[0]),
                                format!("cannot cast to integer: `{value}`"),
                            ))
                        }
                    },

                    // TODO: actually compute the memory layout of types
                    ConstFunc::Sizeof => ConstValue::number(8),
                    ConstFunc::Offsetof => ConstValue::number(0),

                    ConstFunc::Len => {
                        let inferred = self.types.nodes.get(&exprs[0].node).ok_or_else(|| {
                            bug!("type is not known").label(self.node_span(exprs[0]), "")
                        })?;
                        let typ = inferred.value();

                        let len = match typ.lookup(self.db) {
                            &TypeKind::Array(len, _) => Some(len),
                            TypeKind::Pointer(inner) => match inner.lookup(self.db) {
                                &TypeKind::Array(len, _) => Some(len),
                                _ => None,
                            },
                            TypeKind::Untyped(ConstantKind::String) => {
                                match self.eval_boxed(exprs[0]).await? {
                                    ConstValue::String(string) => Some(string.len() as u64),
                                    _ => None,
                                }
                            }
                            _ => None,
                        };

                        match len {
                            Some(len) => ConstValue::number(len),
                            None => {
                                return Err(error!("length not known at compile-time")
                                    .label(self.node_span(exprs[0]), format!("found `{typ}`")))
                            }
                        }
                    }

                    ConstFunc::Cap => {
                        let inferred = self.types.nodes.get(&exprs[0].node).ok_or_else(|| {
                            bug!("type is not known").label(self.node_span(exprs[0]), "")
                        })?;
                        let typ = inferred.value();

                        let len = match typ.lookup(self.db) {
                            &TypeKind::Array(len, _) => Some(len),
                            TypeKind::Pointer(inner) => match inner.lookup(self.db) {
                                &TypeKind::Array(len, _) => Some(len),
                                _ => None,
                            },
                            _ => None,
                        };

                        match len {
                            Some(len) => ConstValue::number(len),
                            None => {
                                return Err(error!("length not known at compile-time")
                                    .label(self.node_span(exprs[0]), format!("found `{typ}`")))
                            }
                        }
                    }

                    ConstFunc::Real => todo!(),
                    ConstFunc::Imag => todo!(),
                    ConstFunc::Complex => todo!(),
                };

                Ok(value)
            }

            _ => Err(error!("cannot evaluate expression")
                .label(self.node_span(expr), "not a constant known at compile-time")),
        }
    }

    fn as_integer(&self, value: &ConstValue, span: impl FnOnce() -> Span) -> Result<rug::Integer> {
        value.as_integer().ok_or_else(|| {
            error!("cannot represent as an integer").label(span(), format!("this was {}", value))
        })
    }

    fn node_span(&self, node: impl Into<NodeId>) -> crate::span::Span {
        self.ast.node_span(self.path.index, node)
    }

    fn join_span(&self, start: impl Into<NodeId>, end: impl Into<NodeId>) -> Span {
        self.node_span(start).join(self.node_span(end))
    }
}
