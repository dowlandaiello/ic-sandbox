use super::{
    ast_lafont::{Expr, Ident, Net, PortGrouping, PortKind, Type},
    parser_lafont::Spanned,
};
use chumsky::error::Simple;
use std::collections::{BTreeMap, BTreeSet, HashSet};

#[derive(Default)]
pub struct TypedProgram {
    types: BTreeSet<Type>,
    symbol_declarations_for: BTreeMap<Ident, Vec<PortKind>>,
    nets: HashSet<Net>,
}

impl TypedProgram {
    pub fn has_type(&self, t: &Type) -> bool {
        self.types.contains(t)
    }

    pub fn has_symbol(&self, s: &Ident) -> bool {
        self.symbol_declarations_for.contains_key(s)
    }

    pub fn has_net(&self, n: &Net) -> bool {
        self.nets.contains(n)
    }

    pub fn get_declaration_for(&self, symbol: &Ident) -> Option<&[PortKind]> {
        self.symbol_declarations_for
            .get(symbol)
            .map(|dec| dec.as_slice())
    }

    pub fn push_type(&mut self, t: Type) {
        self.types.insert(t);
    }
}

pub fn parse_typed_program(statements: Vec<Spanned<Expr>>) -> (TypedProgram, Vec<Simple<Expr>>) {
    statements.into_iter().fold(
        (Default::default(), Default::default()),
        |mut acc: (TypedProgram, Vec<Simple<Expr>>), x| {
            // Guard conflicting identifiers
            // Cannot have the same name, symbol, or rule twice
            match &x {
                Spanned(Expr::Net(n), span) => {
                    if acc.0.has_net(&n) {
                        acc.1.push(Simple::custom(span.clone(), "duplicate net"));

                        return acc;
                    }
                }
                Spanned(Expr::Symbol { ident: s, .. }, span) => {
                    if acc.0.has_symbol(&s) {
                        acc.1.push(Simple::custom(
                            span.clone(),
                            format!("duplicate symbol: {}", s),
                        ));

                        return acc;
                    }
                }
                Spanned(Expr::TypeDec(ty), span) => {
                    if acc.0.has_type(&ty) {
                        acc.1.push(Simple::custom(
                            span.clone(),
                            format!("duplicate type: {}", ty),
                        ));

                        return acc;
                    }
                }
            }

            // Guard types mention existing symbols
            match &x {
                Spanned(Expr::Symbol { ident, ports }, span) => {
                    if let Some(unknown_type) = ports
                        .iter()
                        .filter_map(|port| match &port {
                            PortGrouping::Singleton(PortKind::Input(ty))
                            | PortGrouping::Singleton(PortKind::Output(ty)) => {
                                if !acc.0.has_type(ty) {
                                    Some(ty)
                                } else {
                                    None
                                }
                            }
                            PortGrouping::Partition(ps) => ps
                                .iter()
                                .filter_map(|p| match p {
                                    PortKind::Input(ty) | PortKind::Output(ty) => {
                                        if !acc.0.has_type(ty) {
                                            Some(ty)
                                        } else {
                                            None
                                        }
                                    }
                                })
                                .next(),
                        })
                        .next()
                    {
                        acc.1.push(Simple::custom(
                            span.clone(),
                            format!("symbol {} references unknown type {}", ident, unknown_type),
                        ));
                    }
                }
                _ => {}
            }

            acc
        },
    )
}
