use super::{
    ast_lafont::{Agent, Expr, Ident, Net, Port, PortGrouping, PortKind, Type},
    parser_lafont::Spanned,
};
use chumsky::error::Simple;
use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};

#[derive(Default)]
pub struct TypedProgram {
    types: BTreeSet<Type>,
    symbol_declarations_for: BTreeMap<Ident, Vec<PortGrouping>>,
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

    pub fn get_declaration_for(&self, symbol: &Ident) -> Option<&[PortGrouping]> {
        self.symbol_declarations_for
            .get(symbol)
            .map(|dec| dec.as_slice())
    }

    pub fn push_type(&mut self, t: Type) {
        self.types.insert(t);
    }

    pub fn push_port_grouping(&mut self, ident: Ident, port: PortGrouping) {
        self.symbol_declarations_for
            .entry(ident)
            .or_default()
            .push(port);
    }

    pub fn push_port_kinds(&mut self, ident: Ident, ports: Vec<PortGrouping>) {
        self.symbol_declarations_for
            .entry(ident)
            .or_default()
            .extend(ports);
    }

    pub fn push_net(&mut self, net: Net) {
        self.nets.insert(net);
    }
}

pub fn parse_typed_program(
    statements: Vec<Spanned<Expr>>,
) -> (TypedProgram, Vec<Simple<Spanned<Expr>>>) {
    statements.into_iter().fold(
        (Default::default(), Default::default()),
        |mut acc: (TypedProgram, Vec<Simple<Spanned<Expr>>>), x| {
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

                    acc.0.push_type(ty.clone());
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

                        return acc;
                    }

                    acc.0.push_port_kinds(ident.clone(), ports.clone());
                }
                Spanned(Expr::Net(Net { lhs, rhs }), span) => {
                    let mut to_check: VecDeque<&Agent> = VecDeque::from_iter(
                        [lhs, rhs].map(|x| x.as_ref()).into_iter().filter_map(|x| x),
                    );

                    // All agent must have idents matching some symbol
                    while let Some(check_agent) = to_check.pop_front() {
                        if !acc.0.has_symbol(&check_agent.name) {
                            acc.1.push(Simple::custom(
                                span.clone(),
                                format!("agent references unknown symbol {}", check_agent.name),
                            ));

                            return acc;
                        }

                        // Check all agent ports, too
                        to_check.extend(check_agent.ports.iter().filter_map(|p| match p {
                            Port::Var(_) => None,
                            Port::Agent(ref a) => Some(a),
                        }));
                    }
                }
                _ => {}
            }

            // Guard all redex are joined by opposite polarity, same type ports
            match &x {
                Spanned(Expr::Net(Net { lhs, rhs }), span) => match lhs.as_ref().zip(rhs.as_ref()) {
                    Some((lhs, rhs)) => {
                        let ty_lhs = acc.0.get_declaration_for(&lhs.name);
                        let ty_rhs = acc.0.get_declaration_for(&rhs.name);

                        match (ty_lhs, ty_rhs) {
                            (Some(ty_lhs), Some(ty_rhs)) => {
				if let Some((port_lhs, port_rhs)) = ty_lhs.iter().zip(ty_rhs.iter()).next() {
				    match (port_lhs, port_rhs) {
					(PortGrouping::Singleton(PortKind::Input(ty)), PortGrouping::Singleton(PortKind::Output(ty2))) | (PortGrouping::Singleton(PortKind::Output(ty)), PortGrouping::Singleton(PortKind::Input(ty2))) => {
					    if ty != ty2 {
						acc.1.push(Simple::custom(
                                    span.clone(),
                                    format!(
                                        "agents {}, {} have primary ports with unmatched types; found {} and {}, which do not match",
                                        lhs.name, rhs.name, ty, ty2
                                    )));

					    return acc;
					    }

					    acc.0.push_net(Net { lhs: Some(lhs.clone()), rhs: Some(rhs.clone())});
					},
					_ => {
					    acc.1.push(Simple::custom(
                                    span.clone(),
                                    format!(
                                        "agents {}, {} do not have equally typed, complementary primary ports",
                                        lhs.name, rhs.name
                                    )));

					    return acc;
					}
				    }
				} else {
				    acc.1.push(Simple::custom(
                                    span.clone(),
                                    format!(
                                        "missing type primary port connection for agents {}, {}",
                                        lhs.name, rhs.name
                                    ),
                                ));

                                return acc;
				}
			    }
                            (None, None) => {
                                acc.1.push(Simple::custom(
                                    span.clone(),
                                    format!(
                                        "missing type declarations for agents {}, {}",
                                        lhs.name, rhs.name
                                    ),
                                ));

                                return acc;
                            }
                            (_, None) => {
                                acc.1.push(Simple::custom(
                                    span.clone(),
                                    format!("missing type declaration for agent {}", rhs.name),
                                ));

                                return acc;
                            }
                            (None, _) => {
                                acc.1.push(Simple::custom(
                                    span.clone(),
                                    format!("missing type declaration for agent {}", lhs.name),
                                ));

                                return acc;
                            }
                        }
                    }
                    None => {
                        acc.1.push(Simple::custom(
                            span.clone(),
                            String::from("unit rules are not allowed"),
                        ));

                        return acc;
                    }
                },
                _ => {}
            }

            acc
        },
    )
}

#[cfg(test)]
mod test {
    use super::{super::parser_lafont, *};
    use chumsky::{stream::Stream, Parser};

    #[test]
    fn test_duplicate_identifiers() {
        let program = "type xyz
type xyz
type xyz

symbol abc: xyz+
symbol abc: xyz+
";
        let lexed = parser_lafont::lexer().parse(program).unwrap();
        let parsed = parser_lafont::parser()
            .parse(Stream::from_iter(
                0..program.len(),
                lexed
                    .into_iter()
                    .flatten()
                    .map(|Spanned(v, s)| (Spanned(v, s.clone()), s)),
            ))
            .unwrap();

        let (_, error_reports) = parse_typed_program(parsed);

        assert_eq!(
            error_reports,
            vec![
                Simple::custom(14..17, "duplicate type: xyz"),
                Simple::custom(23..26, "duplicate type: xyz"),
                Simple::custom(52..55, "duplicate symbol: abc"),
            ]
        );
    }
}
