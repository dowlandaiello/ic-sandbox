use super::parser::{
    ast_lafont::{Agent, Expr, Net, Port, PortGrouping, PortKind, Type},
    parser_lafont::Spanned,
};
use chumsky::error::Simple;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Default, Clone)]
pub struct TypedProgram {
    pub types: BTreeSet<Type>,
    pub symbol_declarations_for: BTreeMap<Type, Vec<PortKind>>,
    pub nets: BTreeSet<Net>,
}

impl TypedProgram {
    /// Gets a reference to a port in the agent, if it exists,
    /// which is an output variable.
    pub fn terminal_ports_for<'a>(&'a self, a: &'a Agent) -> Vec<&'a Port> {
        let type_dec = if let Some(dec) = self.symbol_declarations_for.get(&a.name) {
            dec
        } else {
            return Default::default();
        };

        // Both the port on the parent agent
        // and the primary port on the child agent
        // must be outputs
        let output_children = type_dec
            .iter()
            .skip(1)
            .zip(a.ports.iter())
            .filter(|(port_ty, _)| {
                // Port must be an output port to an agent or var
                port_ty.as_output().is_some()
            });

        output_children
            .filter_map(|(port_ty, port)| {
                self.symbol_declarations_for
                    .get(&Type(port.name().0.clone()))
                    .map(|dec| (port_ty, port, dec))
            })
            .filter(
                |(_, port, name_ty): &(&PortKind, &Port, &Vec<PortKind>)| -> bool {
                    port.as_var().is_some() || {
                        name_ty
                            .iter()
                            .map(|port| port.as_output().is_some())
                            .next()
                            .is_some()
                    }
                },
            )
            .map(|(_, port, _)| port)
            .collect::<Vec<_>>()
    }

    pub fn has_type(&self, t: &Type) -> bool {
        self.types.contains(t)
    }

    pub fn has_symbol(&self, s: &Type) -> bool {
        self.symbol_declarations_for.contains_key(s)
    }

    pub fn has_net(&self, n: &Net) -> bool {
        self.nets.contains(n)
    }

    pub fn get_declaration_for(&self, symbol: &Type) -> Option<&[PortKind]> {
        self.symbol_declarations_for
            .get(symbol)
            .map(|dec| dec.as_slice())
    }

    pub fn push_type(&mut self, t: Type) {
        self.types.insert(t);
    }

    pub fn push_port_kind(&mut self, ident: Type, port: PortKind) {
        self.symbol_declarations_for
            .entry(ident)
            .or_default()
            .push(port);
    }

    pub fn push_port_kinds(&mut self, ident: Type, ports: Vec<PortKind>) {
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
                            PortGrouping::Partition(_) => None
                        })
                        .next()
                    {
                        acc.1.push(Simple::custom(
                            span.clone(),
                            format!("symbol {} references unknown type {}", ident, unknown_type),
                        ));

                        return acc;
                    }

                    acc.0.push_port_kinds(ident.clone(), ports.iter().filter_map(|p| p.as_singleton()).cloned().collect());
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
					(PortKind::Input(ty), PortKind::Output(ty2)) | (PortKind::Output(ty), PortKind::Input(ty2)) => {
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
    use super::*;
    use crate::parser::parser_lafont;
    use chumsky::{stream::Stream, Parser};

    #[test]
    fn test_poorly_typed_mismatch() {
        let program = "type atom
type bruh

# This cannot compile, since atom is not opposite polarity
symbol xyz: atom+
symbol abc: bruh-

xyz() >< abc()";

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
            vec![Simple::custom(
                117..120,
                "agents xyz, abc have primary ports with unmatched types; found atom and bruh, which do not match"
            ),]
        );
    }

    #[test]
    fn test_poorly_typed() {
        let program = "type atom

# This cannot compile, since atom is not opposite polarity
symbol xyz: atom+

xyz() >< xyz()";

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
            vec![Simple::custom(
                89..92,
                "agents xyz, xyz do not have equally typed, complementary primary ports"
            ),]
        );
    }

    #[test]
    fn test_unrecognized_identifiers() {
        let program = "type atom

# This references a type that does not exist.
# The compiler will tell you.
symbol xyz: nat+

# This redex also references symbols that don't exist
# the compiler will also tell you
bruh(alsounrecognized(), skibidi()) >< bruh()";

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
                Simple::custom(94..97, "symbol xyz references unknown type nat"),
                Simple::custom(193..197, "agent references unknown symbol bruh"),
            ]
        );
    }

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

    #[test]
    fn test_terminal_port_for() {
        let program = "type nat

symbol Z: nat+
symbol Add: nat-, nat-, nat+

Z() >< Add(y, y)
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

        let (program, _) = parse_typed_program(parsed);

        assert_eq!(
            program.terminal_port_for(
                &program.nets.iter().collect::<Vec<_>>()[0]
                    .rhs
                    .clone()
                    .unwrap()
            ),
            Some(
                program.nets.iter().collect::<Vec<_>>()[0]
                    .rhs
                    .clone()
                    .unwrap()
                    .ports[1]
                    .as_var()
                    .unwrap()
            )
        );
    }
}
