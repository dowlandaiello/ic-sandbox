use super::{
    ast_combinators::{Constructor, Duplicator, Eraser, Expr, Port, Token, Var},
    naming::NameIter,
};
use ast_ext::Spanned;
use chumsky::prelude::*;
use std::collections::{BTreeMap, VecDeque};

pub fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<Spanned<Token>>, extra::Err<Rich<'src, char>>> {
    let era = just("Era").map(|_| Token::Era);
    let constr = just("Constr").map(|_| Token::Constr);
    let dup = just("Dup").map(|_| Token::Dup);
    let comma = just(",").map(|_| Token::Comma);
    let left_bracket = just("[").map(|_| Token::LeftBracket);
    let right_bracket = just("]").map(|_| Token::RightBracket);
    let at = just("@").map(|_| Token::At);
    let hash = just("#").map(|_| Token::Idx);
    let left_paren = just("(").map(|_| Token::LeftParen);
    let right_paren = just(")").map(|_| Token::RightParen);
    let tilde = just("~").map(|_| Token::Tilde);
    let ident = text::ident().map(|s: &str| Token::Ident(s.to_owned()));
    let digits = text::int(10).try_map(|u: &str, span| {
        u.parse()
            .map_err(|e| Rich::custom(span, e))
            .map(|d| Token::Digit(d))
    });
    let active_pair = just("><").map(|_| Token::ActivePair);

    let token = choice((
        comma,
        left_paren,
        right_paren,
        at,
        hash,
        digits,
        left_bracket,
        right_bracket,
        choice((era, constr, dup)).or(ident),
        active_pair,
        tilde,
    ));

    token
        .padded_by(text::whitespace())
        .map_with(|tok: Token, e| {
            Spanned(
                tok,
                {
                    let x: SimpleSpan = e.span();
                    x
                }
                .into_range(),
            )
        })
        .repeated()
        .collect()
        .then_ignore(end())
}

pub fn parser<'src>(
) -> impl Parser<'src, &'src [Spanned<Token>], Vec<Spanned<Port>>, extra::Err<Rich<'src, Spanned<Token>>>>
{
    let span_just = move |val: Token| {
        select! {
            Spanned(x, s) if x == val => Spanned(x, s)
        }
    };
    let agent = recursive(|expr| {
        select! {
            Spanned(Token::Era, span) => Spanned(AgentBuilder::Expr { phrase: Expr::Era(Eraser::new()), name: 0, conns: Vec::new(), port: None }, span),
	    Spanned(Token::Constr, span) => Spanned(AgentBuilder::Expr { phrase: Expr::Constr(Constructor::new()), name: 0, conns: Vec::new(), port: None }, span),
	    Spanned(Token::Dup, span) => Spanned(AgentBuilder::Expr { phrase: Expr::Dup(Duplicator::new()), name: 0, conns: Vec::new(), port: None}, span),
        }
        .then_ignore(span_just(Token::LeftBracket))
        .then_ignore(span_just(Token::At))
        .then(select!{
	    Spanned(Token::Digit(d), s) => Spanned(d, s)
	})
        .then_ignore(span_just(Token::RightBracket))
        .then_ignore(span_just(Token::LeftParen))
        .then(
            choice((
                expr
		    .then(
			span_just(Token::Idx)
			    .ignore_then(
				select!{
				    Spanned(Token::Digit(d), span) => Spanned(d, span)
				})
			    .or_not())
		    .map(|(e, pos): (Spanned<AgentBuilder>, Option<Spanned<usize>>)| {
			pos.map(|p| Spanned(e.0.clone().with_port(Some(p.0)), e.1.clone())).unwrap_or(e)
		    }),
                select! {Spanned(Token::Ident(s), span) => Spanned(AgentBuilder::Expr {
		    phrase: Expr::Var(Var { name: s, port: None}),
		    name: 0,
		    conns: Vec::new(),
		    port: Some(0),
		}, span)},
		span_just(Token::At)
		    .ignore_then(select!{Spanned(Token::Digit(d), span) => Spanned(d, span)})
		    .then_ignore(span_just(Token::Idx))
		    .then(select!{Spanned(Token::Digit(d), span) => Spanned(d, span)})
		    .map(|(id, idx)| (
			Spanned(AgentBuilder::Ref { port: idx.0, agent_id: id.0 }, id.1)))
            ))
            .separated_by(span_just(Token::Comma))
            .collect()
        )
        .then_ignore(span_just(Token::RightParen))
        .map(|((expr, name), children): ((Spanned<AgentBuilder>, Spanned<usize>), Vec<Spanned<AgentBuilder>>)| {
	    Spanned(expr.0.with_children(children.into_iter().map(|x| x.0).collect()).with_name(name.0), expr.1)
	})
    });
    let net = agent
        .clone()
        .then_ignore(span_just(Token::ActivePair))
        .then(agent.clone())
        .try_map(
            |(lhs, rhs): (Spanned<AgentBuilder>, Spanned<AgentBuilder>), span| {
                build_net(lhs, rhs).ok_or(Rich::custom(span, "couldn't build net"))
            },
        );

    let var = select! {
    Spanned(Token::Ident(a), span) => Spanned(a, span)
    };
    let wiring = var
        .then_ignore(span_just(Token::Tilde))
        .then(var)
        .map(|(lhs, rhs)| {
            let mut names = NameIter::default();

            let lhs_var = Expr::Var(Var {
                name: lhs.0,
                port: None,
            })
            .into_port(&mut names);
            let rhs_var = Expr::Var(Var {
                name: rhs.0,
                port: None,
            })
            .into_port(&mut names);

            lhs_var
                .borrow_mut()
                .set_primary_port(Some((0, rhs_var.clone())));
            rhs_var
                .borrow_mut()
                .set_primary_port(Some((0, lhs_var.clone())));

            vec![Spanned(lhs_var, lhs.1)]
        });

    choice((
        net,
        wiring,
        agent.try_map(|agent, span| {
            build_agent(agent, &mut Default::default())
                .ok_or(Rich::custom(span, "couldn't build agent"))
                .map(|a| vec![a])
        }),
    ))
    .then_ignore(end())
}

#[derive(Debug, Clone)]
pub enum AgentBuilder {
    Expr {
        phrase: Expr,
        name: usize,
        conns: Vec<AgentBuilder>,
        port: Option<usize>,
    },
    Ref {
        port: usize,
        agent_id: usize,
    },
}

impl AgentBuilder {
    pub fn with_port(self, port: Option<usize>) -> Self {
        match self {
            Self::Expr {
                phrase,
                name,
                conns,
                port: _,
            } => Self::Expr {
                phrase,
                name,
                conns,
                port,
            },
            Self::Ref { agent_id, port: _ } => Self::Ref {
                agent_id,
                port: port.unwrap(),
            },
        }
    }

    pub fn with_children(self, c: Vec<AgentBuilder>) -> Self {
        match self {
            Self::Expr {
                port, phrase, name, ..
            } => Self::Expr {
                phrase,
                name,
                conns: c,
                port,
            },
            c => c,
        }
    }

    pub fn with_name(self, name: usize) -> Self {
        match self {
            Self::Expr {
                port,
                phrase,
                conns,
                ..
            } => Self::Expr {
                phrase,
                conns,
                name,
                port,
            },
            c => c,
        }
    }

    pub fn is_agent(&self) -> bool {
        match self {
            AgentBuilder::Expr { phrase, .. } => phrase.is_agent(),
            _ => false,
        }
    }

    pub fn into_agent(self) -> Option<(Expr, usize, Vec<AgentBuilder>)> {
        match self {
            AgentBuilder::Expr {
                phrase,
                name,
                conns,
                ..
            } => {
                if phrase.is_agent() {
                    Some((phrase, name, conns))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn as_agent(&self) -> Option<(&Expr, &usize, &Vec<AgentBuilder>)> {
        match &self {
            AgentBuilder::Expr {
                phrase,
                name,
                conns,
                ..
            } => {
                if phrase.is_agent() {
                    Some((phrase, name, conns))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn into_expr(self) -> Option<(Expr, usize, Vec<AgentBuilder>, Option<usize>)> {
        match self {
            AgentBuilder::Expr {
                phrase,
                name,
                conns,
                port,
            } => Some((phrase, name, conns, port)),
            _ => None,
        }
    }
}

pub fn build_agent(agent: Spanned<AgentBuilder>, names: &mut NameIter) -> Option<Spanned<Port>> {
    let mut built_agents: BTreeMap<usize, Spanned<Port>> = Default::default();
    let mut to_build: VecDeque<Spanned<AgentBuilder>> = VecDeque::from_iter([agent.clone()]);
    let mut to_build_later: VecDeque<Spanned<AgentBuilder>> = Default::default();

    // First pass: build all agents
    // This will create ports for every expr that is not
    // a var, but will not connect refs, since
    // these may be circular
    while let Some(Spanned(builder, span)) = to_build.pop_front() {
        to_build_later.push_back(Spanned(builder.clone(), span.clone()));

        let (phrase, name, conns) = if let Some(x) = builder.as_agent() {
            x
        } else {
            continue;
        };

        let agent = phrase.clone().into_port(names);
        built_agents.insert(*name, Spanned(agent, span.clone()));

        // Expression children will not be inserted inline
        // but we will make the ports
        for child in conns.into_iter().filter(|x| x.is_agent()) {
            to_build.push_back(Spanned(child.clone(), span.clone()));
        }
    }

    // Second pass: wire all agents
    // Also create all vars in place, since
    // they cannot be connected to more than one agent
    // This does not work for top level redexes. We will have to bump all indices by 1, since
    // primary ports are taken
    while let Some((_, name, children)) = to_build_later.pop_front().and_then(|x| x.0.into_agent())
    {
        let Spanned(agent_port, _) = &built_agents[&name];

        for (i, child) in children.into_iter().enumerate() {
            let to_insert = match child {
                // We already have ports for agents, so we can
                // look them up and connect them
                AgentBuilder::Expr {
                    port, phrase, name, ..
                } => {
                    if phrase.is_agent() {
                        (port.unwrap_or_default(), built_agents[&name].clone().0)
                    } else {
                        let var = phrase.into_port(names);

                        let insert_idx = if built_agents
                            .get(agent.as_agent().as_ref()?.1)?
                            .0
                            .ptr_eq(agent_port)
                        {
                            i + 1
                        } else {
                            i
                        };

                        var.borrow_mut()
                            .set_primary_port(Some((insert_idx, agent_port.clone())));

                        (0, var)
                    }
                }
                AgentBuilder::Ref { port, agent_id } => (port, built_agents[&agent_id].clone().0),
            };

            // Insert in the next available port
            if agent_port.borrow().primary_port().is_none() {
                agent_port.borrow_mut().set_primary_port(Some(to_insert));
            } else {
                agent_port.borrow_mut().push_aux_port(Some(to_insert));
            }
        }
    }

    let Spanned(a, _) = agent;

    built_agents.remove(a.as_agent().as_ref()?.1)
}

pub fn build_net(
    lhs: Spanned<AgentBuilder>,
    rhs: Spanned<AgentBuilder>,
) -> Option<Vec<Spanned<Port>>> {
    let mut names = Default::default();

    let lhs = build_agent(lhs, &mut names)?;
    let rhs = build_agent(rhs, &mut names)?;

    // Shift down primary port to aux port
    let (aux_port_lhs, aux_port_rhs) = (
        lhs.borrow().aux_ports().iter().cloned().collect::<Vec<_>>(),
        rhs.borrow().aux_ports().iter().cloned().collect::<Vec<_>>(),
    );
    let (primary_port_lhs, primary_port_rhs) = (
        lhs.borrow_mut().primary_port().cloned(),
        rhs.borrow_mut().primary_port().cloned(),
    );

    lhs.borrow_mut().set_aux_ports([
        primary_port_lhs,
        aux_port_lhs.get(0).map(|x| x.as_ref()).flatten().cloned(),
    ]);
    rhs.borrow_mut().set_aux_ports([
        primary_port_rhs,
        aux_port_rhs.get(0).map(|x| x.as_ref()).flatten().cloned(),
    ]);

    lhs.borrow_mut().set_primary_port(Some((0, rhs.0.clone())));
    rhs.borrow_mut().set_primary_port(Some((0, lhs.0.clone())));

    Some(vec![lhs])
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_lex() {
        let cases = ["Constr() >< Era()"];

        for case in cases {
            let _ = lexer().parse(case).unwrap();
        }
    }
}
