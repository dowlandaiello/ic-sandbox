use super::{
    ast_combinators::{Constructor, Duplicator, Eraser, Expr, Port, Token, Var},
    ast_lafont::Ident,
    naming::NameIter,
};
use ast_ext::{Span, Spanned};
use chumsky::prelude::*;
use std::collections::{BTreeMap, VecDeque};

pub fn lexer() -> impl Parser<char, Vec<Spanned<Token>>, Error = Simple<char>> {
    let era = just("Era").map(|_| Token::Era);
    let constr = just("Constr").map(|_| Token::Constr);
    let dup = just("Dup").map(|_| Token::Dup);
    let comma = just(",").map(|_| Token::Comma);
    let left_bracket = just("[").map(|_| Token::LeftBracket);
    let right_bracket = just("]").map(|_| Token::RightBracket);
    let at = just("@").map(|_| Token::At);
    let left_paren = just("(").map(|_| Token::LeftParen);
    let right_paren = just(")").map(|_| Token::RightParen);
    let tilde = just("~").map(|_| Token::Tilde);
    let ident = text::ident().map(|s: String| Token::Ident(s.to_owned()));
    let digits = text::digits(10).try_map(|d: String, span| {
        Ok(Token::Digit(
            d.parse::<usize>()
                .map_err(|e| Simple::custom(span, e.to_string()))?,
        ))
    });
    let active_pair = just("><").map(|_| Token::ActivePair);

    let token = choice((
        comma,
        left_paren,
        right_paren,
        at,
        digits,
        left_bracket,
        right_bracket,
        choice((era, constr, dup)).or(ident),
        active_pair,
        tilde,
    ));

    token
        .padded_by(text::whitespace())
        .map_with_span(|tok, e: Span| Spanned(tok, e))
        .repeated()
        .then_ignore(end())
}

pub fn parser() -> impl Parser<Spanned<Token>, Vec<Spanned<Port>>, Error = Simple<Spanned<Token>>> {
    let span_just = move |val: Token| {
        filter::<Spanned<Token>, _, Simple<Spanned<Token>>>(move |tok: &Spanned<Token>| {
            tok.0 == val
        })
    };
    let agent = recursive(|expr| {
        select! {
            Spanned(Token::Era, span) => Spanned(AgentBuilder::Expr { phrase: Expr::Era(Eraser::new()), name: 0, conns: Vec::new() }, span),
	    Spanned(Token::Constr, span) => Spanned(AgentBuilder::Expr { phrase: Expr::Constr(Constructor::new()), name: 0, conns: Vec::new() }, span),
	    Spanned(Token::Dup, span) => Spanned(AgentBuilder::Expr { phrase: Expr::Dup(Duplicator::new()), name: 0, conns: Vec::new()}, span),
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
                expr,
                select! {Spanned(Token::Ident(s), span) => Spanned(AgentBuilder::Expr {
		    phrase: Expr::Var(Var { name: Ident(s), port: None}),
		    name: 0,
		    conns: Vec::new()
		}, span)},
		span_just(Token::At).ignore_then(select! {
		    Spanned(Token::Digit(d), span) => Spanned(AgentBuilder::Ref(d), span)
		})
            ))
            .separated_by(span_just(Token::Comma))
        )
        .then_ignore(span_just(Token::RightParen))
        .map(|((expr, name), children)| {
	    Spanned(expr.0.with_children(children.into_iter().map(|x| x.0).collect()).with_name(name.0), expr.1)
	})
    });
    let net = agent
        .clone()
        .then_ignore(span_just(Token::ActivePair))
        .then(agent.clone())
        .try_map(
            |(lhs, rhs): (Spanned<AgentBuilder>, Spanned<AgentBuilder>), span| {
                build_net(lhs, rhs).ok_or(Simple::custom(span, "couldn't build net"))
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
                name: Ident(lhs.0),
                port: None,
            })
            .into_port(&mut names);
            let rhs_var = Expr::Var(Var {
                name: Ident(rhs.0),
                port: None,
            })
            .into_port(&mut names);

            lhs_var.borrow_mut().set_primary_port(Some(rhs_var.clone()));
            rhs_var.borrow_mut().set_primary_port(Some(lhs_var.clone()));

            vec![Spanned(lhs_var, lhs.1)]
        });

    choice((
        net,
        wiring,
        agent.try_map(|agent, span| {
            build_agent(agent)
                .ok_or(Simple::custom(span, "couldn't build agent"))
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
    },
    Ref(usize),
}

impl AgentBuilder {
    pub fn with_children(self, c: Vec<AgentBuilder>) -> Self {
        match self {
            Self::Expr { phrase, name, .. } => Self::Expr {
                phrase,
                name,
                conns: c,
            },
            c => c,
        }
    }

    pub fn with_name(self, name: usize) -> Self {
        match self {
            Self::Expr { phrase, conns, .. } => Self::Expr {
                phrase,
                conns,
                name,
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

    pub fn into_expr(self) -> Option<(Expr, usize, Vec<AgentBuilder>)> {
        match self {
            AgentBuilder::Expr {
                phrase,
                name,
                conns,
            } => Some((phrase, name, conns)),
            _ => None,
        }
    }
}

pub fn build_agent(agent: Spanned<AgentBuilder>) -> Option<Spanned<Port>> {
    let mut built_agents: BTreeMap<usize, Spanned<Port>> = Default::default();
    let mut to_build: VecDeque<Spanned<AgentBuilder>> = VecDeque::from_iter([agent.clone()]);
    let mut to_build_later: VecDeque<Spanned<AgentBuilder>> = Default::default();
    let mut var_namer = NameIter::default();

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

        let agent = phrase.clone().into_port_named(*name);
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
    while let Some((_, name, children)) = to_build_later.pop_front().and_then(|x| x.0.into_agent())
    {
        let Spanned(agent_port, span) = &built_agents[&name];

        for child in children.into_iter() {
            let to_insert = match child {
                // We already have ports for agents, so we can
                // look them up and connect them
                AgentBuilder::Expr { phrase, name, .. } => {
                    if phrase.is_agent() {
                        built_agents[&name].clone()
                    } else {
                        let var = phrase.into_port_named(var_namer.next_var());
                        var.borrow_mut().set_primary_port(Some(agent_port.clone()));

                        Spanned(var, span.clone())
                    }
                }
                AgentBuilder::Ref(id) => built_agents[&id].clone(),
            };

            // Insert in the next available port
            if agent_port.borrow().primary_port().is_none() {
                agent_port.borrow_mut().set_primary_port(Some(to_insert.0));
            } else {
                agent_port.borrow_mut().push_aux_port(Some(to_insert.0));
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
    let lhs = build_agent(lhs)?;
    let rhs = build_agent(rhs)?;

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

    lhs.borrow_mut().set_primary_port(Some(rhs.0.clone()));
    rhs.borrow_mut().set_primary_port(Some(lhs.0.clone()));

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
