use chumsky::{prelude::*, text, Error};
use serde::{Deserialize, Serialize};
use std::fmt;

pub type VarName = String;

#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub enum Expr {
    Application {
        rules: Vec<Rule>,
        instance: RuleActivePair,
    },
    Book {
        rules: Vec<Rule>,
    },
}

impl Expr {
    pub fn to_application(self) -> Option<(Vec<Rule>, RuleActivePair)> {
        match self {
            Self::Application { rules, instance } => Some((rules, instance)),
            _ => None,
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Application { rules, instance } => {
                write!(
                    f,
                    "{}\n{}",
                    rules
                        .iter()
                        .map(|w| w.to_string())
                        .collect::<Vec<_>>()
                        .join("\n"),
                    instance
                )
            }
            Self::Book { rules } => {
                write!(
                    f,
                    "{}",
                    rules
                        .iter()
                        .map(|w| w.to_string())
                        .collect::<Vec<_>>()
                        .join("\n")
                )
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Rule {
    lhs: RuleActivePair,
    rhs: Vec<InstanceActivePair>,
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} => {}",
            self.lhs,
            self.rhs
                .iter()
                .map(|w| w.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RuleActivePair {
    pub lhs: ActivePairMember,
    pub rhs: ActivePairMember,
}

impl fmt::Display for RuleActivePair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} >< {}", self.lhs, self.rhs)
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct InstanceActivePair {
    pub lhs: ActivePairMember,
    pub rhs: ActivePairMember,
}

impl fmt::Display for InstanceActivePair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ~ {}", self.lhs, self.rhs)
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ActivePairMember {
    Var(VarName),
    Agent {
        name: VarName,
        inactive_vars: Vec<ActivePairMember>,
    },
}

impl ActivePairMember {
    pub fn get_inactive_vars(&self) -> Option<&[ActivePairMember]> {
        match self {
            Self::Var(_) => None,
            Self::Agent { inactive_vars, .. } => Some(inactive_vars.as_slice()),
        }
    }
}

impl fmt::Display for ActivePairMember {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(v) => write!(f, "{v}"),
            Self::Agent {
                name,
                inactive_vars,
            } => write!(
                f,
                "{}{}",
                name,
                if !inactive_vars.is_empty() {
                    format!(
                        "[{}]",
                        inactive_vars
                            .iter()
                            .map(|v| v.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                } else {
                    String::new()
                }
            ),
        }
    }
}

pub fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    let active_pair_member = recursive(|input| {
        let agent = text::ident()
            .try_map(|s: String, span: <Simple<char> as Error<char>>::Span| {
                if s.chars()
                    .next()
                    .map(|c| c.is_uppercase())
                    .unwrap_or_default()
                {
                    Ok(s)
                } else {
                    Err(<Simple<char>>::custom(
                        span,
                        "agent names must be capitalized".to_owned(),
                    ))
                }
            })
            .then(
                input
                    .separated_by(just(',').padded())
                    .delimited_by(just('['), just(']'))
                    .or_not(),
            )
            .map(|(name, inactive_vars)| ActivePairMember::Agent {
                name,
                inactive_vars: inactive_vars.unwrap_or_default(),
            });
        let var = text::ident().map(ActivePairMember::Var);

        choice((agent, var))
    });

    let rule_active_pair = active_pair_member
        .clone()
        .then_ignore(just("><").padded())
        .then(active_pair_member.clone())
        .map(|(lhs, rhs)| RuleActivePair { lhs, rhs });

    let instance_active_pair = active_pair_member
        .clone()
        .then_ignore(just("~").padded())
        .then(active_pair_member)
        .map(|(lhs, rhs)| InstanceActivePair { lhs, rhs });

    let rule = rule_active_pair
        .clone()
        .then_ignore(just("=>").padded())
        .then(instance_active_pair.separated_by(just(',').padded()))
        .map(|(lhs, rhs)| Rule { lhs, rhs });

    let book = rule.separated_by(just("\n").repeated());
    let application = book
        .clone()
        .then_ignore(just("\n").repeated())
        .then(rule_active_pair)
        .map(|(rules, instance)| Expr::Application { rules, instance });

    choice((
        book.map(|rules| Expr::Book { rules }).then_ignore(end()),
        application.then_ignore(end()),
    ))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse_book() {
        let to_parse = "Add[x, y] >< Z => x ~ y\nAdd[x, y] >< S[a] => x ~ S[b], a ~ Add[b, y]";
        let expr: Expr = parser().parse(to_parse).unwrap();

        assert_eq!(
            expr,
            Expr::Book {
                rules: vec![
                    Rule {
                        lhs: RuleActivePair {
                            lhs: ActivePairMember::Agent {
                                name: "Add".into(),
                                inactive_vars: vec![
                                    ActivePairMember::Var("x".into()),
                                    ActivePairMember::Var("y".into())
                                ]
                            },
                            rhs: ActivePairMember::Agent {
                                name: "Z".into(),
                                inactive_vars: Vec::new()
                            },
                        },
                        rhs: vec![InstanceActivePair {
                            lhs: ActivePairMember::Var("x".into()),
                            rhs: ActivePairMember::Var("y".into())
                        }]
                    },
                    Rule {
                        lhs: RuleActivePair {
                            lhs: ActivePairMember::Agent {
                                name: "Add".into(),
                                inactive_vars: vec![
                                    ActivePairMember::Var("x".into()),
                                    ActivePairMember::Var("y".into())
                                ]
                            },
                            rhs: ActivePairMember::Agent {
                                name: "S".into(),
                                inactive_vars: vec![ActivePairMember::Var("a".into())]
                            },
                        },
                        rhs: vec![
                            InstanceActivePair {
                                lhs: ActivePairMember::Var("x".into()),
                                rhs: ActivePairMember::Agent {
                                    name: "S".into(),
                                    inactive_vars: vec![ActivePairMember::Var("b".into())]
                                }
                            },
                            InstanceActivePair {
                                lhs: ActivePairMember::Var("a".into()),
                                rhs: ActivePairMember::Agent {
                                    name: "Add".into(),
                                    inactive_vars: vec![
                                        ActivePairMember::Var("b".into()),
                                        ActivePairMember::Var("y".into())
                                    ]
                                }
                            }
                        ]
                    }
                ]
            }
        );
        assert_eq!(&expr.to_string(), to_parse);
    }

    #[test]
    fn test_parse_application() {
        let to_parse = "Add[x, y] >< Z => x ~ y\nAdd[x, y] >< S[a] => x ~ S[b], a ~ Add[b, y]\nAdd[x, y] >< Add[z, a]";
        let expr: Expr = parser().parse(to_parse).unwrap();

        assert_eq!(
            expr,
            Expr::Application {
                rules: vec![
                    Rule {
                        lhs: RuleActivePair {
                            lhs: ActivePairMember::Agent {
                                name: "Add".into(),
                                inactive_vars: vec![
                                    ActivePairMember::Var("x".into()),
                                    ActivePairMember::Var("y".into())
                                ]
                            },
                            rhs: ActivePairMember::Agent {
                                name: "Z".into(),
                                inactive_vars: Vec::new()
                            },
                        },
                        rhs: vec![InstanceActivePair {
                            lhs: ActivePairMember::Var("x".into()),
                            rhs: ActivePairMember::Var("y".into())
                        }]
                    },
                    Rule {
                        lhs: RuleActivePair {
                            lhs: ActivePairMember::Agent {
                                name: "Add".into(),
                                inactive_vars: vec![
                                    ActivePairMember::Var("x".into()),
                                    ActivePairMember::Var("y".into())
                                ]
                            },
                            rhs: ActivePairMember::Agent {
                                name: "S".into(),
                                inactive_vars: vec![ActivePairMember::Var("a".into())]
                            },
                        },
                        rhs: vec![
                            InstanceActivePair {
                                lhs: ActivePairMember::Var("x".into()),
                                rhs: ActivePairMember::Agent {
                                    name: "S".into(),
                                    inactive_vars: vec![ActivePairMember::Var("b".into())]
                                }
                            },
                            InstanceActivePair {
                                lhs: ActivePairMember::Var("a".into()),
                                rhs: ActivePairMember::Agent {
                                    name: "Add".into(),
                                    inactive_vars: vec![
                                        ActivePairMember::Var("b".into()),
                                        ActivePairMember::Var("y".into())
                                    ]
                                }
                            }
                        ]
                    }
                ],
                instance: RuleActivePair {
                    lhs: ActivePairMember::Agent {
                        name: "Add".into(),
                        inactive_vars: vec![
                            ActivePairMember::Var("x".into()),
                            ActivePairMember::Var("y".into())
                        ]
                    },
                    rhs: ActivePairMember::Agent {
                        name: "Add".into(),
                        inactive_vars: vec![
                            ActivePairMember::Var("z".into()),
                            ActivePairMember::Var("a".into())
                        ]
                    },
                }
            }
        );
        assert_eq!(&expr.to_string(), to_parse);
    }
}
