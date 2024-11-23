use chumsky::{prelude::*, text, Error, Parser};
use serde::{Deserialize, Serialize};
use std::{collections::VecDeque, fmt};

const COMMENT_STR: &str = "--";

pub type VarName = String;

#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub enum Expr {
    Application {
        rules: Vec<Rule>,
        instance: Vec<Instance>,
    },
    Book {
        rules: Vec<Rule>,
    },
}

impl Expr {
    pub fn to_instance(&self) -> Option<&[Instance]> {
        match self {
            Self::Application { instance, .. } => Some(instance.as_slice()),
            _ => None,
        }
    }

    pub fn to_application(self) -> Option<(Vec<Rule>, Vec<Instance>)> {
        match self {
            Self::Application { rules, instance } => Some((rules, instance)),
            _ => None,
        }
    }

    pub fn to_book(self) -> Vec<Rule> {
        match self {
            Self::Application { rules, .. } | Self::Book { rules } => rules,
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
                        .iter()
                        .map(|w| w.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
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

#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
pub enum Instance {
    PairMember(ActivePairMember),
    ActivePair(InstanceActivePair),
}

impl Instance {
    pub fn as_active_pair(&self) -> Option<&InstanceActivePair> {
        match self {
            Self::ActivePair(p) => Some(p),
            Self::PairMember(_) => None,
        }
    }

    pub fn as_pair_member(&self) -> Option<&ActivePairMember> {
        match self {
            Self::ActivePair(_) => None,
            Self::PairMember(m) => Some(m),
        }
    }
}

impl fmt::Display for Instance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PairMember(m) => write!(f, "{}", m),
            Self::ActivePair(p) => write!(f, "{}", p),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Rule {
    pub lhs: RuleActivePair,
    pub rhs: Vec<Instance>,
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

impl From<RuleActivePair> for InstanceActivePair {
    fn from(r: RuleActivePair) -> Self {
        let RuleActivePair { lhs, rhs } = r;

        Self { lhs, rhs }
    }
}

impl fmt::Display for InstanceActivePair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ~ {}", self.lhs, self.rhs)
    }
}

#[derive(Eq, Hash, Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ActivePairMember {
    Var(VarName),
    Agent {
        name: VarName,
        inactive_vars: Vec<ActivePairMember>,
    },
}

impl ActivePairMember {
    pub fn is_var(&self) -> bool {
        matches!(self, Self::Var(_))
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        let mut to_check = VecDeque::from_iter([(self, other)]);

        while let Some((self_elem, other_elem)) = to_check.pop_front() {
            match other_elem {
                Self::Var(_) => {
                    return true;
                }
                Self::Agent {
                    name,
                    inactive_vars,
                } => match self_elem {
                    Self::Var(_) => {
                        return false;
                    }
                    Self::Agent {
                        name: name_2,
                        inactive_vars: inactive_vars2,
                    } => {
                        if name != name_2 {
                            return false;
                        }

                        if inactive_vars.len() != inactive_vars2.len() {
                            return false;
                        }

                        to_check.extend(inactive_vars2.iter().zip(inactive_vars));
                    }
                },
            }
        }

        true
    }

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
    let comment = just(COMMENT_STR).then_ignore(just("\n").not().repeated());

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
        .then(active_pair_member.clone())
        .map(|(lhs, rhs)| InstanceActivePair { lhs, rhs });

    let unit = just("()");

    let rule = rule_active_pair
        .clone()
        .then_ignore(just("=>").padded())
        .then(choice((
            unit.padded().map(|_| Vec::new()),
            instance_active_pair
                .clone()
                .map(|pair| Instance::ActivePair(pair))
                .or(active_pair_member
                    .clone()
                    .map(|member| Instance::PairMember(member)))
                .separated_by(just(',').padded()),
        )))
        .map(|(lhs, rhs)| Rule { lhs, rhs });

    let book = comment
        .repeated()
        .padded()
        .separated_by(just("\n"))
        .or_not()
        .ignored()
        .then(rule.separated_by(comment.repeated().padded().separated_by(just("\n"))));
    let application = book
        .clone()
        .then_ignore(comment.repeated().padded().separated_by(just("\n")))
        .then(
            instance_active_pair
                .map(|pair| Instance::ActivePair(pair.into()))
                .or(active_pair_member.map(|member| Instance::PairMember(member)))
                .separated_by(just(',').padded()),
        )
        .then_ignore(comment.repeated().padded().separated_by(just("\n")))
        .map(|((_, rules), instance)| Expr::Application { rules, instance });

    choice((
        book.map(|(_, rules)| Expr::Book { rules })
            .then_ignore(end()),
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
                        rhs: vec![Instance::ActivePair(InstanceActivePair {
                            lhs: ActivePairMember::Var("x".into()),
                            rhs: ActivePairMember::Var("y".into())
                        })]
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
                            Instance::ActivePair(InstanceActivePair {
                                lhs: ActivePairMember::Var("x".into()),
                                rhs: ActivePairMember::Agent {
                                    name: "S".into(),
                                    inactive_vars: vec![ActivePairMember::Var("b".into())]
                                }
                            }),
                            Instance::ActivePair(InstanceActivePair {
                                lhs: ActivePairMember::Var("a".into()),
                                rhs: ActivePairMember::Agent {
                                    name: "Add".into(),
                                    inactive_vars: vec![
                                        ActivePairMember::Var("b".into()),
                                        ActivePairMember::Var("y".into())
                                    ]
                                }
                            })
                        ]
                    }
                ]
            }
        );
        assert_eq!(&expr.to_string(), to_parse);
    }

    #[test]
    fn test_parse_application() {
        let to_parse = "Add[x, y] >< Z => x ~ y\nAdd[x, y] >< S[a] => x ~ S[b], a ~ Add[b, y]\nAdd[x, y] ~ Add[z, a]";
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
                        rhs: vec![Instance::ActivePair(InstanceActivePair {
                            lhs: ActivePairMember::Var("x".into()),
                            rhs: ActivePairMember::Var("y".into())
                        })]
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
                            Instance::ActivePair(InstanceActivePair {
                                lhs: ActivePairMember::Var("x".into()),
                                rhs: ActivePairMember::Agent {
                                    name: "S".into(),
                                    inactive_vars: vec![ActivePairMember::Var("b".into())]
                                }
                            }),
                            Instance::ActivePair(InstanceActivePair {
                                lhs: ActivePairMember::Var("a".into()),
                                rhs: ActivePairMember::Agent {
                                    name: "Add".into(),
                                    inactive_vars: vec![
                                        ActivePairMember::Var("b".into()),
                                        ActivePairMember::Var("y".into())
                                    ]
                                }
                            })
                        ]
                    }
                ],
                instance: vec![Instance::ActivePair(InstanceActivePair {
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
                })]
            }
        );
        assert_eq!(&expr.to_string(), to_parse);
    }
}
