use std::fmt;

pub type VarName = String;

pub struct Application {
    pub book: Book,
    pub instance: RuleActivePair,
}

impl fmt::Display for Application {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}", self.book, self.instance)
    }
}

pub struct Book {
    pub rules: Vec<Rule>,
}

impl fmt::Display for Book {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.rules
                .iter()
                .map(|w| w.to_string())
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

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

pub struct RuleActivePair {
    pub lhs: ActivePairMember,
    pub rhs: ActivePairMember,
}

impl fmt::Display for RuleActivePair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} >< {}", self.lhs, self.rhs)
    }
}

pub struct InstanceActivePair {
    pub lhs: ActivePairMember,
    pub rhs: ActivePairMember,
}

impl fmt::Display for InstanceActivePair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}~{}", self.lhs, self.rhs)
    }
}

pub enum ActivePairMember {
    Var(VarName),
    Agent {
        name: VarName,
        inactive_vars: Vec<ActivePairMember>,
    },
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
