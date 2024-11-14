use super::ast::{Expr, Rule};

/// Eliminates redundant rules in the given rulset, producing an equivalent ruleset.
pub fn simplify(_rule: Vec<Rule>) -> Vec<Rule> {
    unimplemented!()
}

/// Eliminates all redundant rules in the book or application.
pub fn simplify_all(e: Expr) -> Expr {
    match e {
        Expr::Application { instance, rules } => Expr::Application {
            rules: simplify(rules),
            instance,
        },
        Expr::Book { rules } => Expr::Book {
            rules: simplify(rules),
        },
    }
}
