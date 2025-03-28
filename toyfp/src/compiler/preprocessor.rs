use crate::parser::{Expr, Ty};
use inetlib::parser::naming::NameIter;
use std::collections::BTreeMap;

pub fn inline_ty(t: Ty, to_replace: &str, def_table: &BTreeMap<String, 

pub fn inline(e: Expr, to_replace: &str, def_table: &BTreeMap<String, Expr>) -> Expr {
    match e {
        Expr::Abstraction { bind_id, bind_ty, body } => Expr::Abstraction {
            bind_id,
            body: Box::new(inline(*body, to_replace, def_table)),
        },
        Expr::Application { lhs, rhs } => Expr::Application {
            lhs: Box::new(inline(*lhs, to_replace, def_table)),
            rhs: Box::new(inline(*rhs, to_replace, def_table)),
        },
        Expr::Id(id) => {
            if id == to_replace {
                def_table.get(&id).cloned().unwrap_or(Expr::Id(id))
            } else {
                Expr::Id(id)
            }
        }
    }
}

pub fn replace_occurrences_lc(e: Expr, old: &str, new: String) -> Expr {
    match e {
        Expr::Abstraction { bind_id, body } => {
            if bind_id == old {
                return Expr::Abstraction {
                    bind_id,
                    body: Box::new(replace_occurrences_lc(*body, old, new)),
                };
            }

            Expr::Abstraction {
                bind_id,
                body: Box::new(replace_occurrences_lc(*body, old, new)),
            }
        }
        Expr::Application { lhs, rhs } => Expr::Application {
            lhs: Box::new(replace_occurrences_lc(*lhs, old, new.clone())),
            rhs: Box::new(replace_occurrences_lc(*rhs, old, new.clone())),
        },
        Expr::Id(v) => Expr::Id(if v == old { new } else { v }),
    }
}

fn remove_root_shadow_vars(e: Expr, names: &NameIter) -> Expr {
    match e {
        Expr::Id(v) => {
            if v.starts_with("v") {
                Expr::Id(format!("_{}", v))
            } else {
                Expr::Id(v)
            }
        }
        Expr::Application { lhs, rhs } => Expr::Application {
            lhs: Box::new(remove_root_shadow_vars(*lhs, names)),
            rhs: Box::new(remove_root_shadow_vars(*rhs, names)),
        },
        Expr::Abstraction { bind_id, body } => {
            if bind_id.starts_with("v") {
                let new_bind_id = format!("_{}", bind_id);

                Expr::Abstraction {
                    bind_id: new_bind_id.clone(),
                    body: Box::new(remove_root_shadow_vars(
                        replace_occurrences_lc(*body, &bind_id, new_bind_id),
                        names,
                    )),
                }
            } else {
                Expr::Abstraction {
                    bind_id,
                    body: Box::new(remove_root_shadow_vars(*body, names)),
                }
            }
        }
    }
}

fn deduplicate_lc(
    e: Expr,
    used_names: &mut BTreeSet<String>,
    available_names: &mut BTreeSet<String>,
) -> Expr {
    match e {
        Expr::Abstraction { bind_id, body } => {
            let new_var = next_dedup(bind_id.clone(), used_names, available_names);

            let replaced = replace_occurrences_lc(*body, &bind_id, new_var.clone());

            Expr::Abstraction {
                bind_id: new_var,
                body: Box::new(deduplicate_lc(replaced, used_names, available_names)),
            }
        }
        Expr::Application { lhs, rhs } => Expr::Application {
            lhs: Box::new(deduplicate_lc(*lhs, used_names, available_names)),
            rhs: Box::new(deduplicate_lc(*rhs, used_names, available_names)),
        },
        v => v,
    }
}
