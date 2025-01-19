pub mod bytecode;
pub mod bytecode2;
pub mod heuristics;
pub mod parser;
pub mod preprocessor;
pub mod reducers;

#[cfg(test)]
mod test;

pub const UNIT_STR: &str = "()";
pub const COMMENT_STR: &str = "#";
pub const BYTECODE_INDENTATION_STR: &str = "  ";
pub const BYTECODE_EXTENSION: &str = ".ivm";

pub const NAME_CONSTR_AGENT: &str = "Constr";
pub const NAME_ERA_AGENT: &str = "Era";
pub const NAME_DUP_AGENT: &str = "Dup";
