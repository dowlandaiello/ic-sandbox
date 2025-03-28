pub mod parser;
pub mod reducers;

pub const UNIT_STR: &str = "()";
pub const COMMENT_STR: &str = "#";
pub const BYTECODE_INDENTATION_STR: &str = "  ";
pub const BYTECODE_EXTENSION: &str = ".ivm";

pub const NAME_CONSTR_AGENT: &str = "Constr";
pub const NAME_ERA_AGENT: &str = "Era";
pub const NAME_DUP_AGENT: &str = "Dup";
