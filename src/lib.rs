pub mod bytecode;
pub mod heuristics;
pub mod parser;
pub mod preprocessor;
pub mod reducers;

pub const UNIT_STR: &str = "()";
pub const COMMENT_STR: &str = "#";
pub const BYTECODE_INDENTATION_STR: &str = "  ";
pub const BYTECODE_EXTENSION: &str = ".dcode";
