use crate::parser::ast_combinators::Port;
use std::fmt;

#[derive(Debug, Clone)]
pub struct CombinatedProgram {
    pub nets: Vec<Port>,
}

impl fmt::Display for CombinatedProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.nets
                .iter()
                .map(|n| n.to_string())
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}
