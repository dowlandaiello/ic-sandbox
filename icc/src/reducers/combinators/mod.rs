use crate::parser::ast_combinators::Port;
pub use buffered::adjacency_matrix::reduce_dyn;
use std::collections::BTreeSet;

pub mod buffered;

pub type Ptr = usize;

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Copy, Debug)]
pub struct Conn {
    pub cell: Ptr,
    pub port: u8,
}

impl From<(Ptr, u8)> for Conn {
    fn from((cell, port): (Ptr, u8)) -> Self {
        Self { cell, port }
    }
}

#[derive(Default, Debug, Clone)]
pub struct Reduction {
    pub nets: Vec<Port>,
    pub active_pairs: BTreeSet<(Port, Port)>,
}

pub trait Reducer {
    fn readback(&self) -> Vec<Port>;

    fn reduce(&mut self) -> Vec<Port>;

    fn reduce_step(&self, redex: (Conn, Conn));
}
