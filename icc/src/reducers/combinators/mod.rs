use crate::parser::ast_combinators::Port;
pub use buffered::adjacency_matrix::reduce_dyn;
use std::fmt;

pub mod buffered;

pub type Ptr = usize;

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Copy, Debug)]
pub enum Cell {
    Constr,
    Dup,
    Era,

    // Vars have unique, monotonically increasing
    // discriminants as well
    Var(usize),
}

impl fmt::Display for Cell {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constr => write!(f, "Constr"),
            Self::Dup => write!(f, "Dup"),
            Self::Era => write!(f, "Era"),
            Self::Var(v) => write!(f, "{}", v),
        }
    }
}

impl Cell {
    pub fn discriminant_uninit_var(&self) -> u8 {
        match self {
            Self::Constr => 0,
            Self::Dup => 1,
            Self::Era => 2,
            Self::Var(_) => 3,
        }
    }

    pub fn from_discriminant_uninit_var(d: u8) -> Self {
        match d {
            0 => Self::Constr,
            1 => Self::Dup,
            2 => Self::Era,
            3 => Self::Var(0),
            _ => panic!("discriminant out of bounds"),
        }
    }
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Clone, Copy, Debug)]
pub struct Conn {
    pub cell: Ptr,
    pub port: u8,
}

impl fmt::Display for Conn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(cell: {}, port: {})", self.cell, self.port)
    }
}

impl From<(Ptr, u8)> for Conn {
    fn from((cell, port): (Ptr, u8)) -> Self {
        Self { cell, port }
    }
}

pub trait Reducer {
    fn readback(&self) -> Vec<Port>;

    fn reduce(&mut self) -> Vec<Port>;

    fn reduce_step(&self, redex: (Conn, Conn));
}
