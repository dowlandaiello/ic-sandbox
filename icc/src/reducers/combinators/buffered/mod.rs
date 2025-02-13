use super::{Conn, Ptr};
use std::{fmt, iter::DoubleEndedIterator};

pub mod adjacency_matrix;

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

pub trait NetBuffer {
    fn iter_tree(&self, p: Ptr) -> impl Iterator<Item = Ptr>;

    fn iter_cells(&self) -> impl Iterator<Item = Ptr>;

    fn iter_redexes<'a>(&'a self) -> impl Iterator<Item = (Conn, Conn)> + 'a;

    fn push(&self, c: Cell) -> Ptr;

    fn delete(&self, p: Ptr);

    fn connect(&self, from: Option<Conn>, to: Option<Conn>);

    fn get_conn(&self, cell: Ptr, port: Ptr) -> Option<(Conn, Conn)>;

    fn get_cell(&self, cell: Ptr) -> Cell;

    fn iter_ports(&self, cell: Ptr) -> impl DoubleEndedIterator<Item = Option<Conn>>;

    fn primary_port(&self, cell: Ptr) -> Option<Conn>;
}
