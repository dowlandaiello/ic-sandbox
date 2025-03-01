use super::{Cell, Conn, Ptr};
use std::iter::DoubleEndedIterator;

pub mod adjacency_matrix;

pub trait NetBuffer {
    fn iter_tree(&self, p: Ptr) -> impl Iterator<Item = Ptr>;

    fn iter_cells(&self) -> impl Iterator<Item = Ptr>;

    fn iter_ports(&self, cell: Ptr) -> impl DoubleEndedIterator<Item = Option<Conn>>;

    fn iter_aux_ports(&self, cell: Ptr) -> impl DoubleEndedIterator<Item = Option<Conn>>;

    fn push(&self, c: Cell) -> Ptr;
}
