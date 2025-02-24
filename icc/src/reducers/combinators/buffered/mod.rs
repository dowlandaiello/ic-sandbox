use super::{Cell, Conn, Ptr};
use std::iter::DoubleEndedIterator;

pub mod adjacency_matrix;

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

    fn iter_aux_ports(&self, cell: Ptr) -> impl DoubleEndedIterator<Item = Option<Conn>>;

    fn primary_port(&self, cell: Ptr) -> Option<Conn>;
}
