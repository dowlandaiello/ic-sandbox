use super::{
    super::super::{Conn, Ptr},
    atomic_reprs::CellRepr,
    Cell, NetBuffer,
};
use std::{iter::DoubleEndedIterator, sync::Arc};

#[derive(Clone)]
pub struct MatrixBuffer {
    cells: Arc<[CellRepr]>,
}

impl MatrixBuffer {
    fn new(cells: Arc<[CellRepr]>) -> Self {
        Self { cells }
    }
}

impl NetBuffer for MatrixBuffer {
    fn push(&self, c: Cell) -> Ptr {
        todo!()
    }

    fn delete(&self, p: Ptr) {
        todo!()
    }

    fn connect(&self, from: Option<Conn>, to: Option<Conn>) {
        todo!()
    }

    fn get_conn(&self, from: usize, to: usize) -> Option<(Conn, Conn)> {
        let from_cell = &self.cells[from];
        let to_cell = &self.cells[to];

        let a_conn = from_cell
            .iter_ports()
            .filter_map(|x| x)
            .filter(|x| x.cell == to)
            .next()?;
        let b_conn = to_cell.load_port_i(a_conn.port)?;

        Some((a_conn, b_conn))
    }

    fn get_cell(&self, idx: usize) -> Cell {
        let elem = &self.cells[idx];
        elem.load_discriminant_uninit_var().unwrap()
    }

    fn iter_ports(&self, cell: usize) -> impl DoubleEndedIterator<Item = Option<Conn>> {
        let cell_repr = &self.cells[cell];

        cell_repr.iter_ports()
    }

    fn primary_port(&self, cell: usize) -> Option<Conn> {
        todo!()
    }
}
