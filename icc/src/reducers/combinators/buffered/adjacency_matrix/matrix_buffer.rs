use super::{
    super::super::{Conn, Ptr},
    atomic_reprs::CellRepr,
    Cell, NetBuffer,
};
use std::{
    collections::{BTreeSet, VecDeque},
    iter::DoubleEndedIterator,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

#[derive(Clone)]
pub struct MatrixBuffer {
    cells: Arc<[CellRepr]>,
    len: Arc<AtomicUsize>,
    next_free: Arc<AtomicUsize>,
}

impl MatrixBuffer {
    pub(crate) fn new(cells: Arc<[CellRepr]>) -> Self {
        // Should be in contiguous order. All remaining get overwritten
        let len = cells.len();

        // Capacitied to N^2, we should always have room at the beginning
        let next_free = cells
            .iter()
            .enumerate()
            .filter(|(_, x)| x.is_empty())
            .map(|(i, _)| i)
            .next()
            .expect("out of matrix storage at initialization");

        Self {
            cells,
            len: AtomicUsize::new(len).into(),
            next_free: AtomicUsize::new(next_free).into(),
        }
    }

    fn get_next_free(&self) -> usize {
        self.cells.iter().position(|x| x.is_empty()).unwrap()
    }
}

impl NetBuffer for MatrixBuffer {
    fn iter_tree(&self, p: Ptr) -> impl Iterator<Item = Ptr> {
        struct TreeWalker<'a> {
            view: &'a MatrixBuffer,
            seen: BTreeSet<Ptr>,
            to_visit: VecDeque<Ptr>,
        }

        impl<'a> TreeWalker<'a> {
            fn new(pos: Ptr, view: &'a MatrixBuffer) -> Self {
                Self {
                    view,
                    seen: Default::default(),
                    to_visit: VecDeque::from_iter([pos]),
                }
            }
        }

        impl<'a> Iterator for TreeWalker<'a> {
            type Item = Ptr;

            fn next(&mut self) -> Option<Self::Item> {
                self.to_visit = self
                    .to_visit
                    .drain(..)
                    .skip_while(|pos| self.seen.contains(&pos))
                    .collect();

                let pos = self.to_visit.pop_front()?;

                self.seen.insert(pos);

                self.to_visit.extend(
                    self.view
                        .iter_ports(pos)
                        .filter_map(|x| x)
                        .filter(|Conn { port: _, cell }| !self.seen.contains(&cell))
                        .map(|Conn { cell, .. }| cell),
                );

                Some(pos)
            }
        }

        TreeWalker::new(p, self)
    }

    fn iter_cells(&self) -> impl Iterator<Item = Ptr> {
        self.cells
            .iter()
            .enumerate()
            .filter_map(|(i, x)| if x.is_empty() { None } else { Some(i) })
    }

    fn iter_redexes<'a>(&'a self) -> impl Iterator<Item = (Conn, Conn)> + 'a {
        self.cells
            .iter()
            .enumerate()
            .filter(|(_, x)| !x.is_empty())
            .map(move |(i, x)| {
                x.iter_ports()
                    .filter_map(|x| x)
                    .filter_map(move |Conn { cell, .. }| {
                        let (conn_a, conn_b) = self.get_conn(cell, i)?;

                        if conn_a.port == 0 && conn_b.port == 0 {
                            Some((conn_a, conn_b))
                        } else {
                            None
                        }
                    })
            })
            .flatten()
    }

    fn push(&self, c: Cell) -> Ptr {
        self.len.fetch_add(1, Ordering::SeqCst);

        // Free port may not be contiguous. We may be currently at an unsafe value
        self.next_free
            .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |mut idx| {
                if !self.cells[idx].is_empty() {
                    idx = self.get_next_free();
                }

                Some(idx)
            })
            .unwrap();

        // It is normalized now
        let last_free = self.next_free.fetch_add(1, Ordering::SeqCst);

        self.cells[last_free].store_discriminant(Some(c));

        last_free
    }

    fn delete(&self, p: Ptr) {
        self.len.fetch_sub(1, Ordering::SeqCst);
        self.next_free.store(p, Ordering::SeqCst);

        let cell = &self.cells[p];
        cell.store_discriminant(None);
    }

    fn connect(&self, from: Option<Conn>, to: Option<Conn>) {
        if let Some(from) = from {
            let cell = &self.cells[from.cell];
            cell.store_port_i(from.port, to);
        }

        if let Some(to) = to {
            let cell = &self.cells[to.cell];
            cell.store_port_i(to.port, from);
        }
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
        let cell = elem.load_discriminant_uninit_var().unwrap();

        match cell {
            Cell::Var(_) => Cell::Var(idx),
            x => x,
        }
    }

    fn iter_ports(&self, cell: usize) -> impl DoubleEndedIterator<Item = Option<Conn>> {
        let cell_repr = &self.cells[cell];

        cell_repr.iter_ports()
    }

    fn primary_port(&self, cell: usize) -> Option<Conn> {
        self.cells[cell].load_primary_port()
    }
}
