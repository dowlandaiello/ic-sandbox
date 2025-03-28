use super::{
    super::super::{Conn, Ptr},
    atomic_reprs::CellRepr,
    Cell, NetBuffer,
};
use lockfree::queue::Queue;
use std::{
    collections::{BTreeSet, VecDeque},
    iter::DoubleEndedIterator,
    sync::Arc,
};

#[derive(Clone)]
pub struct MatrixBuffer {
    pub(crate) cells: Arc<[CellRepr]>,
    pub(crate) next_free: Arc<Queue<usize>>,
}

impl MatrixBuffer {
    pub(crate) fn grow(&mut self, by_n_cells: usize) {
        (*self).next_free = Arc::new(
            self.iter_pop_next_free()
                .chain(self.cells.len()..(self.cells.len() + by_n_cells))
                .collect(),
        );
        (*self).cells = self
            .cells
            .iter()
            .map(|x| x.clone())
            .chain((0..by_n_cells).map(|_| CellRepr::default()))
            .collect::<Vec<CellRepr>>()
            .into();
    }

    pub(crate) fn iter_pop_next_free<'a>(&'a self) -> impl Iterator<Item = usize> + 'a {
        self.next_free.pop_iter()
    }

    pub(crate) fn iter_cells_discriminants<'a>(&'a self) -> impl Iterator<Item = (Ptr, Cell)> + 'a {
        self.cells
            .iter()
            .enumerate()
            .filter_map(|(i, x)| Some((i, x.load_discriminant_uninit_var()?)))
    }

    #[cfg(test)]
    pub fn checksum(&self) {
        self.iter_cells().for_each(|i| {
            self.iter_ports(i)
                .enumerate()
                .filter_map(|(i, x)| Some((i, x?)))
                .for_each(|(port_self, conn)| {
                    tracing::trace!(
                        "checksum context: (cell: {}, port: {}), {}",
                        i,
                        port_self,
                        conn
                    );
                    tracing::trace!(
                        "checksum context: {}",
                        self.get_cell(i).load_discriminant_uninit_var().unwrap(),
                    );
                    tracing::trace!(
                        "checksum context: {}",
                        self.get_cell(conn.cell)
                            .load_discriminant_uninit_var()
                            .unwrap(),
                    );

                    assert_eq!(
                        self.iter_ports(conn.cell)
                            .nth(conn.port as usize)
                            .unwrap()
                            .unwrap(),
                        Conn {
                            cell: i,
                            port: port_self as u8
                        }
                    );
                });
        });
    }

    pub(crate) fn push_next_free(&self, free: usize) {
        self.next_free.push(free);
    }

    pub(crate) fn new_with_capacity_nodes(capacity: usize) -> Self {
        // Capacitied to N^2, we should always have room at the beginning

        Self {
            cells: (0..capacity * capacity)
                .map(|_| CellRepr::default())
                .collect(),
            next_free: Queue::from_iter(0..capacity * capacity).into(),
        }
    }

    pub(crate) fn get_cell(&self, ptr: Ptr) -> &CellRepr {
        &self.cells[ptr]
    }
}

impl NetBuffer for MatrixBuffer {
    fn push(&self, cell: Cell) -> Ptr {
        let next_free = self.next_free.pop().unwrap();

        self.cells[next_free].wipe();
        self.cells[next_free].store_discriminant(Some(cell));

        next_free
    }

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
            .filter_map(|(i, x)| x.load_discriminant_uninit_var().map(|_| i))
    }

    fn iter_aux_ports(&self, cell: usize) -> impl DoubleEndedIterator<Item = Option<Conn>> {
        let cell_guard = &self.cells[cell];

        cell_guard.iter_aux_ports()
    }

    fn iter_ports(&self, cell: usize) -> impl DoubleEndedIterator<Item = Option<Conn>> {
        let cell_guard = &self.cells[cell];

        cell_guard.iter_ports()
    }
}
