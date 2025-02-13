use super::{
    super::super::{Conn, Ptr},
    atomic_reprs::CellRepr,
    Cell, NetBuffer,
};
use std::{
    collections::{BTreeSet, VecDeque},
    fmt,
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

impl fmt::Debug for MatrixBuffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[derive(Debug)]
        struct OwnedCell {
            pos: usize,
            discriminant: Cell,
            primary_port: Option<Conn>,
            aux_ports: [Option<Conn>; 2],
        }

        let cell_debugs = self
            .cells
            .iter()
            .enumerate()
            .filter_map(|(i, repr)| {
                let disc = repr.load_discriminant_uninit_var().map(|c| match c {
                    Cell::Var(_) => Cell::Var(i),
                    x => x,
                })?;

                Some(OwnedCell {
                    pos: i,
                    discriminant: disc,
                    primary_port: repr.load_primary_port(),
                    aux_ports: [repr.load_aux_port(0), repr.load_aux_port(1)],
                })
            })
            .collect::<Vec<_>>();

        f.debug_struct("MatrixBuffer")
            .field("cells", &cell_debugs)
            .field("len", &self.len.load(Ordering::Relaxed))
            .field("next_free", &self.get_next_free())
            .finish()
    }
}

impl MatrixBuffer {
    pub(crate) fn new_with_capacity_nodes(capacity: usize) -> Self {
        // Capacitied to N^2, we should always have room at the beginning

        Self {
            cells: (0..capacity * capacity)
                .map(|_| CellRepr::default())
                .collect(),
            len: AtomicUsize::new(0).into(),
            next_free: AtomicUsize::new(0).into(),
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
        struct RedexVisitor<'a> {
            seen: BTreeSet<BTreeSet<Conn>>,
            pos: Ptr,
            view: &'a MatrixBuffer,
        }

        impl<'a> RedexVisitor<'a> {
            fn new(view: &'a MatrixBuffer) -> Self {
                Self {
                    seen: Default::default(),
                    pos: Default::default(),
                    view,
                }
            }
        }

        impl<'a> Iterator for RedexVisitor<'a> {
            type Item = (Conn, Conn);

            fn next(&mut self) -> Option<Self::Item> {
                loop {
                    if self.pos >= self.view.cells.len() {
                        return None;
                    }

                    let redex = self
                        .view
                        .iter_ports(self.pos)
                        .filter_map(|x| x)
                        .filter_map(|Conn { cell, .. }| {
                            let (conn_a, conn_b) = self.view.get_conn(cell, self.pos)?;

                            if conn_a.port == 0 && conn_b.port == 0 {
                                Some((conn_a, conn_b))
                            } else {
                                None
                            }
                        })
                        .next();

                    self.pos += 1;

                    if let Some(redex) = redex {
                        let record = BTreeSet::from_iter([redex.0, redex.1]);

                        if !self.seen.contains(&record) {
                            self.seen.insert(record);

                            return Some(redex);
                        }
                    }
                }
            }
        }

        RedexVisitor::new(self)
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
