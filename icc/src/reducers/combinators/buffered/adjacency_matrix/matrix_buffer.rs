use super::{
    super::super::{Conn, Ptr},
    Cell, NetBuffer, OwnedCell,
};
use lockfree::queue::Queue;
use std::{
    collections::{BTreeSet, VecDeque},
    fmt,
    iter::DoubleEndedIterator,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, Mutex,
    },
};

#[derive(Clone)]
pub struct MatrixBuffer {
    cells: Arc<[Mutex<Option<OwnedCell>>]>,
    len: Arc<AtomicUsize>,
    next_free: Arc<Queue<usize>>,
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
            .filter_map(|x| x.lock().unwrap().clone())
            .collect::<Vec<_>>();

        f.debug_struct("MatrixBuffer")
            .field("cells", &cell_debugs)
            .field("len", &self.len.load(Ordering::Relaxed))
            .finish()
    }
}

impl MatrixBuffer {
    pub(crate) fn new_with_capacity_nodes(capacity: usize) -> Self {
        // Capacitied to N^2, we should always have room at the beginning

        Self {
            cells: (0..capacity * capacity)
                .map(|_| Mutex::new(Default::default()))
                .collect(),
            len: AtomicUsize::new(0).into(),
            next_free: Queue::from_iter(0..capacity * capacity).into(),
        }
    }

    pub(crate) fn get_cell(&self, ptr: Ptr) -> &Mutex<Option<OwnedCell>> {
        &self.cells[ptr]
    }
}

impl NetBuffer for MatrixBuffer {
    fn push(&self, cell: Cell) -> Ptr {
        let next_free = self.next_free.pop().unwrap();

        *self.cells[next_free].lock().unwrap() = Some(OwnedCell::new(cell));

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
        self.cells.iter().enumerate().filter_map(|(i, x)| {
            if x.lock().unwrap().is_none() {
                None
            } else {
                Some(i)
            }
        })
    }

    fn iter_aux_ports(&self, cell: usize) -> impl DoubleEndedIterator<Item = Option<Conn>> {
        let cell_guard = &self.cells[cell].lock().unwrap();

        cell_guard.unwrap().aux_ports.into_iter()
    }

    fn iter_ports(&self, cell: usize) -> impl DoubleEndedIterator<Item = Option<Conn>> {
        let cell_guard = &self.cells[cell].lock().unwrap();
        let cell = cell_guard.unwrap();

        [cell.primary_port].into_iter().chain(cell.aux_ports)
    }
}
