use super::{
    super::{super::Reducer, Conn, NetBuffer, Ptr},
    matrix_buffer::MatrixBuffer,
    Cell, OwnedCell,
};
use crate::parser::{
    ast_combinators::{Constructor, Duplicator, Eraser, Expr, Port, Var},
    ast_lafont::Ident,
    naming::NameIter,
};
#[cfg(feature = "threadpool")]
use rayon::iter::{IntoParallelIterator, ParallelDrainRange, ParallelIterator};
use std::{
    collections::{BTreeMap, BTreeSet},
    iter::{self, DoubleEndedIterator},
    ops::DerefMut,
    sync::{atomic::AtomicBool, MutexGuard},
    sync::{atomic::Ordering, Arc},
};

#[derive(Default)]
pub struct ReducerBuilder {
    idents: BTreeMap<Ptr, String>,
    names: BTreeMap<Ptr, usize>,
}

impl ReducerBuilder {
    pub fn with_init_net(self, net: &Port) -> CapacitiedBufferedMatrixReducerBuilder {
        self.with_init_nets([net].into_iter())
    }

    pub fn with_init_nets<'a>(
        mut self,
        nets: impl Iterator<Item = &'a Port> + Clone,
    ) -> CapacitiedBufferedMatrixReducerBuilder {
        let n_nodes = nets.clone().map(|net| net.iter_tree().count()).sum();

        let buff = MatrixBuffer::new_with_capacity_nodes(n_nodes);
        let mut root_redexes = BTreeSet::new();

        let slots_for_ast_elems: BTreeMap<usize, usize> = nets
            .clone()
            .map(|net| {
                net.iter_tree()
                    .enumerate()
                    .map(|(i, elem)| {
                        self.names.insert(i, elem.id);

                        let discriminant = match &*elem.borrow() {
                            Expr::Constr(_) => Cell::Constr,
                            Expr::Dup(_) => Cell::Dup,
                            Expr::Era(_) => Cell::Era,
                            Expr::Var(ident) => {
                                self.idents.insert(i, ident.name.to_string());

                                Cell::Var(i)
                            }
                        };

                        let ins_id = buff.push(discriminant);

                        tracing::trace!("expr {:?} -> cell {}", elem, ins_id);

                        (elem.id, ins_id)
                    })
                    .collect::<Vec<_>>()
            })
            .flatten()
            .collect();

        // Wire nodes
        nets.for_each(|net| {
            net.iter_tree().for_each(|elem| {
                let slot = slots_for_ast_elems.get(&elem.id).unwrap();

                tracing::trace!("walking expr {:?} (cell: {}) for linking", elem, slot);

                elem.iter_ports()
                    .into_iter()
                    .enumerate()
                    .filter_map(|(i, x)| Some((i, x?)))
                    .for_each(|(port_self, (port_other, p))| {
                        let other_slot = slots_for_ast_elems.get(&p.id).unwrap();

                        tracing::trace!(
                            "linking (cell: {}, port: {}) <-> (cell: {}, port: {})",
                            slot,
                            port_self,
                            other_slot,
                            port_other,
                        );

                        let cell_self = buff.get_cell(*slot);

                        cell_self.lock().unwrap().as_mut().unwrap().set_port_i(
                            port_self as u8,
                            Some(Conn {
                                cell: *other_slot,
                                port: port_other as u8,
                            }),
                        );

                        let cell_other = buff.get_cell(*other_slot);

                        cell_other.lock().unwrap().as_mut().unwrap().set_port_i(
                            port_other as u8,
                            Some(Conn {
                                cell: *slot,
                                port: port_self as u8,
                            }),
                        );

                        if port_self == 0
                            && port_other == 0
                            && !matches!(*elem.borrow(), Expr::Var(_))
                            && !matches!(*p.borrow(), Expr::Var(_))
                        {
                            root_redexes.insert(BTreeSet::from_iter([
                                Conn {
                                    cell: *other_slot,
                                    port: port_other as u8,
                                },
                                Conn {
                                    cell: *slot,
                                    port: port_self as u8,
                                },
                            ]));
                        }
                    });
            })
        });

        CapacitiedBufferedMatrixReducerBuilder {
            cells: buff,
            idents: self.idents,
            names: self.names,
            root_redexes: root_redexes
                .into_iter()
                .map(|x| {
                    let mut elems = x.into_iter();

                    (elems.next().unwrap(), elems.next().unwrap())
                })
                .collect(),
            locked: (0..(n_nodes * n_nodes))
                .map(|_| AtomicBool::new(false))
                .collect::<Vec<_>>()
                .into(),
        }
    }

    pub fn with_capacity_nodes(self, capacity: usize) -> CapacitiedBufferedMatrixReducerBuilder {
        CapacitiedBufferedMatrixReducerBuilder {
            cells: MatrixBuffer::new_with_capacity_nodes(capacity),
            idents: self.idents,
            names: self.names,
            root_redexes: Default::default(),
            locked: (0..(capacity * capacity))
                .map(|_| AtomicBool::new(false))
                .collect::<Vec<_>>()
                .into(),
        }
    }
}

pub struct CapacitiedBufferedMatrixReducerBuilder {
    cells: MatrixBuffer,
    idents: BTreeMap<Ptr, String>,
    names: BTreeMap<Ptr, usize>,
    root_redexes: Vec<(Conn, Conn)>,
    locked: Arc<[AtomicBool]>,
}

impl CapacitiedBufferedMatrixReducerBuilder {
    pub fn finish(self) -> BufferedMatrixReducer {
        BufferedMatrixReducer {
            buffer: self.cells,
            idents: self.idents,
            names: self.names,
            root_redexes: self.root_redexes,
            locked: self.locked,
        }
    }
}

pub struct BufferedMatrixReducer {
    buffer: MatrixBuffer,
    idents: BTreeMap<Ptr, String>,
    names: BTreeMap<Ptr, usize>,
    root_redexes: Vec<(Conn, Conn)>,
    locked: Arc<[AtomicBool]>,
}

#[derive(Clone)]
pub struct ReductionWorker {
    buffer: MatrixBuffer,
    locked: Arc<[AtomicBool]>,
}

impl ReductionWorker {
    fn mark_locked(&self, cell: Ptr) -> Option<()> {
        self.locked[cell]
            .compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
            .ok()
            .map(|_| ())
    }

    fn mark_unlocked(&self, cell: Ptr) {
        self.locked[cell]
            .compare_exchange(true, false, Ordering::Relaxed, Ordering::Relaxed)
            .unwrap();
    }

    fn conn_maybe_redex(
        &self,
        a: (Conn, OwnedCell),
        b: (Conn, OwnedCell),
    ) -> (
        Option<(Conn, Conn)>,
        ((usize, OwnedCell), (usize, OwnedCell)),
    ) {
        tracing::trace!("linking {} ~ {}", a.0, b.0);

        let (a_conn, mut a_cell) = a;
        let (b_conn, mut b_cell) = b;

        a_cell.wipe();
        b_cell.wipe();

        a_cell.set_port_i(a_conn.port, Some(b_conn));
        b_cell.set_port_i(b_conn.port, Some(a_conn));

        if a_conn.port == 0
            && b_conn.port == 0
            && !matches!(a_cell.discriminant, Cell::Var(_))
            && !matches!(b_cell.discriminant, Cell::Var(_))
        {
            tracing::trace!(
                "found new redex cell {} >< cell {}",
                a_conn.cell,
                b_conn.cell
            );

            return (
                Some((a_conn, b_conn)),
                ((a_conn.cell, a_cell), (b_conn.cell, b_cell)),
            );
        }

        (None, ((a_conn.cell, a_cell), (b_conn.cell, b_cell)))
    }

    #[tracing::instrument(skip(self))]
    fn reduce_step(&self, redex: (Conn, Conn)) -> Vec<(Conn, Conn)> {
        let a_id = redex.0.cell;
        let b_id = redex.1.cell;

        tracing::debug!("reducing {} >< {}", a_id, b_id);

        let mut maybe_to_lock = None;
        let mut maybe_locks: Option<BTreeMap<usize, _>> = None;

        while maybe_locks.is_none() {
            // Thi is to ensure consistent lock ordering
            let pair = if a_id < b_id {
                let lock_a = self.buffer.get_cell(a_id).lock().unwrap().unwrap();
                let lock_b = self.buffer.get_cell(b_id).lock().unwrap().unwrap();

                (lock_a, lock_b)
            } else {
                let lock_b = self.buffer.get_cell(b_id).lock().unwrap().unwrap();
                let lock_a = self.buffer.get_cell(a_id).lock().unwrap().unwrap();

                (lock_a, lock_b)
            };

            maybe_to_lock = Some(
                [a_id, b_id]
                    .into_iter()
                    .chain(
                        pair.0
                            .iter_aux_ports()
                            .filter_map(|x| x)
                            .map(|Conn { cell, port: _ }| cell),
                    )
                    .chain(
                        pair.1
                            .iter_aux_ports()
                            .filter_map(|x| x)
                            .map(|Conn { cell, port: _ }| cell),
                    )
                    .collect::<BTreeSet<_>>(),
            );

            if self
                .locked
                .iter()
                .take(*maybe_to_lock.as_ref().unwrap().iter().next().unwrap())
                .any(|is_locked| is_locked.load(Ordering::Relaxed))
            {
                continue;
            }

            maybe_locks = maybe_to_lock
                .as_ref()
                .unwrap()
                .iter()
                .map(|cell_id| {
                    let lock = self.buffer.get_cell(*cell_id).try_lock().ok()?;

                    Some((*cell_id, lock))
                })
                .collect::<Option<BTreeMap<usize, _>>>();
        }

        let to_lock = maybe_to_lock.unwrap();
        let mut locks = maybe_locks.unwrap();

        to_lock
            .iter()
            .for_each(|cell_id| self.mark_locked(*cell_id).unwrap());

        let mut a_lock = locks.get_mut(&a_id);
        let a_cell = *a_lock.as_mut().unwrap().deref_mut().as_ref().unwrap();

        let mut b_lock = locks.get_mut(&b_id);
        let b_cell = *b_lock.as_mut().unwrap().deref_mut().as_ref().unwrap();

        let transformations = {
            fn map_conn<'a>(
                c: Conn,
                locks: &BTreeMap<usize, MutexGuard<'a, Option<OwnedCell>>>,
            ) -> (Conn, OwnedCell) {
                tracing::trace!("deguarding {}", c.cell);

                (c, locks.get(&c.cell).unwrap().unwrap())
            }

            match (a_cell.discriminant, b_cell.discriminant) {
                // Annihilation of alpha-alpha
                (Cell::Constr, Cell::Constr) | (Cell::Dup, Cell::Dup) => {
                    tracing::trace!(
                        "a aux: {:?} b aux: {:?}",
                        a_cell.unwrap_aux_ports(),
                        b_cell.unwrap_aux_ports()
                    );

                    let (top_ports, bottom_ports) = (
                        a_cell
                            .unwrap_aux_ports()
                            .into_iter()
                            .map(|x| map_conn(x, &locks)),
                        b_cell
                            .unwrap_aux_ports()
                            .into_iter()
                            .map(|x| map_conn(x, &locks)),
                    );

                    // Remember, bottom ports is flipped due to orientation
                    Box::new(
                        top_ports
                            .into_iter()
                            .zip(bottom_ports)
                            .map(|(a, b)| self.conn_maybe_redex(a, b)),
                    )
                        as Box<
                            dyn Iterator<
                                Item = (
                                    Option<(Conn, Conn)>,
                                    ((usize, OwnedCell), (usize, OwnedCell)),
                                ),
                            >,
                        >
                }
                // Annihilation of Era
                (Cell::Era, Cell::Era) => Box::new(iter::empty())
                    as Box<
                        dyn Iterator<
                            Item = (
                                Option<(Conn, Conn)>,
                                ((usize, OwnedCell), (usize, OwnedCell)),
                            ),
                        >,
                    >,
                // Commutation of constr dup
                (Cell::Constr, Cell::Dup) => {
                    // Top is left to right, bottom is right to left
                    let (top_ports, bottom_ports) = (
                        a_cell
                            .unwrap_aux_ports()
                            .into_iter()
                            .map(|x| map_conn(x, &locks)),
                        b_cell
                            .unwrap_aux_ports()
                            .into_iter()
                            .map(|x| map_conn(x, &locks)),
                    );

                    Box::new(self.make_commutation(top_ports, bottom_ports))
                        as Box<
                            dyn Iterator<
                                Item = (
                                    Option<(Conn, Conn)>,
                                    ((usize, OwnedCell), (usize, OwnedCell)),
                                ),
                            >,
                        >
                }
                // Commutation of dup constr
                (Cell::Dup, Cell::Constr) => {
                    let (top_ports, bottom_ports) = (
                        b_cell
                            .unwrap_aux_ports()
                            .into_iter()
                            .map(|x| map_conn(x, &locks)),
                        a_cell
                            .unwrap_aux_ports()
                            .into_iter()
                            .map(|x| map_conn(x, &locks)),
                    );

                    Box::new(self.make_commutation(top_ports, bottom_ports))
                        as Box<
                            dyn Iterator<
                                Item = (
                                    Option<(Conn, Conn)>,
                                    ((usize, OwnedCell), (usize, OwnedCell)),
                                ),
                            >,
                        >
                }
                // Commutation of alpha era
                (Cell::Constr, Cell::Era) | (Cell::Dup, Cell::Era) => {
                    let top_ports = a_cell
                        .unwrap_aux_ports()
                        .into_iter()
                        .map(|x| map_conn(x, &locks));

                    Box::new(self.make_era_commutation(top_ports))
                        as Box<
                            dyn Iterator<
                                Item = (
                                    Option<(Conn, Conn)>,
                                    ((usize, OwnedCell), (usize, OwnedCell)),
                                ),
                            >,
                        >
                }
                (Cell::Era, Cell::Constr) | (Cell::Era, Cell::Dup) => {
                    let top_ports = b_cell
                        .unwrap_aux_ports()
                        .into_iter()
                        .map(|x| map_conn(x, &locks));

                    Box::new(self.make_era_commutation(top_ports))
                        as Box<
                            dyn Iterator<
                                Item = (
                                    Option<(Conn, Conn)>,
                                    ((usize, OwnedCell), (usize, OwnedCell)),
                                ),
                            >,
                        >
                }
                _ => {
                    panic!("invalid redex")
                }
            }
        };

        let (new_redexes, cells) = transformations.fold(
            (Vec::new(), BTreeMap::<usize, OwnedCell>::new()),
            |(mut redexes, mut cells), (maybe_redex, ((id_a, cell_a), (id_b, cell_b)))| {
                if let Some(r) = maybe_redex {
                    redexes.push(r);
                }

                cells
                    .entry(id_a)
                    .and_modify(|cell| {
                        cell.merge(&cell_a);
                    })
                    .or_insert(cell_a);

                cells
                    .entry(id_b)
                    .and_modify(|cell| {
                        cell.merge(&cell_b);
                    })
                    .or_insert(cell_b);

                (redexes, cells)
            },
        );

        cells.into_iter().for_each(|(id, cell)| {
            tracing::trace!("updating cell {}: {:?}", id, cell);

            if let Some(lock) = locks.get_mut(&id) {
                lock.as_mut().unwrap().merge(&cell);
            } else {
                self.buffer
                    .get_cell(id)
                    .lock()
                    .unwrap()
                    .as_mut()
                    .unwrap()
                    .merge(&cell);
            }
        });

        tracing::trace!("deleting cell {}", a_id);
        tracing::trace!("deleting cell {}", b_id);

        let mut a_lock = locks.get_mut(&a_id);
        let a_cell_ref = a_lock.as_mut().unwrap().deref_mut();

        **a_cell_ref = None;

        let mut b_lock = locks.get_mut(&b_id);
        let b_cell_ref = b_lock.as_mut().unwrap().deref_mut();

        **b_cell_ref = None;

        to_lock.iter().for_each(|cell_id| {
            self.mark_unlocked(*cell_id);
        });

        new_redexes
    }

    fn make_era_commutation<'a>(
        &'a self,
        top_ports: impl Iterator<Item = (Conn, OwnedCell)> + 'a,
    ) -> impl Iterator<
        Item = (
            Option<(Conn, Conn)>,
            ((usize, OwnedCell), (usize, OwnedCell)),
        ),
    > + 'a {
        let eras = [self.buffer.push(Cell::Era), self.buffer.push(Cell::Era)];

        top_ports
            .zip(eras.into_iter().map(|ptr| {
                (
                    (ptr, 0).into(),
                    (*self.buffer.get_cell(ptr).lock().unwrap()).unwrap(),
                )
            }))
            .map(|(a, b)| self.conn_maybe_redex(a, (b.0, b.1)))
    }

    fn make_commutation<'a>(
        &'a self,
        top_ports: impl DoubleEndedIterator<Item = (Conn, OwnedCell)> + 'a,
        bottom_ports: impl DoubleEndedIterator<Item = (Conn, OwnedCell)> + 'a,
    ) -> impl Iterator<
        Item = (
            Option<(Conn, Conn)>,
            ((usize, OwnedCell), (usize, OwnedCell)),
        ),
    > + 'a {
        // left to right
        let dups = [self.buffer.push(Cell::Dup), self.buffer.push(Cell::Dup)];

        // Left to right
        let constrs = [
            self.buffer.push(Cell::Constr),
            self.buffer.push(Cell::Constr),
        ];

        let conn_left = ((dups[0], 2), (constrs[0], 1));
        let conn_right = ((dups[1], 1), (constrs[1], 2));
        let conn_middle_left = ((dups[0], 1), (constrs[1], 1));
        let conn_middle_right = ((dups[1], 2), (constrs[0], 2));

        let conns = [conn_left, conn_right, conn_middle_left, conn_middle_right];

        top_ports
            .zip(dups.into_iter().map(|ptr| Conn { cell: ptr, port: 0 }))
            .map(|(a, b)| {
                let b_cell = self.buffer.get_cell(b.cell).lock().unwrap().unwrap();

                self.conn_maybe_redex(a, (b, b_cell))
            })
            .chain(
                bottom_ports
                    .rev()
                    .zip(constrs.into_iter().map(|ptr| Conn { cell: ptr, port: 0 }))
                    .map(|(a, b)| {
                        let b_cell = self.buffer.get_cell(b.cell).lock().unwrap().unwrap();

                        self.conn_maybe_redex(a, (b, b_cell))
                    })
                    .chain(conns.into_iter().map(|(a, b)| {
                        let a_cell = self.buffer.get_cell(a.0).lock().unwrap().unwrap();
                        let b_cell = self.buffer.get_cell(a.0).lock().unwrap().unwrap();

                        self.conn_maybe_redex((a.into(), a_cell), (b.into(), b_cell))
                    })),
            )
    }
}

impl Reducer for BufferedMatrixReducer {
    fn readback(&self) -> Vec<Port> {
        tracing::debug!("reading back");

        let new_names = NameIter::starting_from(self.names.len());

        // Make ports before linking, link later
        let mut ports_for_cells: BTreeMap<Ptr, Port> = self
            .buffer
            .iter_cells()
            .map(|i| (i, self.buffer.get_cell(i)))
            .map(|(i, locked_cell)| {
                let cell = locked_cell.lock().unwrap().unwrap();
                let discriminant = cell.discriminant;

                let name = self
                    .names
                    .get(&i)
                    .map(|x| *x)
                    .unwrap_or_else(|| new_names.next_id());

                let expr = match discriminant {
                    Cell::Constr => Expr::Constr(Constructor::new()).into_port_named(name),
                    Cell::Dup => Expr::Dup(Duplicator::new()).into_port_named(name),
                    Cell::Era => Expr::Era(Eraser::new()).into_port_named(name),
                    Cell::Var(v) => {
                        let ident = self.idents.get(&v).unwrap().clone();

                        Expr::Var(Var {
                            name: Ident(ident),
                            port: None,
                        })
                    }
                    .into_port_named(name),
                };

                tracing::trace!("cell {} -> expr {}", i, expr);

                (i, expr)
            })
            .collect();

        // Link them
        ports_for_cells.iter().for_each(|(i, entry)| {
            tracing::trace!("walking cell {} (expr: {}) for linking", i, entry);

            let mut ports = self.buffer.iter_ports(*i);

            if let Some(conn_p) = ports.next().flatten() {
                tracing::trace!("linking (cell: {}, port: 0) <-> {}", i, conn_p);

                let other_node = ports_for_cells.get(&conn_p.cell).unwrap();
                let ast_conn = (conn_p.port as usize, other_node.clone());

                entry.borrow_mut().set_primary_port(Some(ast_conn));
            }

            ports
                .enumerate()
                .filter_map(|(i, x)| Some((i, x?)))
                .for_each(|(j, conn_aux)| {
                    tracing::trace!(
                        "linking (cell: {}, port: {}) <-> (cell: {}, port: {})",
                        i,
                        j + 1,
                        conn_aux.cell,
                        conn_aux.port
                    );

                    let other_node = ports_for_cells.get(&conn_aux.cell).unwrap();
                    let ast_conn = (conn_aux.port as usize, other_node.clone());

                    entry.borrow_mut().insert_port_i(j + 1, Some(ast_conn));
                });
        });

        // Find all disjoint nets
        // TODO: This is really inefficient!
        self.buffer
            .iter_cells()
            .map(|cell_idx| self.buffer.iter_tree(cell_idx).collect::<BTreeSet<_>>())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .filter_map(|tree| {
                let head_buf_pos = tree.into_iter().next()?;
                ports_for_cells.remove(&head_buf_pos)
            })
            .collect::<Vec<_>>()
    }

    fn reduce_step(&self, redex: (Conn, Conn)) {
        let worker = ReductionWorker {
            buffer: self.buffer.clone(),
            locked: self.locked.clone(),
        };

        worker.reduce_step(redex);
    }

    fn reduce(&mut self) -> Vec<Port> {
        #[cfg(feature = "threadpool")]
        fn reduce_redexes(
            buffer: MatrixBuffer,
            locked: Arc<[AtomicBool]>,
            r: impl IntoParallelIterator<Item = (Conn, Conn)>,
        ) {
            r.into_par_iter().for_each(move |x| {
                let worker = ReductionWorker {
                    buffer: buffer.clone(),
                    locked: locked.clone(),
                };

                let redexes = worker.reduce_step(x);

                reduce_redexes(buffer.clone(), locked.clone(), redexes);
            });
        }

        #[cfg(not(feature = "threadpool"))]
        fn reduce_redexes(buffer: MatrixBuffer, r: impl IntoIterator<Item = (Conn, Conn)>) {
            r.into_iter().for_each(move |x| {
                let worker = ReductionWorker {
                    buffer: buffer.clone(),
                };

                let redexes = worker.reduce_step(x);

                reduce_redexes(buffer.clone(), redexes);
            });
        }

        tracing::trace!("reduction frame: {:#?}", self.buffer);

        // Push all redexes
        #[cfg(feature = "threadpool")]
        reduce_redexes(
            self.buffer.clone(),
            self.locked.clone(),
            self.root_redexes.par_drain(..),
        );

        #[cfg(not(feature = "threadpool"))]
        reduce_redexes(
            self.buffer.clone(),
            self.locked.clone(),
            self.root_redexes.drain(..),
        );

        self.readback()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::parser_combinators as parser;
    use chumsky::Parser;

    #[test_log::test]
    fn test_readback_matrix() {
        let cases = [
	    "Constr[@1](a, b) >< Constr[@2](c, d)",
	    "Dup[@1](a, b) >< Dup[@2](c, d)",
	    "Era[@1]() >< Era[@2]()",
	    "Constr[@1](a, b) >< Era[@2]()",
	    "Dup[@1](a, b) >< Era[@2]()",
	    "Constr[@1](a, b) >< Dup[@2](d, c)",
	    "Dup[@5](a, Constr[@6](d, @5#1, Dup[@4](b, @6#2, Constr[@7](c, @5#2, @4#2)#2)#1)#1, @7#1)",
	    "Dup[@1](a, b) >< Constr[@2](d, c)",
	    "Constr[@5](a, Dup[@6](d, @5#1, Constr[@4](b, @6#2, Dup[@7](c, @5#2, @4#2)#2)#1)#1, @7#1)",
        ];

        for case in cases {
            let parsed = parser::parser()
                .parse(parser::lexer().parse(case).unwrap())
                .unwrap();

            let builder = ReducerBuilder::default();
            let reducer = builder.with_init_net(&parsed[0].0).finish();

            let res = reducer.readback();

            assert_eq!(res[0].to_string(), parsed[0].to_string());
        }
    }

    #[test_log::test]
    fn test_reduce_matrix() {
        let cases = [
            (
                "Constr[@1](a, b) >< Constr[@2](c, d)",
                BTreeSet::from_iter(["c ~ a", "d ~ b"]),
            ),
            ("Dup[@1](a, b) >< Dup[@2](c, d)", BTreeSet::from_iter(["c ~ a", "d ~ b"])),
            ("Era[@1]() >< Era[@2]()", BTreeSet::from_iter([])),
            (
                "Constr[@1](a, b) >< Era[@2]()",
                BTreeSet::from_iter(["Era[@4](a)", "Era[@5](b)"]),
            ),
            (
                "Dup[@1](a, b) >< Era[@2]()",
                BTreeSet::from_iter(["Era[@4](a)", "Era[@5](b)"]),
            ),
            (
                "Constr[@1](a, b) >< Dup[@2](d, c)",
                BTreeSet::from_iter(["Dup[@6](a, Constr[@9](d, @6#1, Dup[@7](b, @9#2, Constr[@8](c, @6#2, @7#2)#2)#1)#1, @8#1)"]),
            ),
            (
                "Dup[@1](a, b) >< Constr[@2](d, c)",
                BTreeSet::from_iter(["Constr[@9](a, Dup[@6](d, @9#1, Constr[@8](b, @6#2, Dup[@7](c, @9#2, @8#2)#2)#1)#1, @7#1)"]),
            ),
        ];

        for (case, expected) in cases {
            let parsed = parser::parser()
                .parse(parser::lexer().parse(case).unwrap())
                .unwrap();

            let builder = ReducerBuilder::default();
            let mut reducer = builder.with_init_net(&parsed[0].0).finish();

            let res = reducer.reduce();

            assert_eq!(
                res.iter()
                    .map(|x| x.orient().to_string())
                    .collect::<BTreeSet<_>>(),
                expected
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<BTreeSet<_>>(),
            );
        }
    }
}
