use super::{
    super::{super::Reducer, Conn, NetBuffer, Ptr},
    atomic_reprs::CellRepr,
    matrix_buffer::MatrixBuffer,
    Cell,
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
    iter::DoubleEndedIterator,
    sync::atomic::AtomicBool,
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

                        cell_self.store_port_i(
                            port_self as u8,
                            Some(Conn {
                                cell: *other_slot,
                                port: port_other as u8,
                            })
                            .into(),
                        );

                        let cell_other = buff.get_cell(*other_slot);

                        cell_other.store_port_i(
                            port_other as u8,
                            Some(Conn {
                                cell: *slot,
                                port: port_self as u8,
                            })
                            .into(),
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
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .ok()
            .map(|_| ())
    }

    fn mark_unlocked(&self, cell: Ptr) {
        self.locked[cell].store(false, Ordering::SeqCst);
    }

    fn lock(&self, cell: Ptr) -> Option<()> {
        while self.mark_locked(cell).is_none() {}

        Some(())
    }

    fn try_lock(&self, cell: Ptr) -> Option<()> {
        self.mark_locked(cell)
    }

    fn conn_maybe_redex(&self, a: (Conn, &CellRepr), b: (Conn, &CellRepr)) -> Option<(Conn, Conn)> {
        tracing::trace!("linking {} ~ {}", a.0, b.0);

        let (a_conn, a_cell) = a;
        let (b_conn, b_cell) = b;

        a_cell.store_port_i(a_conn.port, Some(b_conn));
        b_cell.store_port_i(b_conn.port, Some(a_conn));

        if a_conn.port == 0
            && b_conn.port == 0
            && !matches!(a_cell.load_discriminant_uninit_var().unwrap(), Cell::Var(_))
            && !matches!(b_cell.load_discriminant_uninit_var().unwrap(), Cell::Var(_))
        {
            tracing::trace!(
                "found new redex cell {} >< cell {}",
                a_conn.cell,
                b_conn.cell
            );

            return Some((a_conn, b_conn));
        }

        None
    }

    fn conn_maybe_circular<'a>(
        top_id: Ptr,
        bot_id: Ptr,
        mut top_ports: impl Iterator<Item = Conn>,
        mut bot_ports: impl Iterator<Item = Conn>,
    ) -> Option<(Conn, Conn)> {
        let top_left = top_ports.next()?;
        let top_right = top_ports.next()?;
        let bot_left = bot_ports.next()?;
        let bot_right = bot_ports.next()?;

        if top_left.cell == top_right.cell && top_left.cell == top_id {
            return Some((bot_left, bot_right));
        }

        if bot_left.cell == bot_right.cell && bot_right.cell == bot_id {
            return Some((top_left, top_right));
        }

        None
    }

    #[tracing::instrument(skip(self))]
    fn reduce_step(&self, redex: (Conn, Conn)) -> Vec<(Conn, Conn)> {
        let a_id = redex.0.cell;
        let b_id = redex.1.cell;

        let mut maybe_to_lock = None;

        loop {
            if a_id < b_id {
                self.lock(a_id);
                self.lock(b_id);
            } else {
                self.lock(b_id);
                self.lock(a_id);
            }

            let pair = (self.buffer.get_cell(a_id), self.buffer.get_cell(b_id));

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

            if a_id < b_id {
                self.mark_unlocked(a_id);
                self.mark_unlocked(b_id);
            } else {
                self.mark_unlocked(b_id);
                self.mark_unlocked(a_id);
            }

            // Ensure no lessser numbered cells are locked
            if self
                .locked
                .iter()
                .take(*maybe_to_lock.as_ref().unwrap().iter().next().unwrap())
                .any(|is_locked| is_locked.load(Ordering::SeqCst))
            {
                continue;
            }

            let mut locked_cells = Vec::new();
            let lock_failures = maybe_to_lock
                .as_ref()
                .unwrap()
                .iter()
                .try_for_each(|&cell_id| {
                    if self.try_lock(cell_id).is_some() {
                        locked_cells.push(cell_id);
                        Ok(())
                    } else {
                        Err(cell_id)
                    }
                });

            // If any lock failed, release all acquired locks and retry
            if lock_failures.is_err() {
                for &cell_id in &locked_cells {
                    self.mark_unlocked(cell_id);
                }

                continue;
            }

            break;
        }

        let to_lock = maybe_to_lock.unwrap();

        let a_cell = self.buffer.get_cell(a_id);
        let b_cell = self.buffer.get_cell(b_id);

        tracing::debug!("reducing {} >< {}", a_id, b_id);

        let a_discriminant = a_cell.load_discriminant_uninit_var().unwrap();
        let b_discriminant = b_cell.load_discriminant_uninit_var().unwrap();

        tracing::debug!(
            "reducing {} ({}) >< {} ({})",
            a_discriminant,
            a_id,
            b_discriminant,
            b_id
        );

        let map_conn = |c: Conn| (c, self.buffer.get_cell(c.cell));

        let new_redexes = match (a_discriminant, b_discriminant) {
            // Annihilation of alpha-alpha
            (Cell::Constr, Cell::Constr) | (Cell::Dup, Cell::Dup) => {
                // Handle circular conn
                if let Some((a, b)) = Self::conn_maybe_circular(
                    a_id,
                    b_id,
                    a_cell.iter_aux_ports().map(|x| x.unwrap()),
                    b_cell.iter_aux_ports().map(|x| x.unwrap()),
                ) {
                    [self.conn_maybe_redex(map_conn(a), map_conn(b))]
                        .into_iter()
                        .filter_map(|x| x)
                        .collect()
                } else {
                    let (top_ports, bottom_ports) = (
                        a_cell.iter_aux_ports().map(|x| x.unwrap()).map(map_conn),
                        b_cell.iter_aux_ports().map(|x| x.unwrap()).map(map_conn),
                    );

                    // Remember, bottom ports is flipped due to orientation
                    top_ports
                        .into_iter()
                        .zip(bottom_ports)
                        .map(|(a, b)| self.conn_maybe_redex(a, b))
                        .filter_map(|x| x)
                        .collect()
                }
            }
            // Annihilation of Era
            (Cell::Era, Cell::Era) => Default::default(),
            // Commutation of constr dup
            (Cell::Constr, Cell::Dup) => {
                // Top is left to right, bottom is right to left
                let (top_ports, bottom_ports) = (
                    a_cell.iter_aux_ports().map(|x| x.unwrap()).map(map_conn),
                    b_cell.iter_aux_ports().map(|x| x.unwrap()).map(map_conn),
                );

                self.make_commutation(a_id, b_id, top_ports, bottom_ports)
            }
            // Commutation of dup constr
            (Cell::Dup, Cell::Constr) => {
                let (top_ports, bottom_ports) = (
                    b_cell.iter_aux_ports().map(|x| x.unwrap()).map(map_conn),
                    a_cell.iter_aux_ports().map(|x| x.unwrap()).map(map_conn),
                );

                self.make_commutation(b_id, a_id, top_ports, bottom_ports)
            }
            // Commutation of alpha era
            (Cell::Constr, Cell::Era) | (Cell::Dup, Cell::Era) => {
                let top_ports = a_cell.iter_aux_ports().map(|x| x.unwrap()).map(map_conn);
                let mut ports_2 = a_cell.iter_aux_ports().map(|x| x.unwrap()).map(map_conn);

                // Circular elim
                if ports_2.next().unwrap().0.cell == a_id && ports_2.next().unwrap().0.cell == a_id
                {
                    let eras = [self.buffer.push(Cell::Era), self.buffer.push(Cell::Era)];
                    self.conn_maybe_redex(
                        (
                            Conn {
                                port: 0,
                                cell: eras[0],
                            },
                            self.buffer.get_cell(eras[0]),
                        ),
                        (
                            Conn {
                                port: 0,
                                cell: eras[1],
                            },
                            self.buffer.get_cell(eras[1]),
                        ),
                    )
                    .map(|redex| vec![redex])
                    .unwrap_or_default()
                } else {
                    self.make_era_commutation(top_ports)
                }
            }
            (Cell::Era, Cell::Constr) | (Cell::Era, Cell::Dup) => {
                let top_ports = b_cell.iter_aux_ports().map(|x| x.unwrap()).map(map_conn);
                let mut ports_2 = b_cell.iter_aux_ports().map(|x| x.unwrap()).map(map_conn);

                // Circular elim
                if ports_2.next().unwrap().0.cell == b_id && ports_2.next().unwrap().0.cell == b_id
                {
                    let eras = [self.buffer.push(Cell::Era), self.buffer.push(Cell::Era)];
                    self.conn_maybe_redex(
                        (
                            Conn {
                                port: 0,
                                cell: eras[0],
                            },
                            self.buffer.get_cell(eras[0]),
                        ),
                        (
                            Conn {
                                port: 0,
                                cell: eras[1],
                            },
                            self.buffer.get_cell(eras[1]),
                        ),
                    )
                    .map(|redex| vec![redex])
                    .unwrap_or_default()
                } else {
                    self.make_era_commutation(top_ports)
                }
            }
            _ => {
                panic!("invalid redex")
            }
        };

        tracing::trace!("deleting cell {}", a_id);
        tracing::trace!("deleting cell {}", b_id);

        a_cell.wipe();
        b_cell.wipe();

        to_lock.iter().for_each(|cell_id| {
            self.mark_unlocked(*cell_id);
        });

        self.buffer.push_next_free(a_id);
        self.buffer.push_next_free(b_id);

        new_redexes
            .into_iter()
            .map(|(a, b)| BTreeSet::from_iter([a, b]))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .map(|mut x| (x.pop_first().unwrap(), x.pop_first().unwrap()))
            .collect::<Vec<_>>()
    }

    fn make_era_commutation<'a>(
        &'a self,
        top_ports: impl Iterator<Item = (Conn, &'a CellRepr)> + 'a,
    ) -> Vec<(Conn, Conn)> {
        let eras = [self.buffer.push(Cell::Era), self.buffer.push(Cell::Era)];

        top_ports
            .zip(
                eras.into_iter()
                    .map(|ptr| ((ptr, 0).into(), self.buffer.get_cell(ptr))),
            )
            .map(|(a, b)| self.conn_maybe_redex(a, (b.0, b.1)))
            .filter_map(|x| x)
            .collect()
    }

    fn make_commutation<'a>(
        &'a self,
        a_id: Ptr,
        b_id: Ptr,
        top_ports: impl DoubleEndedIterator<Item = (Conn, &'a CellRepr)> + Clone + 'a,
        bottom_ports: impl DoubleEndedIterator<Item = (Conn, &'a CellRepr)> + Clone + 'a,
    ) -> Vec<(Conn, Conn)> {
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

        let mut redexes = Vec::new();

        let conn_map: BTreeMap<Conn, Conn> = [
            Conn {
                cell: a_id,
                port: 1,
            },
            Conn {
                cell: a_id,
                port: 2,
            },
        ]
        .into_iter()
        .zip(dups.into_iter().map(|ptr| Conn { cell: ptr, port: 0 }))
        .chain(
            [
                Conn {
                    cell: b_id,
                    port: 1,
                },
                Conn {
                    cell: b_id,
                    port: 2,
                },
            ]
            .into_iter()
            .rev()
            .zip(constrs.into_iter().map(|ptr| Conn { cell: ptr, port: 0 })),
        )
        .collect();

        redexes.extend::<Vec<(Conn, Conn)>>(
            top_ports
                .map(|conn| conn_map.get(&conn.0).cloned().unwrap_or(conn.0))
                .zip(dups.into_iter().map(|ptr| Conn { cell: ptr, port: 0 }))
                .map(|(a, b)| {
                    let a_cell = self.buffer.get_cell(a.cell);
                    let b_cell = self.buffer.get_cell(b.cell);

                    self.conn_maybe_redex((a, a_cell), (b, b_cell))
                })
                .filter_map(|x| x)
                .collect(),
        );
        redexes.extend::<Vec<(Conn, Conn)>>(
            bottom_ports
                .map(|conn| conn_map.get(&conn.0).cloned().unwrap_or(conn.0))
                .rev()
                .zip(constrs.into_iter().map(|ptr| Conn { cell: ptr, port: 0 }))
                .map(|(a, b)| {
                    let a_cell = self.buffer.get_cell(a.cell);
                    let b_cell = self.buffer.get_cell(b.cell);

                    self.conn_maybe_redex((a, a_cell), (b, b_cell))
                })
                .filter_map(|x| x)
                .collect(),
        );

        redexes.extend::<Vec<(Conn, Conn)>>(
            conns
                .into_iter()
                .map(|(a, b)| {
                    let a_cell = self.buffer.get_cell(a.0);
                    let b_cell = self.buffer.get_cell(b.0);

                    self.conn_maybe_redex((a.into(), a_cell), (b.into(), b_cell))
                })
                .filter_map(|x| x)
                .collect(),
        );

        redexes
    }
}

impl Reducer for BufferedMatrixReducer {
    fn readback(&self) -> Vec<Port> {
        tracing::debug!("reading back");

        let new_names = NameIter::default();

        // Make ports before linking, link later
        let mut ports_for_cells: BTreeMap<Ptr, Port> = self
            .buffer
            .iter_cells_discriminants()
            .map(|(i, discriminant)| {
                let name = new_names.next_id();

                let expr = match discriminant {
                    Cell::Constr => Expr::Constr(Constructor::new()).into_port_named(name),
                    Cell::Dup => Expr::Dup(Duplicator::new()).into_port_named(name),
                    Cell::Era => Expr::Era(Eraser::new()).into_port_named(name),
                    Cell::Var(_) => {
                        let v = i;

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
        fn reduce_redexes(slf: &mut BufferedMatrixReducer, mut r: Vec<(Conn, Conn)>) {
            while !r.is_empty() {
                let res = slf.readback();

                tracing::debug!(
                    "reduction frame: {}",
                    res.into_iter()
                        .map(|graph| graph.iter_tree_visitor().into_string())
                        .collect::<Vec<_>>()
                        .join("\n")
                );

                let lock = slf.locked.clone();

                let n_empty_cells_required = r.len() * 4;

                let free_cells_reduction = slf
                    .buffer
                    .iter_pop_next_free()
                    .take(n_empty_cells_required)
                    .collect::<Vec<_>>();

                free_cells_reduction
                    .iter()
                    .for_each(|x| slf.buffer.push_next_free(*x));

                if free_cells_reduction.len() < n_empty_cells_required {
                    slf.buffer.grow(n_empty_cells_required);
                    slf.locked = slf
                        .locked
                        .iter()
                        .map(|x| AtomicBool::new(x.load(Ordering::SeqCst)))
                        .chain((0..n_empty_cells_required).map(|_| AtomicBool::default()))
                        .collect();
                }

                let buff = slf.buffer.clone();

                r = r
                    .into_par_iter()
                    .map(move |x| {
                        let worker = ReductionWorker {
                            buffer: buff.clone(),
                            locked: lock.clone(),
                        };

                        worker.reduce_step(x)
                    })
                    .flatten()
                    .collect();
            }
        }

        #[cfg(not(feature = "threadpool"))]
        fn reduce_redexes(slf: &BufferedMatrixReducer, r: impl IntoIterator<Item = (Conn, Conn)>) {
            r.into_iter().for_each(move |x| {
                let res = slf.readback();

                tracing::debug!(
                    "reduction frame: {}",
                    res.into_iter()
                        .map(|graph| graph.iter_tree_visitor().into_string())
                        .collect::<Vec<_>>()
                        .join("\n")
                );

                let worker = ReductionWorker {
                    buffer: slf.buffer.clone(),
                    locked: slf.locked.clone(),
                };

                let redexes = worker.reduce_step(x);

                slf.buffer.checksum();

                reduce_redexes(slf, redexes);
            });
        }

        // Push all redexes
        #[cfg(feature = "threadpool")]
        {
            let redexes = self.root_redexes.par_drain(..).collect();

            reduce_redexes(self, redexes);
        }

        #[cfg(not(feature = "threadpool"))]
        {
            let redexes = self.root_redexes.drain(..).collect::<Vec<_>>();

            reduce_redexes(self, redexes);
        }

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
	    ("Constr[@1](a, b) >< Constr[@2](c, d)", "Constr[@0](a, b) >< Constr[@1](c, d)"),
	    ("Dup[@1](a, b) >< Dup[@2](c, d)", "Dup[@0](a, b) >< Dup[@1](c, d)"),
	    ("Era[@1]() >< Era[@2]()", "Era[@0]() >< Era[@1]()"),
	    ("Constr[@1](a, b) >< Era[@2]()", "Constr[@0](a, b) >< Era[@1]()"),
            ("Dup[@1](a, b) >< Era[@2]()", "Dup[@0](a, b) >< Era[@1]()"),
            ("Constr[@1](a, b) >< Dup[@2](d, c)", "Constr[@0](a, b) >< Dup[@1](d, c)"),
            (
                "Dup[@5](a, Constr[@6](d, @5#1, Dup[@4](b, @6#2, Constr[@7](c, @5#2, @4#2)#2)#1)#1, @7#1)",
                "Dup[@0](a, Constr[@2](d, @0#1, Dup[@5](b, @2#2, Constr[@3](c, @0#2, @5#2)#2)#1)#1, @3#1)"
            ),
            ("Dup[@1](a, b) >< Constr[@2](d, c)", "Dup[@0](a, b) >< Constr[@1](d, c)"),
            (
                "Constr[@5](a, Dup[@6](d, @5#1, Constr[@4](b, @6#2, Dup[@7](c, @5#2, @4#2)#2)#1)#1, @7#1)",
		"Constr[@0](a, Dup[@2](d, @0#1, Constr[@5](b, @2#2, Dup[@3](c, @0#2, @5#2)#2)#1)#1, @3#1)"
            ),
	];

        for (case, expected) in cases {
            let parsed = parser::parser()
                .parse(parser::lexer().parse(case).unwrap())
                .unwrap();

            let builder = ReducerBuilder::default();
            let reducer = builder.with_init_net(&parsed[0].0).finish();

            let res = reducer.readback();

            assert_eq!(res[0].to_string(), expected);
        }
    }

    #[test_log::test]
    fn test_reduce_matrix() {
        let cases = [
            (
                "Constr[@1](a, b) >< Constr[@2](c, d)",
                BTreeSet::from_iter(["a ~ c", "b ~ d"]),
            ),
            ("Dup[@1](a, b) >< Dup[@2](c, d)", BTreeSet::from_iter(["a ~ c", "b ~ d"])),
            ("Era[@1]() >< Era[@2]()", BTreeSet::from_iter([])),
            (
                "Constr[@1](a, b) >< Era[@2]()",
                BTreeSet::from_iter(["a >< Era[@2]()", "b >< Era[@3]()"]),
            ),
            (
                "Dup[@1](a, b) >< Era[@2]()",
                BTreeSet::from_iter(["a >< Era[@2]()", "b >< Era[@3]()"]),
            ),
            (
                "Constr[@1](a, b) >< Dup[@2](d, c)",
                BTreeSet::from_iter(["a >< Dup[@4](Constr[@7](d, @4#1, Dup[@5](b, @7#2, Constr[@6](c, @4#2, @5#2)#2)#1)#1, @6#1)"]),
            ),
            (
                "Dup[@1](a, b) >< Constr[@2](d, c)",
                BTreeSet::from_iter(["a >< Constr[@7](Dup[@4](d, @7#1, Constr[@6](b, @4#2, Dup[@5](c, @7#2, @6#2)#2)#1)#1, @5#1)"]),
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
                res.iter().map(|x| x.to_string()).collect::<BTreeSet<_>>(),
                expected
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<BTreeSet<_>>(),
            );
        }
    }
}
