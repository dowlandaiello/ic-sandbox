use super::{Cell, Conn, Ptr, Reducer as TraitReducer};
use crate::parser::{
    ast_combinators::{Constructor, Duplicator, Eraser, Expr, Port, Var},
    ast_lafont::Ident,
    naming::NameIter,
};
use crossbeam::atomic::AtomicCell;
use lockfree::queue::Queue;
#[cfg(feature = "threadpool")]
use rayon::iter::{IntoParallelIterator, ParallelDrainRange, ParallelIterator};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    sync::{atomic::AtomicUsize, Arc},
};

pub fn reduce_dyn(e: &Port) -> Vec<Port> {
    let mut reducer = Reducer::new([e].into_iter());
    reducer.reduce();

    reducer.readback()
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct OwnedCell {
    kind: Cell,
    primary_port: Option<Conn>,
    aux_ports: [Option<Conn>; 2],
}

impl OwnedCell {
    #[tracing::instrument]
    fn connect(
        lhs_cell: &mut OwnedCell,
        lhs_cell_id: usize,
        lhs_port: u8,
        rhs_cell: &mut OwnedCell,
        rhs_cell_id: usize,
        rhs_port: u8,
    ) {
        tracing::trace!("connecting");

        lhs_cell.set_port_i(
            lhs_port,
            Some(Conn {
                cell: rhs_cell_id,
                port: rhs_port,
            }),
        );
        rhs_cell.set_port_i(
            rhs_port,
            Some(Conn {
                cell: lhs_cell_id,
                port: lhs_port,
            }),
        );
    }

    fn make_constr() -> Self {
        Self {
            kind: Cell::Constr,
            primary_port: None,
            aux_ports: [const { None }; 2],
        }
    }

    fn make_era() -> Self {
        Self {
            kind: Cell::Era,
            primary_port: None,
            aux_ports: [const { None }; 2],
        }
    }

    fn make_dup() -> Self {
        Self {
            kind: Cell::Dup,
            primary_port: None,
            aux_ports: [const { None }; 2],
        }
    }

    fn set_port_i(&mut self, i: u8, val: Option<Conn>) {
        match i {
            0 => {
                self.primary_port = val;
            }
            1 => {
                self.aux_ports[0] = val;
            }
            2 => {
                self.aux_ports[1] = val;
            }
            _ => unreachable!(),
        }
    }
}

#[derive(Clone)]
pub struct Reducer {
    cells: Arc<[AtomicCell<Option<OwnedCell>>]>,
    len: Arc<AtomicUsize>,
    next_free: Arc<Queue<usize>>,
    root_redexes: Vec<(Conn, Conn)>,
    idents: BTreeMap<Ptr, String>,
    names: BTreeMap<Ptr, usize>,
}

impl Reducer {
    pub fn new<'a>(nets: impl Iterator<Item = &'a Port> + Clone) -> Self {
        let n_nodes = nets.clone().map(|net| net.iter_tree().count()).sum();

        let cells = (0..n_nodes * n_nodes)
            .map(|_| AtomicCell::new(None))
            .collect::<Vec<_>>();
        let next_free = Arc::new(Queue::from_iter(n_nodes..(n_nodes * n_nodes)));
        let mut names: BTreeMap<usize, usize> = Default::default();
        let mut idents: BTreeMap<usize, String> = Default::default();
        let mut redexes: BTreeSet<BTreeSet<usize>> = Default::default();

        let cells_for_ast_elems: BTreeMap<usize, RefCell<(OwnedCell, Ptr)>> = nets
            .clone()
            .map(|net| {
                net.iter_tree()
                    .enumerate()
                    .map(|(i, elem)| {
                        names.insert(i, elem.id);

                        let discriminant = match &*elem.borrow() {
                            Expr::Constr(_) => Cell::Constr,
                            Expr::Dup(_) => Cell::Dup,
                            Expr::Era(_) => Cell::Era,
                            Expr::Var(ident) => {
                                idents.insert(i, ident.name.to_string());

                                Cell::Var(i)
                            }
                        };

                        (
                            elem.id,
                            RefCell::new((
                                OwnedCell {
                                    kind: discriminant,
                                    aux_ports: [const { None }; 2],
                                    primary_port: None,
                                },
                                i,
                            )),
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .flatten()
            .collect();

        // Wire nodes
        nets.for_each(|net| {
            net.iter_tree().for_each(|elem| {
                let mut cell_cell_idx = cells_for_ast_elems.get(&elem.id).unwrap().borrow_mut();
                let idx = cell_cell_idx.1;

                tracing::trace!("walking expr {:?} for linking", elem);

                elem.iter_ports()
                    .into_iter()
                    .enumerate()
                    .filter_map(|(i, x)| Some((i, x?)))
                    .for_each(|(port_self, (port_other, p))| {
                        let mut other_cell_cell_idx =
                            cells_for_ast_elems.get(&p.id).unwrap().borrow_mut();
                        let other_idx = other_cell_cell_idx.1;

                        if port_other == 0 && port_self == 0 {
                            redexes.insert(BTreeSet::from_iter([
                                cell_cell_idx.1,
                                other_cell_cell_idx.1,
                            ]));
                        }

                        OwnedCell::connect(
                            &mut cell_cell_idx.0,
                            idx,
                            port_self as u8,
                            &mut other_cell_cell_idx.0,
                            other_idx,
                            port_other as u8,
                        );

                        tracing::trace!(
                            "connected: {:?} ~ {:?}",
                            cell_cell_idx,
                            other_cell_cell_idx
                        );
                    });
            });
        });

        // Commit cells
        cells_for_ast_elems
            .into_iter()
            .map(|(_, v)| v)
            .for_each(|x| {
                let (v, i) = x.into_inner();

                cells[i].swap(Some(v));
            });

        Self {
            cells: cells.into(),
            len: Arc::new(AtomicUsize::new(n_nodes)),
            next_free,
            names,
            idents,
            root_redexes: redexes
                .into_iter()
                .map(|x| {
                    let mut iter = x.into_iter();

                    (
                        Conn {
                            cell: iter.next().unwrap(),
                            port: 0,
                        },
                        Conn {
                            cell: iter.next().unwrap(),
                            port: 0,
                        },
                    )
                })
                .collect(),
        }
    }

    #[tracing::instrument(skip(self))]
    fn connect(&self, redexes: &mut Vec<(Conn, Conn)>, lhs: Conn, rhs: Conn) {
        tracing::trace!("connecting");

        let _ = self.cells[lhs.cell].fetch_update(|lhs_cell| {
            let mut cell_lhs = lhs_cell.unwrap();

            let _ = self.cells[rhs.cell].fetch_update(|rhs_cell| {
                let mut cell = rhs_cell.unwrap();
                cell.set_port_i(rhs.port, Some(lhs));

                if lhs.port == 0
                    && rhs.port == 0
                    && !matches!(cell_lhs.kind, Cell::Var(_))
                    && !matches!(cell.kind, Cell::Var(_))
                {
                    redexes.push((lhs, rhs));
                }

                Some(Some(cell))
            });

            cell_lhs.set_port_i(lhs.port, Some(rhs));

            Some(Some(cell_lhs))
        });
    }

    fn get_next_free(&self) -> usize {
        self.next_free.pop().unwrap()
    }

    fn make_commutation_era(&self, a: OwnedCell) {
        let mut eras = [
            (self.get_next_free(), OwnedCell::make_era()),
            (self.get_next_free(), OwnedCell::make_era()),
        ];

        let top_left_arg = a.aux_ports[0].unwrap();
        let top_right_arg = a.aux_ports[1].unwrap();

        let _ = self.cells[top_left_arg.cell].fetch_update(|top_left_cell| {
            let mut top_left_cell = top_left_cell.unwrap();

            OwnedCell::connect(
                &mut top_left_cell,
                top_left_arg.cell,
                top_left_arg.port,
                &mut eras[0].1,
                eras[0].0,
                0,
            );

            self.cells[eras[0].0].swap(Some(eras[0].1));

            Some(Some(top_left_cell))
        });

        let _ = self.cells[top_right_arg.cell].fetch_update(|top_right_cell| {
            let mut top_right_cell = top_right_cell.unwrap();

            OwnedCell::connect(
                &mut top_right_cell,
                top_right_arg.cell,
                top_right_arg.port,
                &mut eras[1].1,
                eras[1].0,
                0,
            );

            self.cells[eras[1].0].swap(Some(eras[1].1));

            Some(Some(top_right_cell))
        });
    }

    fn make_commutation(&self, a: OwnedCell, b: OwnedCell) {
        // left to right
        let mut dups = [
            (self.get_next_free(), OwnedCell::make_dup()),
            (self.get_next_free(), OwnedCell::make_dup()),
        ];
        let mut constrs = [
            (self.get_next_free(), OwnedCell::make_constr()),
            (self.get_next_free(), OwnedCell::make_constr()),
        ];

        // Internal conns
        // Outer internal conns
        OwnedCell::connect(
            &mut dups[0].1,
            dups[0].0,
            2,
            &mut constrs[0].1,
            constrs[0].0,
            1,
        );
        OwnedCell::connect(
            &mut dups[1].1,
            dups[1].0,
            1,
            &mut constrs[1].1,
            constrs[1].0,
            2,
        );

        // Inner internal conns
        OwnedCell::connect(
            &mut dups[0].1,
            dups[0].0,
            1,
            &mut constrs[1].1,
            constrs[1].0,
            1,
        );
        OwnedCell::connect(
            &mut dups[1].1,
            dups[1].0,
            2,
            &mut constrs[0].1,
            constrs[0].0,
            2,
        );

        let top_left_arg = a.aux_ports[0].unwrap();
        let top_right_arg = a.aux_ports[1].unwrap();

        let bot_left_arg = b.aux_ports[1].unwrap();
        let bot_right_arg = b.aux_ports[0].unwrap();

        // External conns
        let _ = self.cells[top_left_arg.cell].fetch_update(|top_left_cell| {
            let mut top_left_cell = top_left_cell.unwrap();

            OwnedCell::connect(
                &mut top_left_cell,
                top_left_arg.cell,
                top_left_arg.port,
                &mut dups[0].1,
                dups[0].0,
                0,
            );

            self.cells[dups[0].0].swap(Some(dups[0].1));

            Some(Some(top_left_cell))
        });

        let _ = self.cells[top_right_arg.cell].fetch_update(|top_right_cell| {
            let mut top_right_cell = top_right_cell.unwrap();

            OwnedCell::connect(
                &mut top_right_cell,
                top_right_arg.cell,
                top_right_arg.port,
                &mut dups[1].1,
                dups[1].0,
                0,
            );

            self.cells[dups[1].0].swap(Some(dups[1].1));

            Some(Some(top_right_cell))
        });

        let _ = self.cells[bot_left_arg.cell].fetch_update(|bot_left_cell| {
            let mut bot_left_cell = bot_left_cell.unwrap();

            OwnedCell::connect(
                &mut bot_left_cell,
                bot_left_arg.cell,
                bot_left_arg.port,
                &mut constrs[0].1,
                constrs[0].0,
                0,
            );

            self.cells[constrs[0].0].swap(Some(constrs[0].1));

            Some(Some(bot_left_cell))
        });

        let _ = self.cells[bot_right_arg.cell].fetch_update(|bot_right_cell| {
            let mut bot_right_cell = bot_right_cell.unwrap();

            OwnedCell::connect(
                &mut bot_right_cell,
                bot_right_arg.cell,
                bot_right_arg.port,
                &mut constrs[1].1,
                constrs[1].0,
                0,
            );

            self.cells[constrs[1].0].swap(Some(constrs[1].1));

            Some(Some(bot_right_cell))
        });
    }

    #[tracing::instrument(skip(self))]
    fn reduce_step_raw(&self, redex: (Conn, Conn)) -> Vec<(Conn, Conn)> {
        let mut redexes = Vec::default();

        let a_id = redex.0.cell;
        let b_id = redex.1.cell;

        let (a, b) = (
            self.cells[a_id].take().unwrap(),
            self.cells[b_id].take().unwrap(),
        );

        tracing::debug!("reducing {} ({}) >< {} ({})", a.kind, a_id, b.kind, b_id);

        match (a.kind, b.kind) {
            // Annihilation of alpha-alpha
            (Cell::Constr, Cell::Constr) | (Cell::Dup, Cell::Dup) => {
                // Both left to right
                let top_ports = (a.aux_ports[0], a.aux_ports[1]);
                let bot_ports = (b.aux_ports[1], b.aux_ports[0]);

                self.connect(&mut redexes, top_ports.0.unwrap(), bot_ports.1.unwrap());
                self.connect(&mut redexes, top_ports.1.unwrap(), bot_ports.0.unwrap());
            }
            // Annihilation of Era
            (Cell::Era, Cell::Era) => {
                // Nothing to do. Just delete.
            }
            // Commutation of constr dup
            (Cell::Constr, Cell::Dup) => {
                // Top is left to right, bottom is right to left
                self.make_commutation(a, b);
            }
            // Commutation of dup constr
            (Cell::Dup, Cell::Constr) => {
                self.make_commutation(b, a);
            }
            // Commutation of alpha era
            (Cell::Constr, Cell::Era) | (Cell::Dup, Cell::Era) => {
                self.make_commutation_era(a);
            }
            (Cell::Era, Cell::Constr) | (Cell::Era, Cell::Dup) => {
                self.make_commutation_era(b);
            }
            _ => {
                panic!("invalid redex")
            }
        }

        redexes
    }
}

impl TraitReducer for Reducer {
    fn readback(&self) -> Vec<Port> {
        tracing::debug!("reading back");

        let new_names = NameIter::starting_from(self.names.len());

        let cells = self
            .cells
            .iter()
            .enumerate()
            .map(|(i, x)| (i, x.take()))
            .filter_map(|(i, maybe_x)| Some((i, maybe_x?)))
            .collect::<BTreeMap<Ptr, _>>();

        // Make ports before linking, link later
        let ports_for_cells: BTreeMap<Ptr, Port> = cells
            .iter()
            .map(|(i, cell)| {
                let name = self
                    .names
                    .get(&i)
                    .map(|x| *x)
                    .unwrap_or_else(|| new_names.next_id());

                let expr = match cell.kind {
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

                (*i, expr)
            })
            .collect();

        // Link them
        ports_for_cells.iter().for_each(|(i, entry)| {
            tracing::trace!("walking cell {} (expr: {}) for linking", i, entry);

            let cell = cells[i];

            let mut ports = [cell.primary_port]
                .into_iter()
                .chain(cell.aux_ports.into_iter());

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
        ports_for_cells
            .into_iter()
            .map(|(_, cell)| {
                (
                    cell.iter_tree()
                        .map(|x| x.borrow().description())
                        .collect::<BTreeSet<_>>(),
                    cell,
                )
            })
            .collect::<BTreeMap<_, _>>()
            .into_iter()
            .map(|(_, cell)| cell.orient())
            .collect::<Vec<_>>()
    }

    fn reduce(&mut self) -> Vec<Port> {
        #[cfg(feature = "threadpool")]
        fn reduce_redexes(buffer: Reducer, r: impl ParallelIterator<Item = (Conn, Conn)>) {
            r.into_par_iter().for_each(move |x| {
                let redexes = buffer.reduce_step_raw(x);

                reduce_redexes(buffer.clone(), redexes.into_par_iter());
            });
        }

        #[cfg(not(feature = "threadpool"))]
        fn reduce_redexes(buffer: Reducer, r: impl Iterator<Item = (Conn, Conn)>) {
            r.into_iter().for_each(move |x| {
                let redexes = buffer.reduce_step_raw(x);

                reduce_redexes(buffer.clone(), redexes.into_iter());
            });
        }

        // Push all redexes
        #[cfg(feature = "threadpool")]
        reduce_redexes(self.clone(), self.root_redexes.par_drain(..));

        #[cfg(not(feature = "threadpool"))]
        reduce_redexes(self.clone(), self.root_redexes.drain(..));

        self.readback()
    }

    fn reduce_step(&self, redex: (Conn, Conn)) {
        self.reduce_step_raw(redex);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::parser_combinators as parser;
    use chumsky::Parser;

    #[test_log::test]
    fn test_readback_crossbeam() {
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

            let reducer = Reducer::new([&parsed[0].0].into_iter());

            let res = reducer.readback();

            assert_eq!(res[0].to_string(), parsed[0].to_string());
        }
    }

    #[test_log::test]
    fn test_reduce_crossbeam() {
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

            let mut reducer = Reducer::new([&parsed[0].0].into_iter());
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
