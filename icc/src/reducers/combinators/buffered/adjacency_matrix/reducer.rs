use super::{
    super::{super::Reducer, Conn, NetBuffer, Ptr},
    matrix_buffer::MatrixBuffer,
    Cell,
};
use crate::parser::{
    ast_combinators::{Constructor, Duplicator, Eraser, Expr, Port, Var},
    ast_lafont::Ident,
    naming::NameIter,
};
use rayon::{ThreadPool, ThreadPoolBuilder};
use std::{
    collections::{BTreeMap, BTreeSet},
    iter::DoubleEndedIterator,
    sync::mpsc::{self, Receiver, Sender},
};

macro_rules! conn_maybe_redex {
    ($self:ident, $a:expr, $b:expr) => {
        $self.buffer.connect($a, $b);

        if let Some((a, b)) = $a.zip($b) {
            if a.port == 0 && b.port == 0 {
                $self.tx_redexes.send((a, b)).unwrap();
            }
        }
    };
}

pub struct ReducerBuilder {
    tx_redexes: Sender<(Conn, Conn)>,

    #[cfg(feature = "threadpool")]
    pool: ThreadPoolBuilder,
}

impl ReducerBuilder {
    pub fn new_in_redex_loop() -> (Receiver<(Conn, Conn)>, Self) {
        let (tx, rx) = mpsc::channel();

        (
            rx,
            Self {
                tx_redexes: tx,
                #[cfg(feature = "threadpool")]
                pool: Default::default(),
            },
        )
    }

    #[cfg(feature = "threadpool")]
    pub fn with_threadpool_builder(mut self, builder: ThreadPoolBuilder) -> Self {
        self.pool = builder;

        self
    }

    pub fn with_init_net(self, net: &Port) -> CapacitiedBufferedMatrixReducerBuilder {
        let n_nodes = net.iter_tree().count();

        let buff = MatrixBuffer::new_with_capacity_nodes(n_nodes);

        let slots_for_ast_elems: BTreeMap<usize, usize> = net
            .iter_tree()
            .enumerate()
            .map(|(i, elem)| {
                let discriminant = match &*elem.borrow() {
                    Expr::Constr(_) => Cell::Constr,
                    Expr::Dup(_) => Cell::Dup,
                    Expr::Era(_) => Cell::Era,
                    Expr::Var(_) => Cell::Var(i),
                };

                (elem.id, buff.push(discriminant))
            })
            .collect();

        // Wire nodes
        net.iter_tree().for_each(|elem| {
            let slot = slots_for_ast_elems.get(&elem.id).unwrap();

            elem.iter_ports()
                .into_iter()
                .enumerate()
                .filter_map(|(i, x)| Some((i, x?)))
                .for_each(|(port_self, (port_other, p))| {
                    let other_slot = slots_for_ast_elems.get(&p.id).unwrap();

                    buff.connect(
                        Some(Conn {
                            cell: *slot,
                            port: port_self as u8,
                        }),
                        Some(Conn {
                            cell: *other_slot,
                            port: port_other as u8,
                        }),
                    );
                });
        });

        CapacitiedBufferedMatrixReducerBuilder {
            tx_redexes: self.tx_redexes,
            cells: buff,
            #[cfg(feature = "threadpool")]
            pool: self.pool,
        }
    }

    pub fn with_capacity_nodes(self, capacity: usize) -> CapacitiedBufferedMatrixReducerBuilder {
        CapacitiedBufferedMatrixReducerBuilder {
            tx_redexes: self.tx_redexes,
            cells: MatrixBuffer::new_with_capacity_nodes(capacity),
            #[cfg(feature = "threadpool")]
            pool: self.pool,
        }
    }
}

pub struct CapacitiedBufferedMatrixReducerBuilder {
    tx_redexes: Sender<(Conn, Conn)>,
    cells: MatrixBuffer,
    pool: ThreadPoolBuilder,
}

impl CapacitiedBufferedMatrixReducerBuilder {
    pub fn finish(self) -> BufferedMatrixReducer {
        BufferedMatrixReducer {
            tx_redexes: self.tx_redexes,
            buffer: self.cells,

            #[cfg(feature = "threadpool")]
            pool: self.pool.build().unwrap(),
        }
    }
}

pub struct BufferedMatrixReducer {
    tx_redexes: Sender<(Conn, Conn)>,
    buffer: MatrixBuffer,

    #[cfg(feature = "threadpool")]
    pool: ThreadPool,
}

#[derive(Clone)]
pub struct ReductionWorker {
    buffer: MatrixBuffer,
    tx_redexes: Sender<(Conn, Conn)>,
}

impl ReductionWorker {
    fn reduce_step(&self, redex: (Conn, Conn)) {
        let a_id = redex.0.cell;
        let b_id = redex.0.cell;

        let pair = (self.buffer.get_cell(a_id), self.buffer.get_cell(b_id));

        tracing::trace!("reducing {} >< {}", pair.0, pair.1);

        match pair {
            // Annihilation of alpha-alpha
            (Cell::Constr, Cell::Constr) | (Cell::Dup, Cell::Dup) => {
                let (top_ports, bottom_ports) =
                    (self.buffer.iter_ports(a_id), self.buffer.iter_ports(b_id));

                // Remember, bottom ports is flipped due to orientation
                top_ports.zip(bottom_ports).for_each(|(a, b)| {
                    conn_maybe_redex!(self, a, b);
                });
            }
            // Annihilation of Era
            (Cell::Era, Cell::Era) => {
                self.buffer.delete(a_id);
                self.buffer.delete(b_id);
            }
            // Commutation of constr dup
            (Cell::Constr, Cell::Dup) => {
                // Top is left to right, bottom is right to left
                let (top_ports, bottom_ports) =
                    (self.buffer.iter_ports(a_id), self.buffer.iter_ports(b_id));

                self.make_commutation(top_ports, bottom_ports);
            }
            // Commutation of dup constr
            (Cell::Dup, Cell::Constr) => {
                let (top_ports, bottom_ports) =
                    (self.buffer.iter_ports(b_id), self.buffer.iter_ports(a_id));

                self.make_commutation(top_ports, bottom_ports);
            }
            // Commutation of alpha era
            (Cell::Constr, Cell::Era) | (Cell::Dup, Cell::Era) => {
                let top_ports = self.buffer.iter_ports(a_id);

                self.make_era_commutation(top_ports);
            }
            (Cell::Era, Cell::Constr) | (Cell::Era, Cell::Dup) => {
                let top_ports = self.buffer.iter_ports(b_id);

                self.make_era_commutation(top_ports);
            }
            _ => {}
        }
    }

    fn make_era_commutation(&self, top_ports: impl Iterator<Item = Option<Conn>>) {
        let eras = [self.buffer.push(Cell::Era), self.buffer.push(Cell::Era)];

        top_ports
            .zip(eras.iter().map(|ptr| Some((*ptr, 0).into())))
            .for_each(|(a, b)| {
                conn_maybe_redex!(self, a, b);
            });
    }

    fn make_commutation(
        &self,
        top_ports: impl DoubleEndedIterator<Item = Option<Conn>>,
        bottom_ports: impl DoubleEndedIterator<Item = Option<Conn>>,
    ) {
        // left to right
        let dups = [self.buffer.push(Cell::Dup), self.buffer.push(Cell::Dup)];

        // Left to right
        let constrs = [
            self.buffer.push(Cell::Constr),
            self.buffer.push(Cell::Constr),
        ];

        top_ports
            .zip(dups.iter().map(|ptr| {
                Some(Conn {
                    cell: *ptr,
                    port: 0,
                })
            }))
            .for_each(|(a, b)| {
                conn_maybe_redex!(self, a, b);
            });
        bottom_ports
            .rev()
            .zip(constrs.iter().map(|ptr| {
                Some(Conn {
                    cell: *ptr,
                    port: 0,
                })
            }))
            .for_each(|(a, b)| {
                conn_maybe_redex!(self, a, b);
            });

        let conn_left = ((dups[0], 2), (constrs[0], 1));
        let conn_right = ((dups[1], 1), (constrs[1], 2));
        let conn_middle_left = ((dups[0], 1), (constrs[1], 1));
        let conn_middle_right = ((dups[1], 2), (constrs[0], 2));

        let conns = [conn_left, conn_right, conn_middle_left, conn_middle_right];

        conns.iter().for_each(|(a, b)| {
            conn_maybe_redex!(self, Some::<Conn>((*a).into()), Some::<Conn>((*b).into()));
        });
    }
}

impl BufferedMatrixReducer {
    #[cfg(feature = "threadpool")]
    fn dispatch_reduction(&self, redex: (Conn, Conn)) {
        let worker = ReductionWorker {
            buffer: self.buffer.clone(),
            tx_redexes: self.tx_redexes.clone(),
        };

        self.pool.spawn(move || worker.reduce_step(redex))
    }

    #[cfg(not(feature = "threadpool"))]
    fn dispatch_reduction(&self, redex: (Conn, Conn)) {
        self.reduce_step(redex);
    }
}

impl Reducer for BufferedMatrixReducer {
    fn push_active_pair(&self, lhs: Conn, rhs: Conn) {
        self.tx_redexes.send((lhs, rhs)).unwrap();
    }

    fn readback(&self) -> Vec<Port> {
        let mut names = NameIter::default();

        // Make ports before linking, link later
        let mut ports_for_cells: BTreeMap<Ptr, Port> = self
            .buffer
            .iter_cells()
            .map(|i| (i, self.buffer.get_cell(i)))
            .map(|(i, discriminant)| {
                (
                    i,
                    match discriminant {
                        Cell::Constr => Expr::Constr(Constructor::new()).into_port(&mut names),
                        Cell::Dup => Expr::Dup(Duplicator::new()).into_port(&mut names),
                        Cell::Era => Expr::Era(Eraser::new()).into_port(&mut names),
                        Cell::Var(v) => Expr::Var(Var {
                            name: Ident(v.to_string()),
                            port: None,
                        })
                        .into_port(&mut names),
                    },
                )
            })
            .collect();

        // Link them
        ports_for_cells.iter().for_each(|(i, entry)| {
            let mut ports = self.buffer.iter_ports(*i);

            if let Some(conn_p) = ports.next().flatten() {
                let other_node = ports_for_cells.get(&conn_p.cell).unwrap();
                let ast_conn = (conn_p.port as usize, other_node.clone());

                entry.borrow_mut().set_primary_port(Some(ast_conn));
            }

            ports
                .enumerate()
                .filter_map(|(i, x)| Some((i, x?)))
                .for_each(|(i, conn_aux)| {
                    let other_node = ports_for_cells.get(&conn_aux.cell).unwrap();
                    let ast_conn = (conn_aux.port as usize, other_node.clone());

                    entry.borrow_mut().insert_aux_port(i, Some(ast_conn));
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
        self.dispatch_reduction(redex)
    }

    fn reduce(&mut self) -> Vec<Port> {
        let (tx, rx) = mpsc::channel();

        self.tx_redexes = tx.clone();

        // Push all redexes
        for redex in self.buffer.iter_redexes() {
            tx.send(redex).unwrap();
        }

        // Spawn all results
        while let Ok(next) = rx.recv() {
            self.dispatch_reduction(next);
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
    fn test_readback_manual_matrix() {
        let mut matrix = ReducerBuilder::new_in_redex_loop()
            .1
            .with_capacity_nodes(6)
            .finish();
        let constrs = (
            matrix.buffer.push(Cell::Constr),
            matrix.buffer.push(Cell::Constr),
        );

        assert_ne!(constrs.0, constrs.1);

        let vars_top = (
            matrix.buffer.push(Cell::Var(0)),
            matrix.buffer.push(Cell::Var(1)),
        );
        let vars_bot = (
            matrix.buffer.push(Cell::Var(2)),
            matrix.buffer.push(Cell::Var(3)),
        );

        let unique_ids = BTreeSet::from_iter([
            constrs.0, constrs.1, vars_top.0, vars_top.1, vars_bot.0, vars_bot.1,
        ]);
        assert_eq!(unique_ids.len(), 6);

        matrix.buffer.connect(
            Some(Conn {
                cell: constrs.0,
                port: 0,
            }),
            Some(Conn {
                cell: constrs.1,
                port: 0,
            }),
        );

        assert_eq!(
            matrix.buffer.primary_port(constrs.0),
            Some(Conn {
                cell: constrs.1,
                port: 0
            })
        );
        assert_eq!(
            matrix.buffer.primary_port(constrs.1),
            Some(Conn {
                cell: constrs.0,
                port: 0
            })
        );

        matrix.buffer.connect(
            Some(Conn {
                cell: vars_top.0,
                port: 0,
            }),
            Some(Conn {
                cell: constrs.0,
                port: 1,
            }),
        );
        matrix.buffer.connect(
            Some(Conn {
                cell: vars_top.1,
                port: 0,
            }),
            Some(Conn {
                cell: constrs.0,
                port: 2,
            }),
        );
        assert_eq!(
            matrix.buffer.iter_ports(constrs.0).collect::<Vec<_>>(),
            vec![
                Some(Conn {
                    cell: constrs.1,
                    port: 0
                }),
                Some(Conn {
                    cell: vars_top.0,
                    port: 0,
                }),
                Some(Conn {
                    cell: vars_top.1,
                    port: 0,
                })
            ]
        );

        let res = matrix.readback().remove(0);
        assert_eq!(res.to_string(), "Constr[@0](2, 3) >< Constr[@1]()");
    }

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

            let (_, builder) = ReducerBuilder::new_in_redex_loop();
            let reducer = builder.with_init_net(&parsed[0].0).finish();

            println!("{:#?}", reducer.buffer);

            let res = reducer.readback();

            assert_eq!(res[0].orient().to_string(), parsed[0].orient().to_string());
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
                BTreeSet::from_iter(["Era[@2](a)", "Era[@3](b)"]),
            ),
            (
                "Dup[@1](a, b) >< Era[@2]()",
                BTreeSet::from_iter(["Era[@2](a)", "Era[@3](b)"]),
            ),
            (
                "Constr[@1](a, b) >< Dup[@2](d, c)",
                BTreeSet::from_iter(["Dup[@5](a, Constr[@6](d, @5#1, Dup[@4](b, @6#2, Constr[@7](c, @5#2, @4#2)#2)#1)#1, @7#1)"]),
            ),
            (
                "Dup[@1](a, b) >< Constr[@2](d, c)",
                BTreeSet::from_iter(["Constr[@5](a, Dup[@6](d, @5#1, Constr[@4](b, @6#2, Dup[@7](c, @5#2, @4#2)#2)#1)#1, @7#1)"]),
            ),
        ];

        for (case, expected) in cases {
            let parsed = parser::parser()
                .parse(parser::lexer().parse(case).unwrap())
                .unwrap();

            let (rx, builder) = ReducerBuilder::new_in_redex_loop();
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
