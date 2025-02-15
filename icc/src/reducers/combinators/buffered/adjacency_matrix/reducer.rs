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
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use std::{
    collections::{BTreeMap, BTreeSet},
    iter::DoubleEndedIterator,
};

macro_rules! conn_maybe_redex {
    ($self:ident, $redexbuff:expr, $a:expr, $b:expr) => {
        $self.buffer.connect($a, $b);

        if let Some(((a_conn, a_cell), (b_conn, b_cell))) = $a.zip($b).map(|(a, b)| {
            (
                (a, $self.buffer.get_cell(a.cell)),
                (b, $self.buffer.get_cell(b.cell)),
            )
        }) {
            if a_conn.port == 0
                && b_conn.port == 0
                && !matches!(a_cell, Cell::Var(_))
                && !matches!(b_cell, Cell::Var(_))
            {
                $redexbuff.push((a_conn, b_conn));
            }
        }
    };
}

#[derive(Default)]
pub struct ReducerBuilder {
    idents: BTreeMap<Ptr, String>,
    names: BTreeMap<Ptr, usize>,
}

impl ReducerBuilder {
    pub fn with_init_net(mut self, net: &Port) -> CapacitiedBufferedMatrixReducerBuilder {
        let n_nodes = net.iter_tree().count();

        let buff = MatrixBuffer::new_with_capacity_nodes(n_nodes);

        let slots_for_ast_elems: BTreeMap<usize, usize> = net
            .iter_tree()
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
            cells: buff,
            idents: self.idents,
            names: self.names,
        }
    }

    pub fn with_capacity_nodes(self, capacity: usize) -> CapacitiedBufferedMatrixReducerBuilder {
        CapacitiedBufferedMatrixReducerBuilder {
            cells: MatrixBuffer::new_with_capacity_nodes(capacity),
            idents: self.idents,
            names: self.names,
        }
    }
}

pub struct CapacitiedBufferedMatrixReducerBuilder {
    cells: MatrixBuffer,
    idents: BTreeMap<Ptr, String>,
    names: BTreeMap<Ptr, usize>,
}

impl CapacitiedBufferedMatrixReducerBuilder {
    pub fn finish(self) -> BufferedMatrixReducer {
        BufferedMatrixReducer {
            buffer: self.cells,
            idents: self.idents,
            names: self.names,
        }
    }
}

pub struct BufferedMatrixReducer {
    buffer: MatrixBuffer,
    idents: BTreeMap<Ptr, String>,
    names: BTreeMap<Ptr, usize>,
}

#[derive(Clone)]
pub struct ReductionWorker {
    buffer: MatrixBuffer,
}

impl ReductionWorker {
    fn reduce_step(&self, redex: (Conn, Conn)) -> Vec<(Conn, Conn)> {
        let mut redexes = Vec::default();

        let a_id = redex.0.cell;
        let b_id = redex.1.cell;

        let pair = (self.buffer.get_cell(a_id), self.buffer.get_cell(b_id));

        tracing::trace!("reducing {} ({}) >< {} ({})", pair.0, a_id, pair.1, b_id);

        match pair {
            // Annihilation of alpha-alpha
            (Cell::Constr, Cell::Constr) | (Cell::Dup, Cell::Dup) => {
                let (top_ports, bottom_ports) = (
                    self.buffer.iter_aux_ports(a_id),
                    self.buffer.iter_aux_ports(b_id),
                );

                // Remember, bottom ports is flipped due to orientation
                top_ports.zip(bottom_ports).for_each(|(a, b)| {
                    conn_maybe_redex!(self, &mut redexes, a, b);
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
                let (top_ports, bottom_ports) = (
                    self.buffer.iter_aux_ports(a_id),
                    self.buffer.iter_aux_ports(b_id),
                );

                self.make_commutation(&mut redexes, top_ports, bottom_ports);
            }
            // Commutation of dup constr
            (Cell::Dup, Cell::Constr) => {
                let (top_ports, bottom_ports) = (
                    self.buffer.iter_aux_ports(b_id),
                    self.buffer.iter_aux_ports(a_id),
                );

                self.make_commutation(&mut redexes, top_ports, bottom_ports);
            }
            // Commutation of alpha era
            (Cell::Constr, Cell::Era) | (Cell::Dup, Cell::Era) => {
                let top_ports = self.buffer.iter_aux_ports(a_id);

                self.make_era_commutation(&mut redexes, top_ports);
            }
            (Cell::Era, Cell::Constr) | (Cell::Era, Cell::Dup) => {
                let top_ports = self.buffer.iter_aux_ports(b_id);

                self.make_era_commutation(&mut redexes, top_ports);
            }
            _ => {
                panic!("invalid redex")
            }
        }

        self.buffer.delete(a_id);
        self.buffer.delete(b_id);

        redexes
    }

    fn make_era_commutation(
        &self,
        redexes: &mut Vec<(Conn, Conn)>,
        top_ports: impl Iterator<Item = Option<Conn>>,
    ) {
        let eras = [self.buffer.push(Cell::Era), self.buffer.push(Cell::Era)];

        top_ports
            .zip(eras.iter().map(|ptr| Some((*ptr, 0).into())))
            .for_each(|(a, b)| {
                conn_maybe_redex!(self, redexes, a, b);
            });
    }

    fn make_commutation(
        &self,
        redexes: &mut Vec<(Conn, Conn)>,
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
                conn_maybe_redex!(self, redexes, a, b);
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
                conn_maybe_redex!(self, redexes, a, b);
            });

        let conn_left = ((dups[0], 2), (constrs[0], 1));
        let conn_right = ((dups[1], 1), (constrs[1], 2));
        let conn_middle_left = ((dups[0], 1), (constrs[1], 1));
        let conn_middle_right = ((dups[1], 2), (constrs[0], 2));

        let conns = [conn_left, conn_right, conn_middle_left, conn_middle_right];

        conns.iter().for_each(|(a, b)| {
            conn_maybe_redex!(
                self,
                redexes,
                Some::<Conn>((*a).into()),
                Some::<Conn>((*b).into())
            );
        });
    }
}

impl Reducer for BufferedMatrixReducer {
    fn readback(&self) -> Vec<Port> {
        let new_names = NameIter::starting_from(self.names.len());

        // Make ports before linking, link later
        let mut ports_for_cells: BTreeMap<Ptr, Port> = self
            .buffer
            .iter_cells()
            .map(|i| (i, self.buffer.get_cell(i)))
            .map(|(i, discriminant)| {
                let name = self
                    .names
                    .get(&i)
                    .map(|x| *x)
                    .unwrap_or_else(|| new_names.next_id());

                (
                    i,
                    match discriminant {
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
        let mut worker = ReductionWorker {
            buffer: self.buffer.clone(),
        };

        worker.reduce_step(redex);
    }

    fn reduce(&mut self) -> Vec<Port> {
        fn reduce_redexes(buffer: MatrixBuffer, r: impl IntoParallelIterator<Item = (Conn, Conn)>) {
            r.into_par_iter().for_each(move |x| {
                let mut worker = ReductionWorker {
                    buffer: buffer.clone(),
                };

                let redexes = worker.reduce_step(x);

                reduce_redexes(buffer.clone(), redexes);
            });
        }

        // Push all redexes
        reduce_redexes(
            self.buffer.clone(),
            self.buffer.iter_redexes().collect::<Vec<_>>(),
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
    fn test_readback_manual_matrix() {
        let matrix = ReducerBuilder::default().with_capacity_nodes(6).finish();
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
