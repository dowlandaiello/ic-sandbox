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
        let cells = Vec::with_capacity(n_nodes * n_nodes);

        CapacitiedBufferedMatrixReducerBuilder {
            tx_redexes: self.tx_redexes,
            cells: MatrixBuffer::new(cells.into()),
            #[cfg(feature = "threadpool")]
            pool: self.pool,
        }
    }

    pub fn with_capacity_nodes(self, capacity: usize) -> CapacitiedBufferedMatrixReducerBuilder {
        let cells = Vec::with_capacity(capacity * capacity);

        CapacitiedBufferedMatrixReducerBuilder {
            tx_redexes: self.tx_redexes,
            cells: MatrixBuffer::new(cells.into()),
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
        self.buffer.iter_cells().for_each(|i| {
            let entry = ports_for_cells.get(&i).unwrap();

            let mut ports = self.buffer.iter_ports(i);

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
        while let Some(x) = self.buffer.iter_redexes().next() {
            tx.send(x).unwrap();
        }

        // Spawn all results
        while let Ok(next) = rx.recv() {
            self.dispatch_reduction(next);
        }

        self.readback()
    }
}
