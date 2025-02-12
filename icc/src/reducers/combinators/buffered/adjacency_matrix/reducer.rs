use super::{
    super::{super::Reducer, Conn},
    Cell, NetBuffer,
};
use crate::parser::ast_combinators::Port;
use rayon::{ThreadPool, ThreadPoolBuilder};
use std::{
    collections::VecDeque,
    convert::From,
    iter::DoubleEndedIterator,
    sync::{
        mpsc::{self, Receiver, Sender},
        Arc,
    },
};

macro_rules! conn_maybe_redex {
    ($self:ident, $a:expr, $b:expr) => {
        $self.connect($a, $b);

        if let Some((a, b)) = $a.zip($b) {
            if a.port == 0 && b.port == 0 {
                $self.push_active_pair(a, b);
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
        todo!()
    }

    pub fn with_capacity_nodes(self, capacity: usize) -> CapacitiedBufferedMatrixReducerBuilder {
        let cells = Vec::with_capacity(capacity * capacity);

        CapacitiedBufferedMatrixReducerBuilder {
            tx_redexes: self.tx_redexes,
            init_redexes: Default::default(),
            cells: cells.into(),
            #[cfg(feature = "threadpool")]
            pool: self.pool,
        }
    }
}

pub struct CapacitiedBufferedMatrixReducerBuilder {
    tx_redexes: Sender<(Conn, Conn)>,
    cells: Arc<[CellRepr]>,
    init_redexes: VecDeque<(Conn, Conn)>,
    pool: ThreadPoolBuilder,
}

impl CapacitiedBufferedMatrixReducerBuilder {
    pub fn finish(self) -> BufferedMatrixReducer {
        BufferedMatrixReducer {
            tx_redexes: self.tx_redexes,
            init_redexes: self.init_redexes,
            buffer: MatrixBuffer::new(self.cells),

            #[cfg(feature = "threadpool")]
            pool: self.pool.build().unwrap(),
        }
    }
}

pub struct BufferedMatrixReducer {
    tx_redexes: Sender<(Conn, Conn)>,
    init_redexes: VecDeque<(Conn, Conn)>,
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
                self.delete(a_id);
                self.delete(b_id);
            }
            // Commutation of constr dup
            (Cell::Constr, Cell::Dup) => {
                // Top is left to right, bottom is right to left
                let (top_ports, bottom_ports) = (self.iter_ports(a_id), self.iter_ports(b_id));

                self.make_commutation(top_ports, bottom_ports);
            }
            // Commutation of dup constr
            (Cell::Dup, Cell::Constr) => {
                let (top_ports, bottom_ports) = (self.iter_ports(b_id), self.iter_ports(a_id));

                self.make_commutation(top_ports, bottom_ports);
            }
            // Commutation of alpha era
            (Cell::Constr, Cell::Era) | (Cell::Dup, Cell::Era) => {
                let top_ports = self.iter_ports(a_id);

                self.make_era_commutation(top_ports);
            }
            (Cell::Era, Cell::Constr) | (Cell::Era, Cell::Dup) => {
                let top_ports = self.iter_ports(b_id);

                self.make_era_commutation(top_ports);
            }
            _ => {}
        }
    }
}

impl BufferedMatrixReducer {
    #[cfg(feature = "threadpool")]
    fn dispatch_reduction(&self, redex: (Conn, Conn)) {
        let worker = ReductionWorker {
            cells: self.cells.clone(),
            tx_redexes: self.tx_redexes.clone(),
        };

        self.pool.spawn(|| worker.reduce_step(redex))
    }

    #[cfg(not(feature = "threadpool"))]
    fn dispatch_reduction(&self, redex: (Conn, Conn)) {
        self.reduce_step(redex);
    }

    fn make_era_commutation(&self, top_ports: impl Iterator<Item = Option<Conn>>) {
        let eras = [self.push(Cell::Era), self.push(Cell::Era)];

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
        let dups = [self.push(Cell::Dup), self.push(Cell::Dup)];

        // Left to right
        let constrs = [self.push(Cell::Constr), self.push(Cell::Constr)];

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

impl Reducer for BufferedMatrixReducer {
    fn push_active_pair(&self, lhs: Conn, rhs: Conn) {
        self.tx_redexes.send((lhs, rhs)).unwrap();
    }

    fn readback(&self) -> Vec<Port> {
        todo!()
    }

    fn reduce_step(&self, redex: (Conn, Conn)) {
        self.dispatch_reduction(redex)
    }

    fn reduce(&mut self) -> Vec<Port> {
        let (tx, rx) = mpsc::channel();

        self.tx_redexes = tx.clone();

        // Push all redexes
        while let Some(x) = self.init_redexes.pop_front() {
            tx.send(x);
        }

        // Spawn all results
        while let Some(next) = rx.recv() {
            self.dispatch_reduction(next);
        }

        self.readback()
    }

    // Era annihilation, alpha-era comm., alpha annihilation can only decrease the number of cells
    // no extra allocation is necessary there
    // Commutation of constr and dup can increase the number of cells, as the interaction is between
    // two agents, but 4 agents are produced.
}

impl From<Port> for BufferedMatrixReducer {
    fn from(p: Port) -> Self {
        todo!()
    }
}
