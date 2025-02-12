use super::{
    super::{Conn, Ptr, Reducer},
    Cell, NetBuffer,
};
use crate::parser::ast_combinators::Port;
use std::{
    convert::From,
    iter::DoubleEndedIterator,
    sync::mpsc::{self, Receiver, Sender},
};

use atomic_reprs::CellRepr;

mod atomic_reprs;

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
}

impl ReducerBuilder {
    pub fn new_in_redex_loop() -> (Receiver<(Conn, Conn)>, Self) {
        let (tx, rx) = mpsc::channel();

        (rx, Self { tx_redexes: tx })
    }

    pub fn with_init_net(self, net: Port) -> CapacitiedBufferedMatrixReducerBuilder {
        todo!()
    }

    pub fn with_capacity_nodes(self, capacity: usize) -> CapacitiedBufferedMatrixReducerBuilder {
        let cells = Vec::with_capacity(capacity * capacity);

        CapacitiedBufferedMatrixReducerBuilder {
            tx_redexes: self.tx_redexes,
            cells,
        }
    }
}

pub struct CapacitiedBufferedMatrixReducerBuilder {
    tx_redexes: Sender<(Conn, Conn)>,
    cells: Vec<CellRepr>,
}

impl CapacitiedBufferedMatrixReducerBuilder {
    pub fn finish(self) -> BufferedMatrixReducer {
        BufferedMatrixReducer {
            tx_redexes: self.tx_redexes,
            cells: self.cells,
        }
    }
}

pub struct BufferedMatrixReducer {
    tx_redexes: Sender<(Conn, Conn)>,
    cells: Vec<CellRepr>,
}

impl BufferedMatrixReducer {
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
            .zip(dups.iter().map(|ptr| (0, ptr)))
            .for_each(|(a, b)| {
                conn_maybe_redex!(self, a, Some::<Conn>((b.0, *b.1).into()));
            });
        bottom_ports
            .rev()
            .zip(constrs.iter().map(|ptr| (0, ptr)))
            .for_each(|(a, b)| {
                conn_maybe_redex!(self, a, Some::<Conn>((b.0, *b.1).into()));
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
    fn readback(&self) -> Vec<Port> {
        todo!()
    }

    fn reduce(&self) -> Vec<Port> {
        todo!()
    }

    // Era annihilation, alpha-era comm., alpha annihilation can only decrease the number of cells
    // no extra allocation is necessary there
    // Commutation of constr and dup can increase the number of cells, as the interaction is between
    // two agents, but 4 agents are produced.
    fn reduce_step(&self, redex: (Conn, Conn)) {
        let a_id = redex.0.cell;
        let b_id = redex.0.cell;

        let pair = (self.get_cell(a_id), self.get_cell(b_id));

        match pair {
            // Annihilation of alpha-alpha
            (Cell::Constr, Cell::Constr) | (Cell::Dup, Cell::Dup) => {
                let (top_ports, bottom_ports) = (self.iter_ports(a_id), self.iter_ports(b_id));

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

impl NetBuffer for BufferedMatrixReducer {
    fn push_active_pair(&self, lhs: Conn, rhs: Conn) {
        self.tx_redexes.send((lhs, rhs)).unwrap();
    }

    fn push(&self, c: Cell) -> Ptr {
        todo!()
    }

    fn delete(&self, p: Ptr) {
        todo!()
    }

    fn connect(&self, from: Option<Conn>, to: Option<Conn>) {
        todo!()
    }

    fn get_conn(&self, from: usize, to: usize) -> Option<(Conn, Conn)> {
        let from_conn = self.conns[from][to].load().unwrap();
        let to_conn = self.conns[to][from].load().unwrap();

        from_conn
            .map(|port| Conn { cell: to, port })
            .zip(to_conn.map(|port| Conn { cell: from, port }))
    }

    fn get_cell(&self, idx: usize) -> Cell {
        let elem = &self.cells[idx];
        let disc = elem.load().unwrap();

        match disc {
            0 => Cell::Constr,
            1 => Cell::Dup,
            2 => Cell::Era,

            // This will be unique, always
            _ => Cell::Var(idx),
        }
    }

    fn iter_ports(&self, cell: usize) -> impl DoubleEndedIterator<Item = Option<Conn>> {
        let ports = &self.conns[cell];
        ports.iter().enumerate().filter_map(|(other_id, x)| {
            Some((other_id, x.load()?)).map(|(other_id, x)| {
                x.map(|port| Conn {
                    cell: other_id,
                    port,
                })
            })
        })
    }

    fn primary_port(&self, cell: usize) -> Option<Conn> {
        todo!()
    }
}

impl From<Port> for BufferedMatrixReducer {
    fn from(p: Port) -> Self {
        todo!()
    }
}

pub fn reduce_dyn(e: &Port) -> Vec<Port> {
    BufferedMatrixReducer::from(e.clone()).reduce()
}
