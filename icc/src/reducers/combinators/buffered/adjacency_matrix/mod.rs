use super::{
    super::{Conn, Ptr, Reducer},
    Cell, NetBuffer,
};
use crate::parser::ast_combinators::Port;

pub(crate) mod atomic_reprs;
mod matrix_buffer;
mod reducer;

pub use reducer::{BufferedMatrixReducer, ReducerBuilder};

#[derive(Debug, Copy, Clone)]
pub(crate) struct OwnedCell {
    discriminant: Cell,
    primary_port: Option<Conn>,
    aux_ports: [Option<Conn>; 2],
}

impl OwnedCell {
    fn new(discriminant: Cell) -> Self {
        Self {
            discriminant,
            primary_port: None,
            aux_ports: [const { None }; 2],
        }
    }

    fn merge(&mut self, other: &Self) {
        other
            .iter_ports()
            .enumerate()
            .filter_map(|(i, x)| Some((i, x?)))
            .for_each(|(i, x)| self.set_port_i(i as u8, Some(x)));
    }

    fn set_port_i(&mut self, i: u8, c: Option<Conn>) {
        match i {
            0 => {
                self.primary_port = c;
            }
            1 => {
                self.aux_ports[0] = c;
            }
            2 => {
                self.aux_ports[1] = c;
            }
            _ => panic!("port out of range"),
        }
    }

    fn iter_ports<'a>(&'a self) -> impl DoubleEndedIterator<Item = Option<Conn>> + 'a {
        [self.primary_port, self.aux_ports[0], self.aux_ports[1]].into_iter()
    }

    fn unwrap_aux_ports(&self) -> [Conn; 2] {
        [self.aux_ports[0].unwrap(), self.aux_ports[1].unwrap()]
    }

    fn iter_aux_ports<'a>(&'a self) -> impl DoubleEndedIterator<Item = Option<Conn>> + 'a {
        [self.aux_ports[0], self.aux_ports[1]].into_iter()
    }

    fn set_discriminant(&mut self, c: Cell) {
        self.discriminant = c;
    }

    fn wipe(&mut self) {
        self.primary_port = None;

        self.aux_ports[0] = None;
        self.aux_ports[1] = None;
    }
}

pub fn reduce_dyn(e: &Port) -> Vec<Port> {
    let builder = ReducerBuilder::default();

    let mut results = builder.with_init_net(e).finish().reduce();
    results.sort_by(|a, b| {
        b.iter_tree()
            .filter(|x| x.borrow().as_var().is_some())
            .count()
            .cmp(
                &a.iter_tree()
                    .filter(|x| x.borrow().as_var().is_some())
                    .count(),
            )
    });

    results
}
