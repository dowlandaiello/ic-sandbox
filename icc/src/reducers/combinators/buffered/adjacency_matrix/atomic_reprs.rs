use super::{Cell, Conn, Ptr};
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};

const DEFAULT_ORDERING_LOAD: Ordering = Ordering::SeqCst;
const DEFAULT_ORDERING_STORE: Ordering = Ordering::SeqCst;

pub(crate) struct ConnRepr {
    port: AtomicU8,
    cell: AtomicUsize,
}

impl From<Option<Conn>> for ConnRepr {
    fn from(c: Option<Conn>) -> Self {
        let repr = Self::default();
        repr.store(c);

        repr
    }
}

impl Default for ConnRepr {
    fn default() -> Self {
        Self {
            port: store_optional_u8(None),
            cell: store_optional_usize(None),
        }
    }
}

impl Clone for ConnRepr {
    fn clone(&self) -> Self {
        Self {
            port: AtomicU8::new(self.port.load(DEFAULT_ORDERING_STORE)),
            cell: AtomicUsize::new(self.cell.load(DEFAULT_ORDERING_STORE)),
        }
    }
}

impl ConnRepr {
    fn store(&self, c: Option<Conn>) {
        if let Some(c) = c {
            self.cell.store(c.cell << 1, DEFAULT_ORDERING_STORE);
            self.port.store(c.port << 1, DEFAULT_ORDERING_STORE);

            return;
        }

        self.port.store(0b1, DEFAULT_ORDERING_STORE);
        self.cell.store(0b1, DEFAULT_ORDERING_STORE);
    }

    fn load_port(&self) -> Option<u8> {
        load_optional_u8(&self.port)
    }

    fn load_cell(&self) -> Option<Ptr> {
        load_optional_usize(&self.cell)
    }

    fn load(&self) -> Option<Conn> {
        Some(Conn {
            cell: self.load_cell()?,
            port: self.load_port()?,
        })
    }
}

#[cfg(test)]
#[derive(Default, Clone, Copy)]
pub(crate) struct ConnBuilder {
    cell: Option<Ptr>,
    port: Option<u8>,
}

#[cfg(test)]
impl ConnBuilder {
    pub(crate) fn new(conn: Option<Conn>) -> Self {
        if let Some(c) = conn {
            Self::default()
                .with_cell(Some(c.cell))
                .with_port(Some(c.port))
        } else {
            Self::default()
        }
    }

    pub(crate) fn with_cell(mut self, cell: Option<Ptr>) -> Self {
        self.cell = cell;

        self
    }

    pub(crate) fn with_port(mut self, port: Option<u8>) -> Self {
        self.port = port;

        self
    }

    pub(crate) fn finish(self) -> ConnRepr {
        ConnRepr {
            port: store_optional_u8(self.port),
            cell: store_optional_usize(self.cell),
        }
    }
}

/// Each cell has at most 3 ports,
/// 1 primary port, 2 aux ports
pub(crate) struct CellRepr {
    // Empty marked in discriminant
    discriminant: AtomicU8,
    primary_port: ConnRepr,
    aux_ports: [ConnRepr; 2],
}

impl Default for CellRepr {
    fn default() -> Self {
        Self {
            discriminant: store_optional_u8(None),
            primary_port: Default::default(),
            aux_ports: [Default::default(), Default::default()],
        }
    }
}

#[cfg(test)]
#[derive(Default, Clone, Copy)]
pub(crate) struct CellBuilder {
    discriminant: Option<Cell>,
    primary_port: Option<Conn>,
    aux_ports: [Option<Conn>; 2],
}

#[cfg(test)]
impl CellBuilder {
    pub(crate) fn with_discriminant(mut self, c: Cell) -> Self {
        self.discriminant = Some(c);

        self
    }

    pub(crate) fn with_primary_port(mut self, p: Option<Conn>) -> Self {
        self.primary_port = p;

        self
    }

    pub(crate) fn with_port_i(mut self, i: usize, p: Option<Conn>) -> Self {
        match i {
            0 => self.with_primary_port(p),
            1 => {
                self.aux_ports[0] = p;

                self
            }
            2 => {
                self.aux_ports[1] = p;

                self
            }
            _ => panic!("port out of bounds"),
        }
    }

    pub(crate) fn with_push_port(mut self, p: Option<Conn>) -> Self {
        if self.primary_port.is_none() {
            self.primary_port = p;
        } else if self.aux_ports[0].is_none() {
            self.aux_ports[0] = p;
        } else {
            self.aux_ports[1] = p;
        }

        self
    }

    pub(crate) fn with_push_aux_port(mut self, p: Option<Conn>) -> Self {
        if self.aux_ports[0].is_none() {
            self.aux_ports[0] = p;
        } else {
            self.aux_ports[1] = p;
        }

        self
    }

    pub(crate) fn finish(self) -> CellRepr {
        CellRepr {
            discriminant: store_optional_u8(self.discriminant.map(|c| c.discriminant_uninit_var())),
            primary_port: ConnBuilder::new(self.primary_port).finish(),
            aux_ports: [
                ConnBuilder::new(self.aux_ports[0]).finish(),
                ConnBuilder::new(self.aux_ports[1]).finish(),
            ],
        }
    }
}

impl Clone for CellRepr {
    fn clone(&self) -> Self {
        Self {
            discriminant: AtomicU8::new(self.discriminant.load(DEFAULT_ORDERING_STORE)),
            primary_port: self.primary_port.clone(),
            aux_ports: self.aux_ports.clone(),
        }
    }
}

impl CellRepr {
    pub(crate) fn load_discriminant_uninit_var(&self) -> Option<Cell> {
        load_optional_u8(&self.discriminant).map(|c| Cell::from_discriminant_uninit_var(c))
    }

    pub(crate) fn load_primary_port(&self) -> Option<Conn> {
        self.primary_port.load()
    }

    pub(crate) fn store_port_i(&self, i: u8, c: Option<Conn>) {
        match i {
            0 => {
                self.primary_port.store(c);
            }
            1 => {
                self.aux_ports[0].store(c);
            }
            2 => {
                self.aux_ports[1].store(c);
            }
            _ => panic!("port out of range"),
        }
    }

    pub(crate) fn load_aux_port(&self, i: usize) -> Option<Conn> {
        self.aux_ports[i].load()
    }

    pub(crate) fn iter_ports<'a>(
        &'a self,
    ) -> impl DoubleEndedIterator<Item = Option<Conn>> + Clone + 'a {
        [
            self.load_primary_port(),
            self.load_aux_port(0),
            self.load_aux_port(1),
        ]
        .into_iter()
    }

    pub(crate) fn iter_aux_ports<'a>(
        &'a self,
    ) -> impl DoubleEndedIterator<Item = Option<Conn>> + Clone + 'a {
        [self.load_aux_port(0), self.load_aux_port(1)].into_iter()
    }

    pub(crate) fn wipe(&self) {
        self.store_discriminant(None);
        self.store_port_i(0, None);
        self.store_port_i(1, None);
        self.store_port_i(2, None);
    }

    pub(crate) fn store_discriminant(&self, c: Option<Cell>) {
        if let Some(c) = c.map(|c| c.discriminant_uninit_var()) {
            self.discriminant.store(c << 1, DEFAULT_ORDERING_STORE);
        } else {
            self.discriminant.store(0b1, DEFAULT_ORDERING_STORE);
        }
    }
}

pub(crate) fn store_optional_u8(u: Option<u8>) -> AtomicU8 {
    AtomicU8::new(match u {
        None => 0b1,
        Some(x) => x << 1,
    })
}

pub(crate) fn store_optional_usize(u: Option<usize>) -> AtomicUsize {
    AtomicUsize::new(match u {
        None => 0b1,
        Some(x) => x << 1,
    })
}

pub(crate) fn load_optional_u8(u: &AtomicU8) -> Option<u8> {
    let mut u = u.load(DEFAULT_ORDERING_LOAD);

    let empty = u & 0b1;

    if empty == 1 {
        return None;
    }

    u >>= 1;

    Some(u)
}

pub(crate) fn load_optional_usize(u: &AtomicUsize) -> Option<usize> {
    let mut u = u.load(DEFAULT_ORDERING_LOAD);

    let empty = u & 0b1;

    if empty == 1 {
        return None;
    }

    u >>= 1;

    Some(u)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_load_store_helpers() {
        assert_eq!(load_optional_u8(&store_optional_u8(None)), None);

        (0..100).for_each(|x| {
            assert_eq!(load_optional_u8(&store_optional_u8(Some(x))), Some(x));
        });

        assert_eq!(load_optional_usize(&store_optional_usize(None)), None);

        (0..100).for_each(|x| {
            assert_eq!(load_optional_usize(&store_optional_usize(Some(x))), Some(x));
        });
    }

    #[test]
    fn test_reprs() {
        let test_cell_repr_with = |x: CellBuilder| {
            let x_2 = x;

            let repr = x.finish();

            assert_eq!(repr.load_discriminant_uninit_var(), x_2.discriminant);
            assert_eq!(repr.load_primary_port(), x_2.primary_port);
            assert_eq!(repr.load_aux_port(0), x_2.aux_ports[0]);
            assert_eq!(repr.load_aux_port(1), x_2.aux_ports[0]);
            assert_eq!(
                repr.iter_ports().collect::<Vec<_>>(),
                vec![x_2.primary_port, x_2.aux_ports[0], x_2.aux_ports[1]]
            );
            assert_eq!(
                repr.iter_ports().rev().collect::<Vec<_>>(),
                vec![x_2.aux_ports[1], x_2.aux_ports[0], x_2.primary_port]
            );
        };

        test_cell_repr_with(CellBuilder::default());

        (0..3)
            .map(|x| Cell::from_discriminant_uninit_var(x))
            .for_each(|disc| {
                (0..100).for_each(|_| {
                    test_cell_repr_with(
                        CellBuilder::default()
                            .with_discriminant(disc)
                            .with_port_i(0, Some((1, 1).into()))
                            .with_port_i(1, Some((1, 1).into()))
                            .with_port_i(2, Some((1, 1).into())),
                    )
                });
            });
    }
}
