use crate::{parser::ast_lafont::Ident, UNIT_STR};
use std::{
    cell::{Ref, RefCell, RefMut},
    fmt,
    rc::Rc,
};

pub type Port = Rc<RefCell<Expr>>;

const EMPTY_AUX_PORTS: [Option<Port>; 2] = [None, None];

/// Represents any interaction combinator net
#[derive(Debug, Clone)]
pub enum Expr {
    Era(Eraser),
    Dup(Duplicator),
    Constr(Constructor),
    Var(Var),
}

impl From<Expr> for Rc<RefCell<Expr>> {
    fn from(e: Expr) -> Self {
        Self::new(RefCell::new(e))
    }
}

impl Expr {
    pub fn set_aux_ports(&mut self, ports: [Option<Port>; 2]) {
        match self {
            Self::Era(_) => {}
            Self::Constr(c) => {
                c.aux_ports = ports;
            }
            Self::Dup(d) => {
                d.aux_ports = ports;
            }
            Self::Var(_) => {}
        }
    }

    pub fn set_primary_port(&mut self, port: Option<Port>) {
        match self {
            Self::Era(e) => {
                e.primary_port = port;
            }
            Self::Constr(c) => {
                c.primary_port = port;
            }
            Self::Dup(d) => {
                d.primary_port = port;
            }
            Self::Var(v) => {
                v.port = port;
            }
        }
    }

    /// Gets the agent connected to this agent's primary port, if it exists
    pub fn try_as_active_pair(&self) -> Option<(&Expr, Ref<Expr>)> {
        let primary_port = self.primary_port();

        if matches!(&*primary_port.as_ref()?.try_borrow().ok()?, Expr::Var(_)) {
            return None;
        }

        Some((self, primary_port.as_ref()?.try_borrow().ok()?))
    }

    pub fn try_as_active_pair_mut(&self) -> Option<(&Expr, RefMut<Expr>)> {
        let primary_port = self.primary_port();

        if matches!(&*primary_port.as_ref()?.try_borrow().ok()?, Expr::Var(_)) {
            return None;
        }

        Some((self, primary_port.as_ref()?.try_borrow_mut().ok()?))
    }

    /// Gets the agent's primary port, whether it is a variable or an agent
    pub fn primary_port(&self) -> Option<&Port> {
        match &self {
            Self::Era(e) => &e.primary_port,
            Self::Dup(d) => &d.primary_port,
            Self::Constr(c) => &c.primary_port,
            Self::Var(v) => &v.port,
        }
        .as_ref()
    }

    pub fn swap_conn(&mut self, initial: &Port, new: Port) {
        fn swap_conn_maybe(slf: &mut Expr, initial: &Port, new: Port) -> Option<()> {
            match slf {
                Expr::Era(e) => {
                    if Rc::ptr_eq(e.primary_port.as_ref()?, &initial) {
                        e.primary_port = Some(new);
                    }
                }
                Expr::Constr(c) => {
                    if Rc::ptr_eq(c.primary_port.as_ref()?, &initial) {
                        c.primary_port = Some(new.clone());
                    }

                    c.aux_ports = c
                        .aux_ports
                        .iter()
                        .cloned()
                        .map(|p| {
                            if Rc::ptr_eq(p.as_ref()?, &initial) {
                                Some(new.clone())
                            } else {
                                p
                            }
                        })
                        .collect::<Vec<_>>()
                        .try_into()
                        .unwrap_or([None, None]);
                }
                Expr::Dup(d) => {
                    if Rc::ptr_eq(d.primary_port.as_ref()?, &initial) {
                        d.primary_port = Some(new.clone());
                    }

                    d.aux_ports = d
                        .aux_ports
                        .iter()
                        .cloned()
                        .map(|p| {
                            if Rc::ptr_eq(p.as_ref()?, &initial) {
                                Some(new.clone())
                            } else {
                                p
                            }
                        })
                        .collect::<Vec<_>>()
                        .try_into()
                        .unwrap_or([None, None]);
                }
                Expr::Var(v) => {
                    if Rc::ptr_eq(v.port.as_ref()?, &initial) {
                        v.port = Some(new);
                    }
                }
            };

            Some(())
        }

        let _ = swap_conn_maybe(self, initial, new);
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Era(e) => write!(f, "{}", e),
            Self::Dup(d) => write!(f, "{}", d),
            Self::Constr(c) => write!(f, "{}", c),
            Self::Var(v) => write!(f, "{}", v),
        }
    }
}

#[derive(Default, Debug, Clone)]
pub struct Eraser {
    pub primary_port: Option<Port>,
}

impl Eraser {
    pub const fn new() -> Self {
        Self { primary_port: None }
    }
}

impl fmt::Display for Eraser {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Era >< {}",
            self.primary_port
                .as_ref()
                .and_then(|p| p.try_borrow().ok().map(|s| s.to_string()))
                .unwrap_or(UNIT_STR.to_owned())
        )
    }
}

#[derive(Default, Debug, Clone)]
pub struct Duplicator {
    pub primary_port: Option<Port>,
    pub aux_ports: [Option<Port>; 2],
}

impl Duplicator {
    pub const fn new() -> Self {
        Duplicator {
            primary_port: None,
            aux_ports: EMPTY_AUX_PORTS,
        }
    }
}

impl fmt::Display for Duplicator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Dup({}, {}) >< {}",
            self.aux_ports[0]
                .as_ref()
                .and_then(|p| p.try_borrow().ok().map(|s| s.to_string()))
                .unwrap_or(UNIT_STR.to_owned()),
            self.aux_ports[1]
                .as_ref()
                .and_then(|p| p.try_borrow().ok().map(|s| s.to_string()))
                .unwrap_or(UNIT_STR.to_owned()),
            self.primary_port
                .as_ref()
                .and_then(|p| p.try_borrow().ok().map(|s| s.to_string()))
                .unwrap_or(UNIT_STR.to_owned())
        )
    }
}

#[derive(Default, Debug, Clone)]
pub struct Constructor {
    pub primary_port: Option<Port>,
    pub aux_ports: [Option<Port>; 2],
}

impl Constructor {
    pub const fn new() -> Self {
        Self {
            primary_port: None,
            aux_ports: EMPTY_AUX_PORTS,
        }
    }
}

impl fmt::Display for Constructor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Constr({}, {}) >< {}",
            self.aux_ports[0]
                .as_ref()
                .and_then(|p| p.try_borrow().ok().map(|s| s.to_string()))
                .unwrap_or(UNIT_STR.to_owned()),
            self.aux_ports[1]
                .as_ref()
                .and_then(|p| p.try_borrow().ok().map(|s| s.to_string()))
                .unwrap_or(UNIT_STR.to_owned()),
            self.primary_port
                .as_ref()
                .and_then(|p| p.try_borrow().ok().map(|s| s.to_string()))
                .unwrap_or(UNIT_STR.to_owned())
        )
    }
}

#[derive(Debug, Clone)]
pub struct Var {
    pub name: Ident,
    pub port: Option<Port>,
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}
