use crate::{
    parser::{ast_lafont::Ident, naming::NameIter},
    UNIT_STR,
};
use std::{cell::RefCell, collections::HashSet, fmt, ops::Deref, rc::Rc};

#[derive(Debug, Clone)]
pub struct Port {
    pub e: Rc<RefCell<Expr>>,
    pub id: usize,
}

impl Deref for Port {
    type Target = Rc<RefCell<Expr>>;

    fn deref(&self) -> &Self::Target {
        &self.e
    }
}

impl fmt::Display for Port {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut seen: HashSet<usize> = Default::default();

        fn fmt_expr_ports(seen: &mut HashSet<usize>, e: &Port, ports: Vec<Port>) -> Option<String> {
            if !e.borrow().is_var() {
                if seen.contains(&e.id) {
                    return Some(format!("@{}", e.id));
                }

                seen.insert(e.id);
            }

            Some(match &*e.borrow() {
                Expr::Era(_) => format!(
                    "Era[@{}]({})",
                    e.id,
                    ports
                        .iter()
                        .map(|p| {
                            fmt_expr_ports(
                                seen,
                                p,
                                [p.borrow().primary_port().cloned()]
                                    .into_iter()
                                    .chain(p.borrow().aux_ports().into_iter().cloned())
                                    .filter_map(|x| x)
                                    .collect::<Vec<_>>(),
                            )
                        })
                        .filter_map(|x| x)
                        .collect::<Vec<_>>()
                        .join(", "),
                ),
                Expr::Dup(_) => format!(
                    "Dup[@{}]({})",
                    e.id,
                    ports
                        .iter()
                        .map(|p| fmt_expr_ports(
                            seen,
                            p,
                            [p.borrow().primary_port().cloned()]
                                .into_iter()
                                .chain(p.borrow().aux_ports().into_iter().cloned())
                                .filter_map(|x| x)
                                .collect::<Vec<_>>(),
                        ))
                        .filter_map(|x| x)
                        .collect::<Vec<_>>()
                        .join(", "),
                ),
                Expr::Constr(_) => format!(
                    "Constr[@{}]({})",
                    e.id,
                    ports
                        .iter()
                        .map(|p| fmt_expr_ports(
                            seen,
                            p,
                            [p.borrow().primary_port().cloned()]
                                .into_iter()
                                .chain(p.borrow().aux_ports().into_iter().cloned())
                                .filter_map(|x| x)
                                .collect::<Vec<_>>(),
                        ))
                        .filter_map(|x| x)
                        .collect::<Vec<_>>()
                        .join(", "),
                ),
                Expr::Var(v) => {
                    format!("{}", v.name)
                }
            })
        }

        if let Some((_, rhs)) = self.try_as_active_pair() {
            write!(
                f,
                "{} >< {}",
                fmt_expr_ports(
                    &mut seen,
                    self,
                    self.borrow()
                        .aux_ports()
                        .into_iter()
                        .filter_map(|x| x.as_ref())
                        .cloned()
                        .collect::<Vec<_>>()
                )
                .unwrap_or(UNIT_STR.to_owned()),
                fmt_expr_ports(
                    &mut seen,
                    &rhs,
                    rhs.borrow()
                        .aux_ports()
                        .into_iter()
                        .filter_map(|x| x.as_ref())
                        .cloned()
                        .collect::<Vec<_>>()
                )
                .unwrap_or(UNIT_STR.to_owned())
            )
        } else if let Some((_, rhs)) = self.try_as_wired_vars() {
            write!(
                f,
                "{} ~ {}",
                fmt_expr_ports(&mut seen, self, Vec::new()).unwrap_or(UNIT_STR.to_owned()),
                fmt_expr_ports(&mut seen, &rhs, Vec::new()).unwrap_or(UNIT_STR.to_owned())
            )
        } else {
            write!(
                f,
                "{}",
                fmt_expr_ports(
                    &mut seen,
                    self,
                    [self.borrow().primary_port().cloned()]
                        .into_iter()
                        .chain(self.borrow().aux_ports().into_iter().cloned())
                        .filter_map(|x| x)
                        .collect::<Vec<_>>()
                )
                .unwrap_or(UNIT_STR.to_owned())
            )
        }
    }
}

impl Port {
    pub fn try_as_wired_vars(&self) -> Option<(Port, Port)> {
        let self_port = self.borrow();
        let primary_port = self_port.primary_port()?;
        let port = primary_port.try_borrow().ok()?;

        if !primary_port.borrow().is_var() || !self_port.is_var() {
            return None;
        }

        match &*port {
            Expr::Var(v) => {
                if v.port
                    .as_ref()
                    .map(|p| Rc::ptr_eq(self, &p))
                    .unwrap_or_default()
                {
                    Some((self.clone(), primary_port.clone()))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn try_as_active_pair(&self) -> Option<(Port, Port)> {
        let self_port = self.borrow();
        let primary_port = self_port.primary_port()?;
        let port = primary_port.try_borrow().ok()?;

        match &*port {
            Expr::Var(_) => None,
            Expr::Constr(c) => {
                if c.primary_port
                    .as_ref()
                    .map(|p| Rc::ptr_eq(self, &p))
                    .unwrap_or_default()
                {
                    Some((self.clone(), primary_port.clone()))
                } else {
                    None
                }
            }
            Expr::Dup(d) => {
                if d.primary_port
                    .as_ref()
                    .map(|p| Rc::ptr_eq(self, &p))
                    .unwrap_or_default()
                {
                    Some((self.clone(), primary_port.clone()))
                } else {
                    None
                }
            }
            Expr::Era(e) => {
                if e.primary_port
                    .as_ref()
                    .map(|p| Rc::ptr_eq(self, &p))
                    .unwrap_or_default()
                {
                    Some((self.clone(), primary_port.clone()))
                } else {
                    None
                }
            }
        }
    }

    /// Sets all free ports to new vars
    pub fn fill_aux_vars(&self, names: &mut NameIter) {
        let n_ports = self.borrow().aux_ports().len();

        for _ in 0..n_ports {
            let v: Port = Expr::Var(Var {
                name: Ident(names.next()),
                port: Some(self.clone()),
            })
            .into_port(names);

            self.borrow_mut().push_aux_port(Some(v));
        }
    }
}

const EMPTY_AUX_PORTS: [Option<Port>; 2] = [None, None];

#[derive(Hash, Eq, PartialEq, Debug, Clone)]
pub enum Token {
    Era,
    Constr,
    Dup,
    Ident(String),
    ActivePair,
    LeftParen,
    RightParen,
    At,
    LeftBracket,
    RightBracket,
    Comma,
    Digit(usize),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Era => write!(f, "Era"),
            Self::Constr => write!(f, "Constr"),
            Self::Dup => write!(f, "Dup"),
            Self::Ident(i) => write!(f, "{}", i),
            Self::ActivePair => write!(f, "><"),
            Self::LeftParen => write!(f, "("),
            Self::RightParen => write!(f, ")"),
            Self::At => write!(f, "@"),
            Self::LeftBracket => write!(f, "["),
            Self::RightBracket => write!(f, "]"),
            Self::Comma => write!(f, ","),
            Self::Digit(d) => write!(f, "{}", d),
        }
    }
}

/// Represents any interaction combinator net
#[derive(Debug, Clone)]
pub enum Expr {
    Era(Eraser),
    Dup(Duplicator),
    Constr(Constructor),
    Var(Var),
}

impl Expr {
    pub fn is_var(&self) -> bool {
        matches!(self, Self::Var(_))
    }

    pub fn is_agent(&self) -> bool {
        !self.is_var()
    }
}

impl Expr {
    pub fn into_port(self, namer: &mut NameIter) -> Port {
        Port {
            e: Rc::new(RefCell::new(self)),
            id: namer.next_id(),
        }
    }

    pub fn into_port_named(self, id: usize) -> Port {
        Port {
            e: Rc::new(RefCell::new(self)),
            id,
        }
    }

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

    pub fn aux_ports(&self) -> &[Option<Port>] {
        match self {
            Self::Era(_) => &[],
            Self::Dup(d) => &d.aux_ports,
            Self::Constr(c) => &c.aux_ports,
            Self::Var(_) => &[],
        }
    }

    pub fn push_aux_port(&mut self, val: Option<Port>) {
        match self {
            Self::Era(_) => {}
            Self::Dup(d) => {
                if d.aux_ports[0].is_none() {
                    d.aux_ports[0] = val;
                } else {
                    d.aux_ports[1] = val;
                }
            }
            Self::Constr(c) => {
                if c.aux_ports[0].is_none() {
                    c.aux_ports[0] = val;
                } else {
                    c.aux_ports[1] = val;
                }
            }
            Self::Var(_) => {}
        }
    }

    pub fn insert_aux_port(&mut self, index: usize, val: Option<Port>) {
        match self {
            Self::Era(_) => {}
            Self::Dup(d) => {
                d.aux_ports[index] = val;
            }
            Self::Constr(c) => {
                c.aux_ports[index] = val;
            }
            Self::Var(_) => {}
        }
    }

    pub fn swap_conn(&mut self, initial: &Port, new: Option<Port>) {
        fn swap_conn_maybe(slf: &mut Expr, initial: &Port, new: Option<Port>) -> Option<()> {
            match slf {
                Expr::Era(e) => {
                    if Rc::ptr_eq(e.primary_port.as_ref()?, &initial) {
                        e.primary_port = new;
                    }
                }
                Expr::Constr(c) => {
                    if Rc::ptr_eq(c.primary_port.as_ref()?, &initial) {
                        c.primary_port = new.clone();
                    }

                    c.aux_ports = c
                        .aux_ports
                        .iter()
                        .cloned()
                        .map(|p| {
                            if Rc::ptr_eq(p.as_ref()?, &initial) {
                                new.clone()
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
                        d.primary_port = new.clone();
                    }

                    d.aux_ports = d
                        .aux_ports
                        .iter()
                        .cloned()
                        .map(|p| {
                            if Rc::ptr_eq(p.as_ref()?, &initial) {
                                new.clone()
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
                        v.port = new;
                    }
                }
            };

            Some(())
        }

        let _ = swap_conn_maybe(self, initial, new);
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

#[derive(Debug, Clone)]
pub struct Var {
    pub name: Ident,
    pub port: Option<Port>,
}
