use crate::{
    parser::{
        ast_lafont::{Agent, Ident, Port as LafontPort},
        naming::NameIter,
    },
    NAME_CONSTR_AGENT, NAME_DUP_AGENT, NAME_ERA_AGENT, UNIT_STR,
};
use std::{cell::RefCell, fmt, rc::Rc};

pub type Port = Rc<RefCell<Expr>>;

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
    Comma,
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
            Self::Comma => write!(f, ","),
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

impl TryFrom<Agent> for Port {
    type Error = ();

    fn try_from(a: Agent) -> Result<Self, Self::Error> {
        let agent: Port = match a.name.0.as_ref() {
            NAME_CONSTR_AGENT => Ok::<Port, _>(Expr::Constr(Constructor::new()).into()),
            NAME_ERA_AGENT => Ok::<Port, _>(Expr::Era(Eraser::new()).into()),
            NAME_DUP_AGENT => Ok::<Port, _>(Expr::Dup(Duplicator::new()).into()),
            _ => Err(()),
        }?
        .into();

        agent.try_borrow_mut().map_err(|_| ())?.set_aux_ports(
            a.ports
                .into_iter()
                .map(|p| match p {
                    LafontPort::Var(v) => Some(
                        Expr::Var(Var {
                            port: Some(agent.clone()),
                            name: Ident(v.0),
                        })
                        .into(),
                    ),
                    LafontPort::Agent(a) => Self::try_from(a.clone()).ok(),
                })
                .collect::<Vec<_>>()
                .try_into()
                .map_err(|_| ())?,
        );

        Ok(agent)
    }
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

/// Sets all free ports to new vars
pub fn fill_port_aux_vars(slf: &Port, names: &mut NameIter) {
    let n_ports = slf.borrow().aux_ports().len();

    for _ in 0..n_ports {
        let v: Port = Expr::Var(Var {
            name: Ident(names.next()),
            port: Some(slf.clone()),
        })
        .into();

        slf.borrow_mut().push_aux_port(Some(v));
    }
}

pub fn try_as_active_pair(slf: &Port) -> Option<(Port, Port)> {
    let slf_port = slf.try_borrow().ok()?;
    let primary_port = slf_port.primary_port()?;
    let port = primary_port.try_borrow().ok()?;

    match &*port {
        Expr::Var(_) => None,
        Expr::Constr(c) => {
            if c.primary_port
                .as_ref()
                .map(|p| Rc::ptr_eq(slf, &p))
                .unwrap_or_default()
            {
                Some((slf.clone(), primary_port.clone()))
            } else {
                None
            }
        }
        Expr::Dup(d) => {
            if d.primary_port
                .as_ref()
                .map(|p| Rc::ptr_eq(slf, &p))
                .unwrap_or_default()
            {
                Some((slf.clone(), primary_port.clone()))
            } else {
                None
            }
        }
        Expr::Era(e) => {
            if e.primary_port
                .as_ref()
                .map(|p| Rc::ptr_eq(slf, &p))
                .unwrap_or_default()
            {
                Some((slf.clone(), primary_port.clone()))
            } else {
                None
            }
        }
    }
}

pub fn port_to_string(slf: &Port) -> String {
    let mut seen: Vec<*mut Expr> = Default::default();

    fn fmt_expr_ports(seen: &mut Vec<*mut Expr>, e: &Port, ports: Vec<Port>) -> Option<String> {
        if let Some(idx) = seen.iter().position(|x| *x == e.as_ptr()) {
            return Some(format!("@{}", idx));
        }

        seen.push(e.as_ptr());

        Some(match &*e.borrow() {
            Expr::Era(_) => format!(
                "Era[@{}]({})",
                seen.len() - 1,
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
                seen.len() - 1,
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
                seen.len() - 1,
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
            Expr::Var(v) => format!("{}", v.name),
        })
    }

    if let Some((_, rhs)) = try_as_active_pair(slf) {
        format!(
            "{} >< {}",
            fmt_expr_ports(
                &mut seen,
                slf,
                slf.borrow()
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
    } else {
        format!(
            "{}",
            fmt_expr_ports(
                &mut seen,
                slf,
                [slf.borrow().primary_port().cloned()]
                    .into_iter()
                    .chain(slf.borrow().aux_ports().into_iter().cloned())
                    .filter_map(|x| x)
                    .collect::<Vec<_>>()
            )
            .unwrap_or(UNIT_STR.to_owned())
        )
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
