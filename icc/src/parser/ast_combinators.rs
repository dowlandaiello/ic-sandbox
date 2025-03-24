use crate::{
    parser::{ast_lafont::Ident, naming::NameIter},
    UNIT_STR,
};
use ast_ext::{TreeCursor, TreeVisitor, VisualDebug};
use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet, VecDeque},
    fmt,
    hash::Hash,
    ops::Deref,
};

#[cfg(feature = "threadpool")]
use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};

#[cfg(not(feature = "threadpool"))]
use std::{
    cell::{Ref, RefCell},
    rc::Rc,
};

pub type IndexedPort = (usize, Port);

#[derive(Clone)]
pub struct Port {
    #[cfg(not(feature = "threadpool"))]
    pub e: Rc<RefCell<Expr>>,

    #[cfg(feature = "threadpool")]
    pub e: Arc<RwLock<Expr>>,

    pub id: usize,
}

impl Eq for Port {}

impl Ord for Port {
    fn cmp(&self, o: &Self) -> Ordering {
        self.id.cmp(&o.id)
    }
}

impl PartialEq for Port {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl PartialOrd for Port {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.id.partial_cmp(&other.id)
    }
}

impl TreeCursor<Port> for Port {
    fn hash(&self) -> usize {
        self.id
    }

    fn value(&self) -> Port {
        self.clone()
    }

    fn children(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(
            self.iter_ports()
                .into_iter()
                .filter_map(|x| x)
                .map(|(_, x)| x),
        )
    }
}

impl VisualDebug for Port {
    fn node_id(&self) -> usize {
        self.id
    }

    fn node_label(&self) -> String {
        format!("{} ({})", self.borrow().name(), self.id,)
    }

    fn node_color(&self) -> String {
        if self
            .borrow()
            .primary_port()
            .map(|(port, _)| port == &0)
            .unwrap_or_default()
        {
            "red".to_owned()
        } else {
            "black".to_owned()
        }
    }

    fn conns(&self) -> impl Iterator<Item = String> {
        self.iter_ports()
            .into_iter()
            .enumerate()
            .filter_map(|(i, x)| Some((i, x?)))
            .map(|(i, (port, p))| {
                format!(
                    "{} -- {} [label=\"({}, {})\"]",
                    self.node_id(),
                    p.node_id(),
                    i,
                    port
                )
            })
            .collect::<Vec<_>>()
            .into_iter()
    }
}

impl Port {
    pub fn deep_clone(&self, names: &NameIter) -> Port {
        let mut new_for_id: BTreeMap<usize, Port> = [self.clone()]
            .into_iter()
            .chain(self.iter_tree_visitor())
            .map(|port| (port.id, port.borrow().clone().into_port(names)))
            .collect();

        // Wire nodes
        self.iter_tree().for_each(|port| {
            let new_self = new_for_id.get(&port.id).clone().unwrap();

            port.iter_ports()
                .into_iter()
                .enumerate()
                .filter_map(|(port, x)| Some((port, x?)))
                .for_each(|(port_self, (port_other, other))| {
                    let new_other = new_for_id.get(&other.id).clone().unwrap();

                    new_other
                        .borrow_mut()
                        .insert_port_i(port_other, Some((port_self, new_self.clone())));
                    new_self
                        .borrow_mut()
                        .insert_port_i(port_self, Some((port_other, new_other.clone())));
                })
        });

        new_for_id.remove(&self.id).unwrap()
    }

    pub fn checksum(&self) {
        self.iter_tree().for_each(|x| {
            x.iter_ports()
                .into_iter()
                .map(|x| x.unwrap())
                .for_each(|(port, p)| {
                    tracing::trace!("checksum context: {:?} {:?} in {}", x, p, port);

                    assert!(p
                        .iter_ports()
                        .into_iter()
                        .nth(port)
                        .flatten()
                        .unwrap()
                        .1
                        .ptr_eq(&x));
                });
        });
    }

    pub fn unroot(&self) -> Option<IndexedPort> {
        let old_primary_port = self.borrow().primary_port().cloned();
        self.borrow_mut().set_primary_port(None);

        old_primary_port
    }

    pub fn orient(&self) -> Self {
        let mut active_pairs = self
            .iter_tree()
            .filter_map(|x| x.try_as_active_pair())
            .filter(|((_, a), (_, b))| {
                a.borrow().as_var().is_none() && b.borrow().as_var().is_none()
            })
            .map(|((_, a), (_, b))| if a.id < b.id { a } else { b })
            .collect::<Vec<_>>();
        active_pairs.sort_by(|a, b| a.id.cmp(&b.id));

        if let Some(first) = active_pairs.into_iter().next() {
            return first;
        }

        let mut roots = self
            .iter_tree()
            .filter(|x| {
                x.borrow()
                    .as_var()
                    .map(|v| v.name.0.starts_with("v"))
                    .unwrap_or_default()
            })
            .collect::<Vec<_>>();
        roots.sort_by(|a, b| {
            let (a_bor, b_bor) = (a.borrow(), b.borrow());
            let (a_var, b_var) = a_bor.as_var().zip(b_bor.as_var()).unwrap();

            a_var.name.cmp(&b_var.name)
        });

        let root = roots.into_iter().next().unwrap();

        let borrow = root.borrow();
        borrow
            .primary_port()
            .expect("missing root parent")
            .1
            .clone()
    }

    pub fn alpha_eq(&self, other: &Port) -> bool {
        // TODO: this is awful
        let a = self
            .iter_children()
            .filter(|x| x.borrow().as_var().is_none())
            .map(|x| x.borrow().description())
            .collect::<BTreeSet<_>>();
        let b = other
            .iter_children()
            .filter(|x| x.borrow().as_var().is_none())
            .map(|x| x.borrow().description())
            .collect::<BTreeSet<_>>();

        tracing::trace!("found:    {:?}", a);
        tracing::trace!("expected: {:?}", b);

        a == b
    }

    #[cfg(not(feature = "threadpool"))]
    pub fn as_ptr(&self) -> *const RefCell<Expr> {
        Rc::as_ptr(&self.e)
    }

    #[cfg(feature = "threadpool")]
    pub fn as_ptr(&self) -> *const RwLock<Expr> {
        Arc::as_ptr(&self.e)
    }

    #[cfg(not(feature = "threadpool"))]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.e, &other.e)
    }

    #[cfg(feature = "threadpool")]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.e, &other.e)
    }

    #[cfg(not(feature = "threadpool"))]
    pub fn new(e: Expr, id: usize) -> Self {
        Self {
            e: Rc::new(RefCell::new(e)),
            id,
        }
    }

    #[cfg(feature = "threadpool")]
    pub fn new(e: Expr, id: usize) -> Self {
        Self {
            e: Arc::new(RwLock::new(e)),
            id,
        }
    }

    #[cfg(feature = "threadpool")]
    pub fn borrow(&self) -> RwLockReadGuard<'_, Expr> {
        self.e.read().unwrap()
    }

    #[cfg(not(feature = "threadpool"))]
    pub fn borrow(&self) -> Ref<'_, Expr> {
        (&self.e).try_borrow().unwrap()
    }

    #[cfg(feature = "threadpool")]
    pub fn borrow_mut(&self) -> RwLockWriteGuard<'_, Expr> {
        self.e.try_write().unwrap()
    }
}

#[cfg(not(feature = "threadpool"))]
impl Deref for Port {
    type Target = Rc<RefCell<Expr>>;

    fn deref(&self) -> &Self::Target {
        &self.e
    }
}

#[cfg(feature = "threadpool")]
impl Deref for Port {
    type Target = Arc<RwLock<Expr>>;

    fn deref(&self) -> &Self::Target {
        &self.e
    }
}

impl fmt::Display for Port {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut seen: BTreeSet<usize> = Default::default();

        fn fmt_expr_ports(
            seen: &mut BTreeSet<usize>,
            e: &Port,
            ports: Vec<IndexedPort>,
        ) -> Option<String> {
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
                        .map(|(port, p)| {
                            fmt_expr_ports(
                                seen,
                                p,
                                [p.borrow().primary_port().cloned()]
                                    .into_iter()
                                    .chain(p.borrow().aux_ports().into_iter().cloned())
                                    .filter_map(|x| x)
                                    .collect::<Vec<_>>(),
                            )
                            .map(|port_str| {
                                if p.borrow().is_var() {
                                    port_str
                                } else {
                                    format!("{}#{}", port_str, port)
                                }
                            })
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
                        .map(|(port, p)| fmt_expr_ports(
                            seen,
                            p,
                            [p.borrow().primary_port().cloned()]
                                .into_iter()
                                .chain(p.borrow().aux_ports().into_iter().cloned())
                                .filter_map(|x| x)
                                .collect::<Vec<_>>(),
                        )
                        .map(|port_str| {
                            if p.borrow().is_var() {
                                port_str
                            } else {
                                format!("{}#{}", port_str, port)
                            }
                        }))
                        .filter_map(|x| x)
                        .collect::<Vec<_>>()
                        .join(", "),
                ),
                Expr::Constr(_) => format!(
                    "Constr[@{}]({})",
                    e.id,
                    ports
                        .iter()
                        .map(|(port, p)| fmt_expr_ports(
                            seen,
                            p,
                            [p.borrow().primary_port().cloned()]
                                .into_iter()
                                .chain(p.borrow().aux_ports().into_iter().cloned())
                                .filter_map(|x| x)
                                .collect::<Vec<_>>(),
                        )
                        .map(|port_str| {
                            if p.borrow().is_var() {
                                port_str
                            } else {
                                format!("{}#{}", port_str, port)
                            }
                        }))
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
                    &rhs.1,
                    rhs.1
                        .borrow()
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

impl fmt::Debug for Port {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ports = self.iter_ports();
        let ports_debug = ports
            .into_iter()
            .skip(1)
            .map(|p| {
                p.map(|(p, port)| {
                    format!(
                        "{} @ 0x{} in {}",
                        port.borrow().name().to_owned(),
                        port.id,
                        p
                    )
                })
                .unwrap_or("empty".to_owned())
            })
            .collect::<Vec<_>>();

        f.debug_struct("Port")
            .field("name", &self.borrow().name())
            .field("id", &self.id)
            .field(
                "primary_port",
                &self.iter_ports().into_iter().next().map(|p| {
                    p.map(|(p, port)| {
                        format!(
                            "{} @ 0x{} in {}",
                            port.borrow().name().to_owned(),
                            port.id,
                            p
                        )
                    })
                    .unwrap_or("empty".to_owned())
                }),
            )
            .field("aux_ports", &ports_debug)
            .finish()
    }
}

impl Port {
    pub fn iter_ports(&self) -> impl IntoIterator<Item = Option<IndexedPort>> {
        [self.borrow().primary_port()]
            .into_iter()
            .chain(self.borrow().aux_ports().into_iter().map(|x| x.as_ref()))
            .map(|x| x.cloned())
            .collect::<Vec<_>>()
    }

    pub fn iter_tree(&self) -> impl Iterator<Item = Port> {
        PortTreeWalker::new([self.clone()].into_iter())
    }

    pub fn iter_tree_visitor(&self) -> TreeVisitor<Port, Port> {
        TreeVisitor::new(self.clone())
    }

    pub fn iter_children(&self) -> impl Iterator<Item = Port> {
        PortTreeWalker {
            seen: BTreeSet::from_iter([self.id]),
            to_visit: self
                .iter_ports()
                .into_iter()
                .skip(1)
                .filter_map(|x| x.map(|(_, x)| x))
                .collect(),
        }
    }

    pub fn try_as_wired_vars(&self) -> Option<(Port, Port)> {
        let self_port = self.borrow();
        let primary_port = self_port.primary_port()?;
        let port = primary_port.1.borrow();

        if !primary_port.1.borrow().is_var() || !self_port.is_var() {
            return None;
        }

        match &*port {
            Expr::Var(v) => {
                if v.port
                    .as_ref()
                    .map(|p| self.ptr_eq(&p.1))
                    .unwrap_or_default()
                {
                    Some((self.clone(), primary_port.1.clone()))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn try_as_active_pair(&self) -> Option<(IndexedPort, IndexedPort)> {
        let self_port = self.borrow();
        let primary_port = self_port.primary_port()?;
        let port = primary_port;

        if port.0 == 0 && primary_port.1.borrow().as_var().is_none() {
            Some(((0, self.clone()), primary_port.clone()))
        } else {
            None
        }
    }

    /// Sets all free ports to new vars
    pub fn fill_aux_vars(&self, names: &mut NameIter) {
        let n_ports = self.borrow().aux_ports().len();

        for i in 0..n_ports {
            let v: Port = Expr::Var(Var {
                name: Ident(names.next()),
                port: Some((i, self.clone())),
            })
            .into_port(names);

            self.borrow_mut().push_aux_port(Some((0, v)));
        }
    }
}

pub struct PortTreeWalker {
    seen: BTreeSet<usize>,
    to_visit: VecDeque<Port>,
}

impl PortTreeWalker {
    pub fn new(i: impl Iterator<Item = Port>) -> Self {
        Self {
            seen: Default::default(),
            to_visit: i.into_iter().collect(),
        }
    }
}

impl Iterator for PortTreeWalker {
    type Item = Port;

    fn next(&mut self) -> Option<Self::Item> {
        self.to_visit = self
            .to_visit
            .drain(..)
            .skip_while(|n| !n.borrow().is_var() && self.seen.contains(&n.id))
            .collect();
        let next = self.to_visit.pop_front()?;

        self.seen.insert(next.id);

        self.to_visit.extend(
            next.iter_ports()
                .into_iter()
                .filter_map(|x| x)
                .filter(|(_, p)| !self.seen.contains(&p.id))
                .map(|(_, x)| x),
        );

        Some(next)
    }
}

const EMPTY_AUX_PORTS: [Option<IndexedPort>; 2] = [None, None];

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
    Idx,
    LeftBracket,
    RightBracket,
    Comma,
    Digit(usize),
    Tilde,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Idx => write!(f, "#"),
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
            Self::Tilde => write!(f, "~"),
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
    pub fn description(&self) -> (String, Vec<Option<(usize, String)>>) {
        let name = self.name();
        let ports = [self.primary_port()]
            .into_iter()
            .chain(self.aux_ports().iter().map(|x| x.as_ref()))
            .filter(|x| x.map(|x| !x.1.borrow().is_var()).unwrap_or(true))
            .map(|x| x.map(|(p, port)| (*p, port.borrow().name())))
            .collect();

        (name, ports)
    }

    pub fn name(&self) -> String {
        match self {
            Self::Era(_) => String::from("Era"),
            Self::Dup(_) => String::from("Dup"),
            Self::Constr(_) => String::from("Constr"),
            Self::Var(v) => v.name.0.clone(),
        }
    }

    pub fn is_var(&self) -> bool {
        matches!(self, Self::Var(_))
    }

    pub fn is_agent(&self) -> bool {
        !self.is_var()
    }

    pub fn as_var(&self) -> Option<&Var> {
        match &self {
            Self::Var(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_constr(&self) -> Option<&Constructor> {
        match &self {
            Self::Constr(c) => Some(c),
            _ => None,
        }
    }
}

impl Expr {
    pub fn into_port(self, namer: &NameIter) -> Port {
        Port::new(self, namer.next_id())
    }

    pub fn into_port_named(self, id: usize) -> Port {
        Port::new(self, id)
    }

    pub fn set_aux_ports(&mut self, ports: [Option<IndexedPort>; 2]) {
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

    pub fn set_primary_port(&mut self, port: Option<IndexedPort>) {
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
    pub fn primary_port(&self) -> Option<&IndexedPort> {
        match &self {
            Self::Era(e) => &e.primary_port,
            Self::Dup(d) => &d.primary_port,
            Self::Constr(c) => &c.primary_port,
            Self::Var(v) => &v.port,
        }
        .as_ref()
    }

    pub fn aux_ports(&self) -> &[Option<IndexedPort>] {
        match self {
            Self::Era(_) => &[],
            Self::Dup(d) => &d.aux_ports,
            Self::Constr(c) => &c.aux_ports,
            Self::Var(_) => &[],
        }
    }

    pub fn push_aux_port(&mut self, val: Option<IndexedPort>) {
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

    pub fn insert_port_i(&mut self, index: usize, val: Option<IndexedPort>) {
        match self {
            Self::Era(e) => {
                assert_eq!(index, 0);

                e.primary_port = val;
            }
            Self::Constr(c) => match index {
                0 => {
                    c.primary_port = val;
                }
                1 => {
                    c.aux_ports[0] = val;
                }
                2 => {
                    c.aux_ports[1] = val;
                }
                _ => panic!("invalid port"),
            },
            Self::Dup(c) => match index {
                0 => {
                    c.primary_port = val;
                }
                1 => {
                    c.aux_ports[0] = val;
                }
                2 => {
                    c.aux_ports[1] = val;
                }
                _ => panic!("invalid port"),
            },
            Self::Var(v) => {
                assert_eq!(index, 0);

                v.port = val;
            }
        }
    }

    pub fn insert_aux_port(&mut self, index: usize, val: Option<IndexedPort>) {
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

    pub fn swap_conn(&mut self, pos: usize, new: Option<IndexedPort>) {
        if pos == 0 {
            self.set_primary_port(new);

            return;
        }

        match self {
            Self::Era(_) | Self::Var(_) => {}
            Self::Constr(_) | Self::Dup(_) => match pos {
                1 => {
                    self.set_aux_ports([new, self.aux_ports()[1].clone()]);
                }
                2 => {
                    self.set_aux_ports([self.aux_ports()[0].clone(), new]);
                }
                _ => {}
            },
        }
    }
}

#[derive(Default, Debug, Clone)]
pub struct Eraser {
    pub primary_port: Option<IndexedPort>,
}

impl Eraser {
    pub const fn new() -> Self {
        Self { primary_port: None }
    }
}

#[derive(Default, Debug, Clone)]
pub struct Duplicator {
    pub primary_port: Option<IndexedPort>,
    pub aux_ports: [Option<IndexedPort>; 2],
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
    pub primary_port: Option<IndexedPort>,
    pub aux_ports: [Option<IndexedPort>; 2],
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
    pub port: Option<IndexedPort>,
}
