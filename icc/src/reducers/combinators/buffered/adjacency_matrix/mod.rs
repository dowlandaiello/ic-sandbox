use super::{
    super::{Conn, Ptr, Reducer},
    Cell, NetBuffer,
};
use crate::parser::ast_combinators::Port;

pub(crate) mod atomic_reprs;
mod matrix_buffer;
mod reducer;

pub use reducer::{BufferedMatrixReducer, ReducerBuilder};

pub fn reduce_dyn(e: &Port) -> Vec<Port> {
    let builder = ReducerBuilder::default();

    let mut results = builder
        .with_init_net(e)
        .finish()
        .reduce()
        .into_iter()
        .filter(|net| net.iter_tree().any(|x| x.borrow().as_var().is_some()))
        .collect::<Vec<_>>();
    let n_roots = |p: Port| Some(p.borrow().as_var()?.name.starts_with("v"));
    results.sort_by(|a, b| {
        b.iter_tree()
            .filter_map(n_roots)
            .count()
            .cmp(&a.iter_tree().filter_map(n_roots).count())
    });

    results
}
