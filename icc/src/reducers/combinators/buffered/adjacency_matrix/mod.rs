use super::{
    super::{Conn, Ptr, Reducer},
    Cell, NetBuffer,
};
use crate::parser::ast_combinators::Port;

mod atomic_reprs;
mod matrix_buffer;
mod reducer;

pub use reducer::{BufferedMatrixReducer, ReducerBuilder};

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
