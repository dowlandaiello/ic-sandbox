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

    builder.with_init_net(e).finish().reduce()
}
