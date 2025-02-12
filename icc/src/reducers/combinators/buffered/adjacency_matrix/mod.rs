use super::{
    super::{Conn, Ptr, Reducer},
    Cell, NetBuffer,
};
use crate::parser::ast_combinators::Port;

mod atomic_reprs;
mod matrix_buffer;
mod reducer;

use reducer::BufferedMatrixReducer;

pub fn reduce_dyn(e: &Port) -> Vec<Port> {
    BufferedMatrixReducer::from(e.clone()).reduce()
}
