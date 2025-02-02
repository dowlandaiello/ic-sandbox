use inetlib::parser::ast_combinators::Port;

pub trait Engine {
    fn goal(&self) -> Port;

    fn applicand(&self) -> Port;

    fn curr(&self) -> Port;

    fn step(&mut self);
}
