use inetlib::{
    parser::ast_combinators::{Constructor, Expr},
    reducers::combinators::reduce_dyn,
};
use rayon::prelude::*;
use std::{env::args, time::Instant};

fn main() {
    let n = args().last().unwrap().parse::<u128>().unwrap();

    let top = Expr::Constr(Constructor::new()).into_port_named(0);
    let bottom = Expr::Constr(Constructor::new()).into_port_named(1);

    top.borrow_mut().set_primary_port(Some(bottom.clone()));
    bottom.borrow_mut().set_primary_port(Some(top.clone()));

    let mut insert = vec![top.clone(), bottom.clone()];

    for _ in 0..n {
        insert = insert
            .par_drain(0..)
            .enumerate()
            .fold(
                || Vec::new(),
                |mut acc, (i, to_insert)| {
                    let left = Expr::Constr(Constructor::new()).into_port_named(2 * i);
                    let right = Expr::Constr(Constructor::new()).into_port_named(2 * i);

                    left.borrow_mut().set_primary_port(Some(to_insert.clone()));
                    right.borrow_mut().set_primary_port(Some(to_insert.clone()));

                    to_insert
                        .borrow_mut()
                        .set_aux_ports([Some(left.clone()), Some(right.clone())]);

                    acc.extend([left, right]);

                    acc
                },
            )
            .flatten()
            .collect::<Vec<_>>();
    }

    let bench_with = top.to_string();
    println!(
        "starting bench with: {} (len = {})",
        &bench_with,
        bench_with.len()
    );

    let start = Instant::now();

    let res = reduce_dyn(&top).unwrap();

    let end = Instant::now();

    println!(
        "result: {}",
        res.iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    );
    println!("time: {}ms", end.duration_since(start).as_millis());
}
