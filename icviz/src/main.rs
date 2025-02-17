use chumsky::Parser;
use inetlib::parser::{
    ast_combinators::Port,
    parser_combinators::{lexer, parser},
};
use petgraph::{
    dot::{Config, Dot},
    Graph,
};
use std::{
    collections::BTreeMap,
    io::{stdin, Read},
};

fn main() {
    let mut raw_expr = String::new();
    let _ = stdin()
        .read_to_string(&mut raw_expr)
        .expect("failed to read input expression");

    let prog = parser()
        .parse(lexer().parse(raw_expr.clone()).expect("lexer error"))
        .expect("parser error");

    let fmt_port = |(port, p): &(usize, Port)| {
        format!("<p>{} @ 0x{} in {}</p>", p.borrow().name(), p.id, port,)
    };

    let mut graph = Graph::new_undirected();

    let nodes_for_id: BTreeMap<usize, _> = prog[0]
        .iter_tree()
        .map(|x| {
            (
                x.id,
                graph.add_node(format!("{}: {}", x.borrow().name(), x.id)),
            )
        })
        .collect();
    prog[0].iter_tree().for_each(|x| {
        x.iter_ports()
            .into_iter()
            .enumerate()
            .filter_map(|(i, x)| Some((i, x?)))
            .for_each(|(self_port, (other_port, other_p))| {
                let self_node = nodes_for_id[&x.id];
                let other_node = nodes_for_id[&other_p.id];

                if graph.contains_edge(self_node, other_node)
                    || graph.contains_edge(other_node, self_node)
                {
                    return;
                }

                graph.add_edge(
                    self_node,
                    other_node,
                    format!("({}, {})", self_port, other_port),
                );
            });
    });

    println!("{:?}", Dot::with_config(&graph, &[]));
}
