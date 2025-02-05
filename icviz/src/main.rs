use chumsky::Parser;
use inetlib::parser::{
    ast_combinators::Port,
    parser_combinators::{lexer, parser},
};
use std::io::{stdin, Read};

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

    let agents = prog[0]
        .iter_tree()
        .map(|x| {
            format!(
                r#"<div className="agent">
{}
<h1>{}</h1>
<div className="body-port">
{}
</div>
</div>"#,
                x.borrow()
                    .primary_port()
                    .map(fmt_port)
                    .unwrap_or("empty".to_string()),
                format!("{} @ 0x{}", x.borrow().name(), x.id),
                x.borrow()
                    .aux_ports()
                    .iter()
                    .map(|x| x.as_ref().map(fmt_port).unwrap_or("empty".to_string()))
                    .collect::<Vec<_>>()
                    .join("\n"),
            )
        })
        .collect::<Vec<_>>()
        .join("\n");

    println!(
        "<html>
<head>
<title>{}</title>
<body>
{}
</body>
</html>",
        raw_expr.chars().take(20).collect::<String>(),
        agents
    );
}
