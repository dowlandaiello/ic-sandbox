use super::{
    ast_combinators::{Constructor, Duplicator, Eraser, Expr, Port, Token, Var},
    ast_lafont::Ident,
    parser_lafont::{Span, Spanned},
};
use chumsky::prelude::*;

pub fn lexer() -> impl Parser<char, Vec<Spanned<Token>>, Error = Simple<char>> {
    let era = just("Era").map(|_| Token::Era);
    let constr = just("Constr").map(|_| Token::Constr);
    let dup = just("Dup").map(|_| Token::Dup);
    let comma = just(",").map(|_| Token::Comma);
    let left_paren = just("(").map(|_| Token::LeftParen);
    let right_paren = just(")").map(|_| Token::RightParen);
    let ident = text::ident().map(|s: String| Token::Ident(s.to_owned()));
    let active_pair = just("><").map(|_| Token::ActivePair);

    let token = choice((
        comma,
        left_paren,
        right_paren,
        choice((era, constr, dup)).or(ident),
        active_pair,
    ));

    token
        .padded_by(text::whitespace())
        .map_with_span(|tok, e: Span| Spanned(tok, e))
        .repeated()
        .then_ignore(end())
}

pub fn parser() -> impl Parser<Spanned<Token>, Vec<Spanned<Port>>, Error = Simple<Spanned<Token>>> {
    let span_just = move |val: Token| {
        filter::<Spanned<Token>, _, Simple<Spanned<Token>>>(move |tok: &Spanned<Token>| {
            tok.0 == val
        })
    };
    let agent = recursive(|expr| {
        select! {
            Spanned(Token::Era, span) => Spanned(<Expr as Into<Port>>::into(Expr::Era(Eraser::new())), span),
	    Spanned(Token::Constr, span) => Spanned(<Expr as Into<Port>>::into(Expr::Constr(Constructor::new())), span),
	    Spanned(Token::Dup, span) => Spanned(<Expr as Into<Port>>::into(Expr::Dup(Duplicator::new())), span),
        }
        .then_ignore(span_just(Token::LeftParen))
        .then(
            choice((
                expr,
                select! {Spanned(Token::Ident(s), span) => Spanned(<Expr as Into<Port>>::into(Expr::Var(Var {name: Ident(s), port: None})), span)}
            ))
            .separated_by(span_just(Token::Comma)).exactly(2)
        )
        .then_ignore(span_just(Token::RightParen))
        .map(|(expr, mut ports): (Spanned<Port>, Vec<Spanned<Port>>)| -> Spanned<Port> {
            Spanned(
                {
		    expr.0.borrow_mut().set_aux_ports([Some(ports.remove(0).0), Some(ports.remove(0).0)]);
		    expr.0
		},
		expr.1
            )
        })
    });
    let net = agent
        .clone()
        .then_ignore(span_just(Token::ActivePair))
        .then(agent)
        .map(|(lhs, rhs): (Spanned<Port>, Spanned<Port>)| {
            lhs.0.borrow_mut().set_primary_port(Some(rhs.0.clone()));
            rhs.0.borrow_mut().set_primary_port(Some(lhs.0.clone()));

            vec![lhs]
        });

    net.then_ignore(end())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_lex() {
        let cases = ["Constr() >< Era()"];

        for case in cases {
            let _ = lexer().parse(case).unwrap();
        }
    }
}
