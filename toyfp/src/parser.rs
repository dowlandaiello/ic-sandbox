use ast_ext::Spanned;
use chumsky::{
    error::{LabelError, RichPattern},
    prelude::*,
    util::MaybeRef,
};
use std::{collections::BTreeSet, fmt};

const COMMENT_STR: &str = "--";

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    Def { bind_name: String, def: Expr },
    Expr(Expr),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Def { bind_name, def } => {
                write!(f, "{} = {}", bind_name, def)
            }
            Self::Expr(e) => {
                write!(f, "{}", e)
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Id(Spanned<String>),
    Abstraction {
        bind_id: Spanned<String>,
        bind_ty: Spanned<Box<Expr>>,
        body: Spanned<Box<Expr>>,
    },
    Application {
        lhs: Spanned<Box<Expr>>,
        rhs: Spanned<Box<Expr>>,
    },
}

impl Expr {
    pub fn free_vars<'a>(&'a self) -> BTreeSet<&'a str> {
        match &self {
            Self::Id(i) => BTreeSet::from_iter([i.as_str()]),
            Self::Abstraction { bind_id, body, .. } => {
                let mut all = body.free_vars();
                all.remove(bind_id.as_str());

                all
            }
            Self::Application { lhs, rhs } => {
                let mut lhs_free = lhs.free_vars();
                lhs_free.extend(&rhs.free_vars());

                lhs_free
            }
        }
    }

    pub fn contains_var(&self, v: &str) -> bool {
        self.free_vars().iter().any(|x| x == &v)
    }

    pub fn contains_lambda(&self) -> bool {
        match self {
            Self::Id(_) => false,
            Self::Abstraction { .. } => true,
            Self::Application { lhs, rhs } => lhs.contains_lambda() || rhs.contains_lambda(),
        }
    }

    pub fn as_id(&self) -> Option<&str> {
        match self {
            Self::Id(s) => Some(s),
            _ => None,
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Id(s) => write!(f, "{}", s.0),
            Self::Abstraction {
                bind_id,
                bind_ty,
                body,
            } => write!(f, "\\{}:{}.{}", bind_id.0, bind_ty.0, body.0),
            Self::Application { lhs, rhs } => {
                write!(f, "({} {})", lhs.0, rhs.0)
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Token {
    LeftParen,
    RightParen,
    Lambda,
    Ident(String),
    Dot,
    Eq,
    Newline,
    Space,
    Colon,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LeftParen => write!(f, "("),
            Self::RightParen => write!(f, "("),
            Self::Lambda => write!(f, "\\"),
            Self::Ident(s) => write!(f, "{}", s),
            Self::Dot => write!(f, "."),
            Self::Eq => write!(f, "="),
            Self::Newline => write!(f, "\n"),
            Self::Space => write!(f, " "),
            Self::Colon => write!(f, ":"),
        }
    }
}

pub fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<Spanned<Token>>, extra::Err<Rich<'src, char>>> {
    let comment = just(COMMENT_STR)
        .then(any().and_is(just('\n').not()).repeated())
        .padded();

    let left_paren = just("(").map(|_| Token::LeftParen);
    let right_paren = just(")").map(|_| Token::RightParen);
    let lambda = just("\\").map(|_| Token::Lambda);
    let ident = text::ident().map(|i: &str| Token::Ident(i.to_owned()));
    let dot = just(".").map(|_| Token::Dot);
    let eq = just("=").map(|_| Token::Eq);
    let newline = text::newline().map(|_| Token::Newline);
    let space = just(" ").map(|_| Token::Space);
    let colon = just(":").map(|_| Token::Colon);

    let tok = choice((
        left_paren,
        right_paren,
        lambda,
        ident,
        dot,
        eq,
        newline,
        space,
        colon,
    ));

    tok.map_with(|tok, e| {
        Spanned(
            tok,
            {
                let x: SimpleSpan = e.span();
                x
            }
            .into_range(),
        )
    })
    .padded_by(comment.repeated())
    .recover_with(skip_then_retry_until(any().ignored(), end()))
    .repeated()
    .collect()
    .then_ignore(end())
}

pub fn parser<'src>(
) -> impl Parser<'src, &'src [Spanned<Token>], Vec<Spanned<Stmt>>, extra::Err<Rich<'src, Spanned<Token>>>>
{
    let span_just = move |val: Token| {
        let v = val.clone();

        select! {
            Spanned(x, s) if x == v => Spanned({ let z: Token = x; z }, s)
        }
        .map_err(move |e: Rich<_>| {
            <Rich<_> as LabelError<&'src [Spanned<Token>], RichPattern<_>>>::merge_expected_found(
                e.clone(),
                [RichPattern::Token(MaybeRef::Val(Spanned(
                    val.clone(),
                    e.clone().span().into_range(),
                )))],
                None,
                *e.span(),
            )
        })
    };
    let id = select! {
    Spanned(Token::Ident(i), s) => Spanned(Expr::Id(Spanned(i, s.clone())), s),
    };

    let expr = recursive(|expr| {
        let abstraction = span_just(Token::Lambda)
            .ignore_then(select! {
            Spanned(Token::Ident(i), s) => Spanned(i, s)
            })
            .then_ignore(span_just(Token::Colon))
            .then(expr.clone())
            .then_ignore(span_just(Token::Dot))
            .then(expr.clone())
            .map(
                |((bind_id, bind_ty), body): ((Spanned<String>, Spanned<Expr>), Spanned<Expr>)| {
                    Spanned(
                        Expr::Abstraction {
                            bind_id: bind_id.clone(),
                            bind_ty: Spanned(Box::new(bind_ty.0), bind_ty.1),
                            body: Spanned(Box::new(body.0), body.1),
                        },
                        bind_id.1,
                    )
                },
            );
        let application = span_just(Token::LeftParen)
            .ignore_then(expr.clone())
            .clone()
            .foldl(
                span_just(Token::Space)
                    .ignore_then(expr)
                    .repeated()
                    .at_least(1),
                |a: Spanned<Expr>, b: Spanned<Expr>| {
                    Spanned(
                        Expr::Application {
                            lhs: Spanned(Box::new(a.0), a.1.clone()),
                            rhs: Spanned(Box::new(b.0), b.1),
                        },
                        a.1,
                    )
                },
            )
            .then_ignore(span_just(Token::RightParen));
        let nested_app = span_just(Token::LeftParen)
            .ignore_then(application.clone())
            .then_ignore(span_just(Token::RightParen));

        choice((application, id, abstraction, nested_app))
    });

    let def = select! {
    Spanned(Token::Ident(i), s) => Spanned(i, s)
    }
    .then_ignore(span_just(Token::Space).repeated())
    .then_ignore(span_just(Token::Eq))
    .then_ignore(span_just(Token::Space).repeated())
    .then(expr.clone())
    .map(|(bind, def)| {
        Spanned(
            Stmt::Def {
                bind_name: bind.0,
                def: def.0,
            },
            bind.1,
        )
    });

    def.then_ignore(
        span_just(Token::Newline)
            .repeated()
            .at_least(1)
            .collect::<Vec<_>>(),
    )
    .repeated()
    .collect::<Vec<_>>()
    .then(expr.map_with(|e, err| {
        Spanned(
            Stmt::Expr(e.0),
            {
                let x: SimpleSpan = err.span();
                x
            }
            .into_range(),
        )
    }))
    .then_ignore(span_just(Token::Newline).repeated().ignore_then(end()))
    .map(|(mut defs, entry)| {
        defs.push(entry);

        defs
    })
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse_ok() {
        let cases = [
            ("a", "a"),
            ("(a b)", "(a b)"),
            ("\\a:_.a", "\\a:_.a"),
            ("\\f:_.x", "\\f:_.x"),
            ("(\\a:_.a a)", "(\\a:_.a a)"),
            ("(\\a:_.\\b:_.a c d)", "((\\a:_.\\b:_.a c) d)"),
            (
                "id = \\x:_.x
(id x)",
                "id = \\x:_.x
(id x)",
            ),
            (
                "nil = \\c:_.\\n:_.n
z = \\f:_.\\g:_.g
one = \\f:_.\\g:_.(f g)
cons = \\h:_.\\t:_.\\c:_.\\n:_.(c h (t c n))
nth = \\n:_.\\l:_.(l \\x:_.\\r:_.(n \\z:_.x r) \\z:_.z)
my_list = \\c:_.\\n:_.(c x (c y (c z n)))

(nth one my_list)",
                "nil = \\c:_.\\n:_.n
z = \\f:_.\\g:_.g
one = \\f:_.\\g:_.(f g)
cons = \\h:_.\\t:_.\\c:_.\\n:_.((c h) ((t c) n))
nth = \\n:_.\\l:_.((l \\x:_.\\r:_.((n \\z:_.x) r)) \\z:_.z)
my_list = \\c:_.\\n:_.((c x) ((c y) ((c z) n)))
((nth one) my_list)",
            ),
        ];

        for (case, expected) in cases {
            let lexed = lexer().parse(case).unwrap();

            assert_eq!(
                parser()
                    .parse(&lexed)
                    .unwrap()
                    .iter()
                    .map(|stmt| stmt.to_string())
                    .collect::<Vec<_>>()
                    .join("\n"),
                expected
            );
        }
    }
}
