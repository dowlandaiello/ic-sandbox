# inetlang

Low-level intermediary representation "language" for general interaction calculus-based languages. Supports general interaction net rule programs, including but not limited to interaction combinators. Includes a single-threaded reducer, `icc` for prototyping and proving purposes.

## Components

| Name | Crate / Binary Name | Description | Source Root |
|---|---|---|---|
| INetLang Parser / AST | inetlib | AST representing programs and expressions written in interaction calculus.<br>Comes with a parser written with Chumsky. | src/lib.rs |
| INetLang Interpreter | icc | Interpreter and REPL for reducing interaction calculus programs given a rule set.<br>Includes a dev repl with expression and net debugging capabilities. | src/main.rs |
