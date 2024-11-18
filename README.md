# inetlang

Low-level intermediary representation "language" for general interaction calculus-based languages. Supports general interaction net rule programs, including but not limited to interaction combinators. Includes a single-threaded reducer, `icc` for prototyping and proving purposes.

## Example: Addition Net

Represented here is a set of interaction net rules and an active pair which represent addition.

```
Add[x, y] >< Z => x ~ y
S[x] >< Add[y, z] => Add[y, S[z]] ~ x
Add[Z, y] >< Z
```

This representation is borrowed from a paper "[Compilation of Interaction Nets](https://core.ac.uk/download/pdf/82756233.pdf)," by Hassan et al.

## Components

| Name | Crate / Binary Name | Description | Source Root |
|---|---|---|---|
| INetLang Parser / AST | inetlib | AST representing programs and expressions written in interaction calculus.<br>Comes with a parser written with Chumsky. | src/lib.rs |
| INetLang Interpreter | icc | Interpreter and REPL for reducing interaction calculus programs given a rule set.<br>Includes a dev repl with expression and net debugging capabilities. | src/main.rs |

## Current Limitations

This project is still very bleeding edge, and needs to be refactored significantly. Test coverage needs to be improved, and more examples need to be tried.
