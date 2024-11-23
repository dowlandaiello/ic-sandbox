# DEVM

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
| INetLang Parser / AST | inetlib | AST representing programs and expressions written in interaction calculus.<br>Comes with a parser written with Chumsky. | `src/lib.rs` |
| INetLang Interpreter | icc | Interpreter and REPL for reducing interaction calculus programs given a rule set.<br>Includes a dev repl with expression and net debugging capabilities. | `src/main.rs` |

### Why Single-Threaded Reducer

The inclusion of a single-threaded reducer may seem questionable considering the highly parallel nature of interaction nets. However, this reducer is meant for prototyping and debugging purposes. Furthermore, it may find utility in single-threaded environments where access to system resources and interfaces is minimal (e.g., WebAssembly).

## Current Limitations

This project is still very bleeding edge, and needs to be refactored significantly. Test coverage needs to be improved, and more examples need to be tried.

## `icc` Usage

`icc` comes with three commands:
- `compile` - produces a bincode representation of a parsed AST from an input file
- `eval` - reduces an input file containing a ruleset and expr, printing the resulting expr to stdout
- `dev` - REPL with debugging and step-by-step reduction capabilities

## Todo

- [ ] Syntax rework to implement original lafont paper spec
