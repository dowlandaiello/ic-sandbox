# DVM

Dowland's Virtual Machine: an interpreter based on a low-level intermediary representation "language" for the symetric interaction combinators. Includes a reducer, `icc` for prototyping and proving purposes, in addition to an implementation of optimal lambda calculus reduction using the combinators.

## `icc` Usage

`icc` comes with three commands:
- `eval <FILE_NAME>` - reduces an interaction combinator expression to completion
- `dev` - enables a REPL with debugging and prototyping tools
- `check` - checks a .d file for proper syntax
