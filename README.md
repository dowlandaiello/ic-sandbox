# DVM

Low-level intermediary representation "language" for the symetric interaction combinators. Includes a single-threaded reducer, `icc` for prototyping and proving purposes.

### Why Single-Threaded Reducer

The inclusion of a single-threaded reducer may seem questionable considering the highly parallel nature of interaction nets. However, this reducer is meant for prototyping and debugging purposes. Furthermore, it may find utility in single-threaded environments where access to system resources and interfaces is minimal (e.g., WebAssembly).

## Current Limitations

This project is still very bleeding edge, and needs to be refactored significantly. Test coverage needs to be improved, and more examples need to be tried.

## `icc` Usage

`icc` comes with three commands:
