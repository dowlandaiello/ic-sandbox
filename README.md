# Interaction Combinator Sandbox

Home of my self-directed research into the interaction combinators.

## Quick Start

```bash
git clone git@github.com:dowlandaiello/ic-playground.git
cargo run --bin toyfp dev

>> (\x.x)(a)
>> (\x.(\a.a)(x))(a)
>> (\x.(\a.x)(x))(a)
```

This will drop you into a lambda calculus shell utilizing a compiler from lambda calculus to the SK combinators to my interaction combinator intermediate representation language. Reduction is powered by my interaction combinator VM. Note that some partially applied functions are not decodeable yet. See *in progress*.

## Directory

- `icc` contains implementations of:
  - various parsers for interaction net and combinator syntaxes
  - various compilers, virtual machines, and interpreters for interaction nets and combinators
  - Most folders in this area of the repo are vestigal from incomplete previous attempts at implementing the VM. The current runtime resides in [`reducers/combinators/buffered/matrix_reducer/reducer.rs`](https://github.com/dowlandaiello/ic-sandbox/blob/master/icc/src/reducers/combinators/buffered/adjacency_matrix/reducer.rs). There is more work that needs to be done to improve performance, and I am working towards a lockless version of the runtime.
- `toyfp` contains a compiler from the SK combinators to my interaction combinator language and a compiler form lambda calculus to my interaction combinator language
- `ast-ext` contains some utilities for debugging tree-like or graphical structures, which are found frequently in the interaction combinator paradigm

## Usage

Two notable entrypoints are:

- The `icc` binary, which contains an interaction combinator REPL, interpreter, and syntax checker
- The `toyfp` binary, which contains a repl for the lambda calculus and the SK combinators based on a compiler to my interaction combinator IR language

Type `cargo run --bin icc dev` to enter the interaction combinator REPL. The syntax is relatively obscure and not easily readable, but is documented below.

Type `cargo run --bin toyfp dev` to enter the lambda calculus -> interaction combinator REPL. `(x)(y)` for application, `(\x.x)` for abstraction. **I recommend trying out this command with the `RUST_LOG=trace` environment variable set to demonstrate everything going on under the hood.** Doing so will display a log of the conversion to interaction combinators, all the steps in reduction, all the steps in compilation, and all the steps in decoding.

Type `cargo run --bin toyfp dev --sk` to enter the SK combinator -> interaction combinator REPL. Use S or K for the combinators, respectively and parenthesis for application: `((KS)K) => S`. **I recommend trying out this command with the `RUST_LOG=trace` environment variable set to demonstrate everything going on under the hood.** Doing so will display a log of the conversion to interaction combinators, all the steps in reduction, all the steps in compilation, and all the steps in decoding.

Type `cargo test` to run tests. One which is in-progress will fail in `toyfp`.

## IC IR Syntax

In modified, informal Backus-Naur Form notation:

```haskell
comment ::= -- <stuff>
id      ::= 0 | 1 | .. | n
ref     ::= @<id>
port    ::= <agent>#<port number in agent> | <ref>#<port number in agent>
var     ::= <C style identifier>
agent   ::= <var> | Constr[@<id>](<port>, <port>) | Dup[@<id>](<port>, <port>) | Era[@<id>](<port>)
expr    ::= <agent> | <agent> >< <agent>
program ::= <comment?>\n<expr>
```

where `><` represents an active pair.

For example:

```haskell
Constr[@1](a, b) >< Constr[@2](c, d)
-- => a ~ b
--    c ~ d
```

Another example:

```haskell
Constr[@1](Constr[@2](a, b)#0, Constr[@3](c, d)#0) >< Constr[@4](Constr[@5](e, f)#0, Constr[@6](g, h)#0)
```

## Limitations

All of these packages are in progress. `icc` has stabilized, and the runtime is working, featuring parallelism. More optimization needs to be done, but it is demonstrated to be correct via unit tests.

`toyfp` contains multiple compilers, the only semi-complete ones being the SK combinator and lambda calculus compilers. However, some expressions cannot be decoded properly (partially applied expressions that do not reduce to just S or K, Sxy, Sx, or Kx).

Extensive refactoring needs to be completed across the entire project, as many components were added ad-hoc, with little regard for structure or cleanliness, in an attempt to iterate rapidly.

## In Progress

I am currently working on generalizing the readbacking algorithm from interaction combinators to SK combinators. This should enable decoding more kinds of partially applied functions, enabling greater expressivity.
Furthermore, I have many optimizations in the pipeline for my interaction combinator runtime. I hope to finalize my BCKW compiler before this is completed.

## References

1. Mazza, Damiano. (2007). A denotational semantics for the symmetric interaction combinators. Mathematical Structures in Computer Science. 17. 527-562. 10.1017/S0960129507006135.
2. Taelin, Victor. HVM2: A PARALLEL EVALUATOR FOR INTERACTION COMBINATORS. https://github.com/higherOrderCO/hvm
3. Lafont, Y. (1997). Interaction Combinators. Inf. Comput., 137, 69-101.
4. Lafont Y. (1989). Interaction nets. In Proceedings of the 17th ACM SIGPLAN-SIGACT symposium on Principles of programming languages (POPL '90). Association for Computing Machinery, New York, NY, USA, 95–108. https://doi.org/10.1145/96709.96718
5. Hassan A. et al (2009). Compilation of Interaction Nets. Electronic Notes in Theoretical Computer Science, Volume 253, Issue 4, 2009, Pages 73-90, https://doi.org/10.1016/j.entcs.2009.10.018.

Among others which escape my mind at the moment.

## Thanks

Thanks for stopping by! :D
