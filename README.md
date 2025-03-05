# Interaction Combinator Sandbox

Home of my self-directed research into the interaction combinators.

## Directory

- `icc` contains implementations of:
  - various parsers for interaction net and combinator syntaxes
  - various compilers, virtual machines, and interpreters for interaction nets and combinators
- `toyfp` contains a compiler from the SK combinators to my interaction combinator language
- `formalfp` contains a compiler written in Lean from the BCKW combinators to my interaction combinator language
- `astext` contains come utilities for debugging tree-like or graphical structures, which are found frequently in the interaction combinator paradigm

## Usage

Two notable endpoints are:

- The `icc` binary, which contains an interaction combinator REPL, interpreter, and syntax checker
- The `toyfp` binary, which contains a repl for the SK combinators targeting my interaction combinator VM

Type `cargo run --bin icc dev` to enter the interaction combinator REPL. The syntax is relatively obscure and not easily readable, but is documented below.

Type `cargo run --bin toyfp dev --sk` to enter the SK combinator -> interaction combinator REPL. Use S or K for the combinators, respectively and parenthesis for application: `((KS)K) => S`. **I recommend trying out this command with the `RUST_LOG=trace` environment variable set to demonstrate everything going on under the hood.** Doing so will display a log of the conversion to interaction combinators, all the steps in reduction, all the steps in compilation, and all the steps in decoding.

Type `cargo test` to run tests. One which is in-progress will fail in `toyfp`.

## Limitations

All of these packages are in progress. `icc` has stabilized, and the runtime is working, featuring parallelism. More optimization needs to be done, but it is demonstrated to be correct via unit tests.

`toyfp` contains multiple compilers, the only semi-complete one being the SK combinator compiler. However, some expressions cannot be decoded properly (partially applied expressions that do not reduce to just S or K), and some do not behave as expected. The extent of incompleteness is not clear.

Extensive refactoring needs to be completed across the entire project, as many components were added ad-hoc, with little regard for structure or cleanliness, in an attempt to iterate rapidly.

## In Progress

I am currently working on a more formal compiler from a high level language to my interaction combinator VM. Specifically, I am working on a compiler in Lean from the BCKW combinators to the interaction combinators. So far, I have prototyped an implementation of the BCKW combinators in the interaction combinator paradigm, pictured in an abbreviated form below. Note that decoder agents are omitted in places whewre they are obvious.

![pic 1](./.github.img/BCKW_-_page_1.png)
![pic 2](./.github.img/BCKW_-_page_2.png)
![pic 3](./.github.img/BCKW_-_page_3.png)

Furthermore, I have many optimizations in the pipeline for my interaction combinator runtime. I hope to finalize my BCKW compiler before this is completed.

Thanks for stopping by! :D
