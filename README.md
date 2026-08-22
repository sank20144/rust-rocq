# rust-rocq

Translates Rust MIR into Rocq.

The frontend is a rustc driver that reads the borrow-checked MIR body and emits
Rocq terms of the syntax in `theories/Syntax.v`. It also runs Polonius and turns
its output into loan start and loan end annotations for each body.

## Requirements

It runs on Linux on x86-64. The driver links against rustc's own libraries, so
it only works with one compiler build on one platform.

You need rustup and Rocq 9.0 or later.

## Setup

### Rust

    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

The nightly toolchain and components are pinned in `rust-toolchain.toml`, and
rustup downloads them on the first build. The download is a few hundred
megabytes because `rustc-dev` includes the compiler's libraries.

### Rocq

Any Rocq 9.0 or later on `PATH` works. Only the Rocq standard library is used.

To install it with opam:

    bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"
    opam init

    opam switch create rocq-9 ocaml-base-compiler.4.14.2
    eval $(opam env --switch=rocq-9 --set-switch)
    opam install rocq-core rocq-stdlib

Both packages are in the default opam repository.

The `eval` line puts `rocq` on `PATH` for the current shell and has to be run
again in each new shell. If `rocq` is not on `PATH`, `check.sh` looks for it in
each opam switch until it finds one that has it.

## Build

    cargo build

## Translate a file

    ./run.sh --rocq-out out/mine path/to/file.rs

Writes two files into `out/mine`:

- `<crate>.v`, the translation
- `<crate>.mir`, the MIR it was made from

The input must be a crate root the pinned compiler can build on its own, so a
standalone `.rs` file works but a Cargo project's dependencies are not resolved.

Other arguments are passed to rustc, for example `--edition 2024`. The defaults
are `--crate-type=lib --edition=2021`.

## Translate a Cargo project

Build both frontend executables, put them on Cargo's command search path, and
run the `rocq` Cargo subcommand in the project to translate:

    cargo build --bins
    PATH="$PWD/target/debug:$PATH" cargo rocq --rocq-out out/my-project -- \
        --manifest-path path/to/Cargo.toml

`cargo rocq` runs `cargo check` with `rust-rocq` as the Rust compiler. Cargo
reads the project's own `Cargo.toml` and `Cargo.lock`, builds its dependencies,
runs build scripts, and passes the frontend the edition, features, target and
`--extern` arguments.

Only Cargo's primary packages are translated by default; dependencies are
compiled normally. Pass `--include-deps` before `--` to translate dependency
crates too. Options after `--` are passed to `cargo check`.

Each translated crate produces four files:

- `<crate>.v`, the Rocq translation
- `<crate>.mir`, the borrow-checked MIR that was translated
- `<crate>.bodies`, the exact set of translated body names
- `<crate>.constructs`, the exact set of Rocq constructors used

Output goes to a separate directory for each crate and Cargo metadata hash, so
compiler runs with different configurations do not overwrite each other.

## Check

    ./check.sh

Translates every input under `tests/inputs` and compiles each result against
`theories/Syntax.v`. It also translates the Cargo projects under `tests/cargo`.
It reports how many constructs could not be translated, which should be zero.
