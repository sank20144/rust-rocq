# rust-rocq

Translates Rust MIR into Rocq.

## Requirements

- Linux on x86-64. The driver links against rustc's own libraries.
- rustup. The nightly and components in `rust-toolchain.toml` are installed on
  the first build.
- Rocq 9.0 or later on `PATH`. If it is in an opam switch, activate it:

      eval $(opam env --switch=<name> --set-switch)

## Build

    cargo build

## Translate a file

    ./run.sh --rocq-out out/mine path/to/file.rs

Other arguments are passed to rustc, for example `--edition 2024`.

Writes two files into `out/mine`:

- `<crate>.v`, the translation
- `<crate>.mir`, the MIR it was made from

The input must be a crate root the pinned compiler can build on its own.

## Check

    ./check.sh

Translates every input under `tests/inputs` and compiles each result against
`theories/Syntax.v`.
