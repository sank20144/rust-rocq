# rust-rocq

Translates Rust MIR into Rocq.

## Requirements

- The nightly pinned in `rust-toolchain.toml`, with the `rustc-dev` component.
  rustup installs it on first build.
- Rocq 9.0 or later on `PATH`.

## Build

    cargo build

## Translate a file

    ./run.sh --rocq-out out/mine path/to/file.rs

Writes two files into `out/mine`:

- `<crate>.v`, the translation
- `<crate>.mir`, the MIR it was made from

The input must be a crate root the pinned compiler can build on its own.

## Check

    ./check.sh

Translates every input under `tests/inputs` and compiles each result against
`theories/Syntax.v`.
