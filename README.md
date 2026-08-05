# rust-rocq

Translates Rust MIR into Rocq for foundational verification.

The frontend is a rustc driver that reads the borrow-checked MIR body
(`MirPhase::Analysis(Initial)`) and emits Rocq terms of a deeply embedded MIR
syntax. Region and loan facts from Polonius are attached to each body.

`theories/Syntax.v` contains only the syntax and does not depend on Iris.

## Why the analysis body

Polonius facts refer to locations in borrow-checked MIR. Translating a later
phase would mean mapping those locations back, which takes RefinedRust about
3,000 lines and still leaves some locations unmapped. Translating the
borrow-checked body avoids that mapping.

At this phase `Drop` is conditional, so the semantics has to track which places
are initialised instead of reading drop flags from the control-flow graph. In
return, rustc's drop elaboration is not part of the trusted base.

## Layout

    src/          rustc driver and the MIR to Rocq translation
    theories/     the Rocq syntax layer and generic instantiation
    tests/        Rust inputs, and Rocq checks over the translation of them

`./check.sh` translates every input under `tests/inputs` and checks the Rocq it
produces type-checks.

## Building

Needs the pinned nightly with `rustc-dev`, see `rust-toolchain.toml`.

    cargo build --release

The Rocq side needs Rocq 9.0 or later.
