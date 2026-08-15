# rust-rocq

Translates Rust MIR into Rocq for foundational verification.

The frontend is a rustc driver that reads the borrow-checked MIR body
(`MirPhase::Analysis(Initial)`) and emits Rocq terms of a deeply embedded MIR
syntax. Region and loan facts from Polonius are attached to each body.

`theories/Syntax.v` contains only the syntax and does not depend on Iris.

`theories/Denote.v` gives the syntax a denotational semantics over the
byte-level memory model in `theories/Memory.v`, so a translated body can be run.
A construct with no meaning evaluates to `Unmodelled`.

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
    theories/     the Rocq syntax, memory model, instantiation and semantics
    tests/        Rust inputs, and Rocq checks over the translation of them

`./check.sh` translates every input under `tests/inputs` and checks the Rocq it
produces type-checks.

Each translation writes two files, `<crate>.v` and `<crate>.mir`. The `.mir`
file is the body the `.v` file was made from, printed by rustc. It differs from
`-Zdump-mir` output: the borrow checker gives the driver a copy of the body with
renumbered regions, and the `.mir` file uses those numbers, so a reference
printed as `&'?4 u32` there is `TRef (RVar 4)` in the `.v` file. The driver
turns on verbose printing so the region numbers are shown.

`docs/constructs.md` lists every MIR construct, whether the semantics gives it a
meaning, and what that meaning is.

## Building

Needs the pinned nightly with `rustc-dev`, see `rust-toolchain.toml`.

    cargo build --release

The Rocq side needs Rocq 9.0 or later.
