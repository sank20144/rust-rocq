# Cargo integration fixtures

These are separate Cargo projects that `check.sh` translates with `cargo rocq`.
Each one has its own manifest and lock file.

`basic` has a local dependency, `cargo_helper`. Cargo builds the dependency, the
main crate is translated, and the call into the dependency appears in the
generated Rocq. The dependency is not translated by default.

`oak_bitmap` contains `oak_restricted_kernel/src/mm/bitmap_frame_allocator.rs`
unchanged from the Oak commit recorded in `UPSTREAM.toml`. `cargo check` does
not enable the file's `#[cfg(test)]` module, so only the allocator code is
translated. `expected.bodies`, `expected.constructs` and `expected.annotations`
hold the expected results. If the translated bodies, the constructors used, the
loan annotation counts or the output size change, `check.sh` fails, and the
expected files have to be reviewed and updated.

Oak builds with Rust nightly 2024-09-05 and x86_64 0.14.11. x86_64 0.14.11 does
not compile with the newer nightly that rust-rocq uses, because of a change to
the unstable `Step` trait, so the fixture uses x86_64 0.14.13 from the same 0.14
release line. The allocator source is not modified, and `check.sh` checks its
SHA-256 checksum before translating it.

The check confirms that every MIR body is translated to well-typed Rocq with no
`TError` or `CError`. The frontend runs Polonius and emits loan starts and loan
ends for each body, including loans that are killed but still needed, which
RefinedRust calls zombie loans.
