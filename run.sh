#!/bin/sh
set -e
SYSROOT=$(rustc --print sysroot)
export SYSROOT
export LD_LIBRARY_PATH="$SYSROOT/lib:$LD_LIBRARY_PATH"
exec "$(dirname "$0")/target/debug/rust-rocq" --crate-type=lib --edition 2021 "$@"
