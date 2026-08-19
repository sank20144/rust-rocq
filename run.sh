#!/bin/sh
set -e
here=$(dirname "$0")

if [ ! -x "$here/target/debug/rust-rocq" ]; then
    echo "rust-rocq is not built. Run: cargo build" >&2
    exit 1
fi

SYSROOT=$(rustc --print sysroot)
export SYSROOT
export LD_LIBRARY_PATH="$SYSROOT/lib:$LD_LIBRARY_PATH"

defaults=""
case " $* " in *" --crate-type"*) ;; *) defaults="--crate-type=lib" ;; esac
case " $* " in *--edition*) ;; *) defaults="$defaults --edition=2021" ;; esac

exec "$here/target/debug/rust-rocq" $defaults "$@"
