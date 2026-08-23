#!/bin/sh
set -e

cd "$(dirname "$0")"
root=$(pwd)
out=${1:-out}
case "$out" in
    /*) out_root=$out ;;
    *) out_root=$root/$out ;;
esac

cargo build

for built in $(find theories tests -name '*.vo' -o -name '*.glob' -o -name '*.vok' -o -name '*.vos' 2>/dev/null); do
    [ -f "${built%.*}.v" ] || rm -f "$built"
done

if ! command -v rocq >/dev/null 2>&1 && command -v opam >/dev/null 2>&1; then
    eval "$(opam env 2>/dev/null)" || true
fi
if ! command -v rocq >/dev/null 2>&1; then
    echo "rocq not found on PATH." >&2
    echo "Install Rocq 9.0 or later, or activate the switch holding it:" >&2
    echo "    eval \$(opam env --switch=<name> --set-switch)" >&2
    exit 1
fi

rocq makefile -f _RocqProject -o Makefile >/dev/null && make -s

if grep -rn 'Admitted\.\|^[[:space:]]*admit\.' theories tests --include='*.v'; then
    echo "FAIL (admitted proof)" >&2
    exit 1
fi

rm -rf "$out"
fail=0
for input in tests/inputs/*.rs; do
    name=$(basename "$input" .rs)
    printf '%-12s ' "$name"

    if ! "$root/run.sh" --rocq-out "$out/$name" "$input" >/dev/null 2>"$out.err"; then
        echo "FAIL (translation)"
        cat "$out.err"
        fail=1
        continue
    fi

    generated=$(find "$out/$name" -name '*.v' | head -1)
    if [ -z "$generated" ]; then
        echo "FAIL (no output)"
        fail=1
        continue
    fi

    if ! rocq compile -Q theories RustRocq -Q "$out/$name" Generated "$generated" 2>"$out.err"; then
        echo "FAIL (rocq)"
        head -20 "$out.err"
        fail=1
        continue
    fi

    holes=$(grep -c 'TError "\|CError "' "$generated" || true)
    lines=$(wc -c <"$generated")
    mir=$(wc -c <"${generated%.v}.mir")

    if [ -f "tests/$name.v" ]; then
        if rocq compile -Q theories RustRocq -Q "$out/$name" Generated "tests/$name.v" 2>"$out.err"; then
            checks="checked"
        else
            echo "FAIL (tests/$name.v)"; head -20 "$out.err"; fail=1; continue
        fi
    else
        checks="no checks"
    fi

    echo "ok  ${lines} bytes rocq, ${mir} bytes mir, ${holes} unrepresented, ${checks}"
done

check_cargo_fixture() {
    label=$1
    manifest=$2
    crate=$3
    expected_dir=${4:-}
    fixture_out="$out_root/cargo-$label"
    cargo_target="$out_root/cargo-target/$label"

    printf '%-12s ' "$label"
    if ! PATH="$root/target/debug:$PATH" cargo rocq \
        --rocq-out "$fixture_out" -- \
        --manifest-path "$manifest" --target-dir "$cargo_target" \
        >/dev/null 2>"$out.err"; then
        echo "FAIL (cargo translation)"
        cat "$out.err"
        fail=1
        return
    fi

    generated=$(find "$fixture_out" -name "$crate.v" -type f | head -1)
    generated_count=$(find "$fixture_out" -name '*.v' -type f | wc -l)
    if [ -z "$generated" ] || [ "$generated_count" -ne 1 ]; then
        echo "FAIL (expected one primary-crate output, found $generated_count)"
        fail=1
        return
    fi

    if ! rocq compile -Q theories RustRocq -Q "$(dirname "$generated")" Generated \
        "$generated" 2>"$out.err"; then
        echo "FAIL (rocq)"
        head -20 "$out.err"
        fail=1
        return
    fi

    holes=$(grep -c 'TError "\|CError "' "$generated" || true)
    if [ "$holes" -ne 0 ]; then
        echo "FAIL ($holes unrepresented constructs)"
        fail=1
        return
    fi

    constructs=${generated%.v}.constructs
    bodies=${generated%.v}.bodies
    if [ ! -f "$constructs" ] || [ ! -f "$bodies" ]; then
        echo "FAIL (missing coverage summary)"
        fail=1
        return
    fi

    if [ -n "$expected_dir" ]; then
        if ! diff -u "$expected_dir/expected.constructs" "$constructs" >"$out.err"; then
            echo "FAIL (Rocq construct coverage changed)"
            cat "$out.err"
            fail=1
            return
        fi
        if ! diff -u "$expected_dir/expected.bodies" "$bodies" >"$out.err"; then
            echo "FAIL (translated body coverage changed)"
            cat "$out.err"
            fail=1
            return
        fi
    fi

    annotation_report=
    if [ -n "$expected_dir" ] && [ -f "$expected_dir/expected.annotations" ]; then
        expected_starts=$(sed -n 's/^loan_starts=//p' "$expected_dir/expected.annotations")
        expected_ends=$(sed -n 's/^loan_ends=//p' "$expected_dir/expected.annotations")
        max_rocq_lines=$(sed -n 's/^max_rocq_lines=//p' "$expected_dir/expected.annotations")
        actual_starts=$(grep -o 'LoanStart' "$generated" | wc -l)
        actual_ends=$(grep -o 'LoanEnd' "$generated" | wc -l)
        rocq_lines=$(wc -l <"$generated")
        if [ "$actual_starts" -ne "$expected_starts" ] || \
           [ "$actual_ends" -ne "$expected_ends" ]; then
            echo "FAIL (borrowck annotations changed: $actual_starts starts, $actual_ends ends)"
            fail=1
            return
        fi
        if [ "$rocq_lines" -gt "$max_rocq_lines" ]; then
            echo "FAIL (Rocq output grew to $rocq_lines lines; limit is $max_rocq_lines)"
            fail=1
            return
        fi
        if grep -q 'Facts\|subset_base\|path_accessed_at_base' "$generated"; then
            echo "FAIL (raw Polonius relations leaked into normal Rocq output)"
            fail=1
            return
        fi
        annotation_report=", $actual_starts loan starts, $actual_ends loan ends, $rocq_lines lines"
    fi

    construct_count=$(wc -l <"$constructs")
    body_count=$(wc -l <"$bodies")
    echo "ok  $body_count bodies, $construct_count rocq constructors, $holes unrepresented$annotation_report"
}

check_cargo_fixture \
    basic \
    tests/cargo/basic/Cargo.toml \
    cargo_input

if ! grep -q '"cargo_helper::increment"' \
    "$out_root"/cargo-basic/cargo_input/*/cargo_input.v; then
    echo "cargo-basic  FAIL (dependency call missing from primary translation)"
    fail=1
fi
if find "$out_root/cargo-basic" -name 'cargo_helper.v' -type f | grep -q .; then
    echo "cargo-basic  FAIL (dependency translated in workspace-only mode)"
    fail=1
fi

oak_dir=tests/cargo/oak_bitmap
oak_source=$oak_dir/upstream/bitmap_frame_allocator.rs
oak_expected_hash=$(sed -n 's/^sha256 = "\([0-9a-f]*\)"/\1/p' "$oak_dir/UPSTREAM.toml")
oak_actual_hash=$(sha256sum "$oak_source" | awk '{print $1}')
if [ "$oak_actual_hash" != "$oak_expected_hash" ]; then
    echo "oak-bitmap   FAIL (upstream source checksum changed)"
    fail=1
else
    check_cargo_fixture \
        oak-bitmap \
        "$oak_dir/Cargo.toml" \
        oak_bitmap_allocator \
        "$oak_dir"
fi

rm -f "$out.err"
exit $fail
