#!/bin/sh
set -e

cd "$(dirname "$0")"
root=$(pwd)
out=${1:-out}

cargo build

if [ -z "$ROCQBIN" ] && command -v opam >/dev/null 2>&1; then
    eval "$(opam env --switch=proofs --set-switch 2>/dev/null)" || true
fi
(cd theories && rocq makefile -f _RocqProject -o Makefile >/dev/null && make -s)

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
    echo "ok  ${lines} bytes rocq, ${mir} bytes mir, ${holes} unrepresented"
done

check_against() {
    printf '%-12s ' "$1"
    if rocq compile -Q theories RustRocq -Q "$out/$2" Generated "$3" 2>"$out.err"; then
        echo "ok"
    else
        echo "FAIL"
        head -20 "$out.err"
        fail=1
    fi
}

check_against instantiate coverage tests/instantiation.v
check_against evaluate arith tests/semantics.v

rm -f "$out.err"
exit $fail
