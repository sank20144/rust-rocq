#!/bin/sh
set -e

cd "$(dirname "$0")"
root=$(pwd)
out=${1:-out}

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

rm -f "$out.err"
exit $fail
