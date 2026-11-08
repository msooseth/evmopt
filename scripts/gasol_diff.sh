#!/usr/bin/env bash
# Run gasol on each block (one per line) of $1 and validate its output with evmopt check.
# Usage: GASOL_PY=<python with networkx+pandas> scripts/gasol_diff.sh blocks.txt [extra gasol flags]
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
PY=${GASOL_PY:-python3}
BLOCKS=$(realpath "$1"); shift
export ROOT PY GASOL_FLAGS="$*"
one() {
  d=$(mktemp -d); trap 'rm -rf "$d"' RETURN
  printf '%s\n' "$1" > "$d/b.txt"
  out=$(cd "$d" && timeout 120 "$PY" -W ignore "$ROOT/gasol-optimizer/gasol_asm.py" b.txt -bl $GASOL_FLAGS 2>&1) || true
  opt=$(printf '%s\n' "$out" | awk '/^Optimized sequence/{getline; print; exit}')
  {
    echo "### $1"
    echo "gasol: ${opt:-<no output>}"
    if [ -n "$opt" ]; then
      "$ROOT/.lake/build/bin/evmopt" --fork "${EVMOPT_FORK:-cancun}" check "$1" "$opt" 2>&1 | cut -c1-200 || true
    else
      printf '%s\n' "$out" | grep -E "Error|Exception|Traceback" | tail -2 | cut -c1-200
    fi
  } > "$d/report"
  cat "$d/report"
}
export -f one
grep -v '^[[:space:]]*$' "$BLOCKS" | tr '\n' '\0' |
  xargs -0 -P "$(getconf _NPROCESSORS_ONLN)" -I{} bash -c 'one "$@"' _ {}
