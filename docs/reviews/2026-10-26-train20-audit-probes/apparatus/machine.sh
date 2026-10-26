#!/usr/bin/env bash
# machine.sh — after modprobes.sh: the machine's answer for probe() on the wires the frontend
# wrote where gc's answer was moved by something the frontend never read (gc printed `true`;
# the Go 1.26 module default answers `false`). Needs the built golean (.lake/build/bin/golean).
set -u
ROOT="$(cd "$(dirname "$0")" && git rev-parse --show-toplevel)"
G="${GOLEAN_BIN:-$ROOT/.lake/build/bin/golean}"; P="$ROOT/.tmp/probes/cases"
[[ -x "$G" ]] || { echo "machine: no golean at $G" >&2; exit 2; }
for c in w01-control w13-goenv-path w27-modfile-flag w28-goenv-modfile w15-gopath; do
  w="$P/$c/wire.json"
  if [[ ! -f "$w" ]]; then printf '%s\tno wire (the frontend refused)\n' "$c"; continue; fi
  printf '%s\t%s\n' "$c" "$("$G" native-json-run --input "$w" --function probe 2>/dev/null | python3 -c 'import json,sys; o=json.load(sys.stdin); print("status:", o.get("status"), "values:", o.get("values"))')"
done
