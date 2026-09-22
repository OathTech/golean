#!/usr/bin/env bash
# gc.sh <pkg-dir> <out.txt> <runs> <subject>... — gc 1.26.5 draws: driver per subject, default and -N -l builds,
# <runs> runs x GOMAXPROCS 1/8 each; the exit status appended on a panic. (After the lane's .tmp/e5/gc-draws.sh.)
set -uo pipefail
PKG="$1"; OUT="$2"; RUNS="$3"; shift 3
ROOT=/home/dev/projects/golean/.claude/worktrees/audit-unseq-stage-e5
export GO111MODULE=off GOCACHE="$ROOT/.tmp/gocache"
for subj in "$@"; do
  d="$ROOT/.tmp/gc/$(echo "$PKG" | tr '/' '_')_$subj"; rm -rf "$d"; mkdir -p "$d/bin"
  cp "$PKG"/*.go "$d/" 2>/dev/null || cp "$ROOT/$PKG"/*.go "$d/"
  if grep -q "^func main()" "$d"/*.go; then sed -i 's/^func main()/func mainOrig()/' "$d"/*.go; fi
  printf 'package main\n\nfunc main() { println(%s()) }\n' "$subj" > "$d/driver.go"
  (cd "$d" && go build -o bin/default . && go build -gcflags=all='-N -l' -o bin/nl .) 2>"$d/build.err" || { echo "$PKG:$subj BUILD FAILED: $(head -c 300 "$d/build.err" | tr '\n' ' ')" >> "$OUT"; continue; }
  for procs in 1 8; do for flags in default nl; do for run in $(seq 1 "$RUNS"); do
    label="default"; [[ $flags == nl ]] && label="-N -l"
    out="$(GOMAXPROCS=$procs "$d/bin/$flags" 2>&1)"; rc=$?
    line="$(printf '%s' "$out" | grep -v -e '^goroutine ' -e '^main\.' -e $'^\t' -e '^exit status' -e '^$' | tr '\n' '|')"; [[ $rc -ne 0 ]] && line="$line [exit $rc]"
    echo "$(basename "$PKG"):$subj GOMAXPROCS=$procs $label run$run: $line" >> "$OUT"
  done; done; done
done
