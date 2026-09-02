#!/usr/bin/env bash
# repro.sh — producer of every *.log in docs/evidence/2026-09-02_diffcov-argmax/
# (the scripts/diff-coverage ARG_MAX fan-out defect: red-first record, then
# the post-fix refusal). Run from the repo root, under the memory cap:
#
#   scripts/capped docs/evidence/2026-09-02_diffcov-argmax/repro.sh [mechanism|prefix|postfix|all]
#
# Needs: the built golean binary (scripts/capped lake build) and go on PATH
# at the oracle pin (baselines/go-oracle-pin) — the runner refuses otherwise,
# and a run that dies at those checks would NOT be a reproduction (exit 2
# there is indistinguishable from the exit 2 under test; every stage below
# asserts the specific stderr text, not just the exit code).
# Scratch: artifacts/argmax-scratch (gitignored). The PRE-fix runner is
# materialised from git at scripts/.diff-coverage-prefix (its ROOT derives
# from its own location, so it must live in scripts/) and removed afterwards.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
cd "$ROOT"
HERE="docs/evidence/2026-09-02_diffcov-argmax"
PREFIX_SHA=e7d07b26            # main at the fix's branch point (pre-fix runner)
N=19999                        # the grossmith campaign's row count
JOBS=8
S="$ROOT/artifacts/argmax-scratch"
mkdir -p "$S"
# The campaign's TMPDIR was 130 bytes long; the cliff is a function of this
# length, so we pad a scratch dir to exactly 130 (or report if ROOT alone is
# longer).
PAD="$S/t"
while [ "${#PAD}" -lt 130 ]; do PAD="${PAD}a"; done
mkdir -p "$PAD"

relativize() { sed -i "s|$ROOT/||g" "$1"; }   # evidence convention: repo-relative paths only

hdr() { # $1 = log basename
  printf '# %s — produced by %s/repro.sh %s\n# host: %s; ARG_MAX=%s; %s; commit %s%s\n# TMPDIR used for the runner: %s bytes\n\n' \
    "$1" "$HERE" "$STAGE" "$(uname -sm)" "$(getconf ARG_MAX)" "$(go version)" \
    "$(git rev-parse --short HEAD)" "$([ -z "$(git status --porcelain -- scripts Corpus GoLean 2>/dev/null)" ] || printf ' (dirty tree: %s)' "$(git status --porcelain -- scripts Corpus GoLean | tr '\n' ' ')")" "${#PAD}"
}

# One manifest row per case. ELEVEN fields: the 11th makes every row a
# real, fast, per-row manifest-stage FAIL ("too many tab-separated
# fields" — run_case_rows' first check, no go/lean shell-out), so the
# post-fix runner can drive 19,999 real workers through the fan-out in
# ~a minute. The subject under test is the FAN-OUT, not the
# classification; the pre-fix runner never reads a row at all.
make_manifest() {
  local dir="Corpus/coverage/exec/maps/range-first-key" i
  : > "$S/manifest-argmax.tsv"
  for ((i = 1; i <= N; i++)); do
    printf 'argmax-%06d\t%s\trangeFirstKey\t-\tok\tmaps,range,keys,loops,nondet\t-\tmembership\twhy\twidth=16\tEXTRA\n' "$i" "$dir"
  done >> "$S/manifest-argmax.tsv"
}

stage_mechanism() {
  STAGE=mechanism
  local log="$HERE/mechanism.log" R="$PAD/golean-coverage-rows.MECHXX" i k lo hi mid
  hdr mechanism.log > "$log"
  {
    rm -rf "$R"; mkdir -p "$R"
    for ((i = 1; i <= N; i++)); do : > "$R/$(printf '%06d' "$i").in"; done
    echo "fake ROWDIR: $R"
    echo "per-file path length: $(( ${#R} + 1 + 9 )) bytes; files: $(find "$R" -name '*.in' | wc -l)"
    echo "argv estimate: N * (path + NUL + 8-byte pointer) = $(( N * (${#R} + 10 + 1 + 8) )) bytes vs ARG_MAX $(getconf ARG_MAX)"
    echo
    echo "--- (1) the old enumerator, bash: ls \"\$ROWDIR\"/*.in | wc -l"
    ls "$R"/*.in | wc -l
    echo "--- (2) the old fan-out shape: ls ... | xargs -P 4 -n 1 sh -c 'echo INVOKED arg=<\$1>' _"
    ls "$R"/*.in | xargs -P 4 -n 1 sh -c 'echo "INVOKED arg=<$1>"' _
    echo "pipeline statuses (ls xargs): ${PIPESTATUS[*]}"
    echo "--- (3) same with xargs -r: invocations ="
    ls "$R"/*.in | xargs -r -P 4 -n 1 sh -c 'echo "INVOKED arg=<$1>"' _ | wc -l
    echo "--- (4) the new fan-out shape: find -print0 | xargs -0 -r -P 4 -n 1 … invocations ="
    find "$R" -maxdepth 1 -name '*.in' -print0 | xargs -0 -r -P 4 -n 1 sh -c 'echo "$1"' _ | wc -l
    echo
    echo "--- (5) measured cliff at this path length (bisection on the largest k for which 'ls <k paths>' execs):"
    lo=1000; hi=40000
    for ((i = hi; i > N; i--)); do : > "$R/$(printf '%06d' "$i").in"; done
    while (( hi - lo > 1 )); do
      mid=$(( (lo + hi) / 2 ))
      if ls $(seq -f "$R/%06g.in" 1 "$mid") >/dev/null 2>&1; then lo=$mid; else hi=$mid; fi
    done
    echo "path length $(( ${#R} + 10 )) bytes: ls succeeds at k=$lo, fails (E2BIG) at k=$hi"
    echo "predicted from ARG_MAX/(path+1+8) = $(( $(getconf ARG_MAX) / (${#R} + 10 + 1 + 8) )) (environment bytes also count against ARG_MAX)"
    rm -rf "$R"
  } >> "$log" 2>&1
  relativize "$log"; echo "wrote $log"
}

stage_prefix() {
  STAGE=prefix
  local log="$HERE/prefix.log" art="$S/art-prefix" rc
  make_manifest
  git show "$PREFIX_SHA:scripts/diff-coverage" > scripts/.diff-coverage-prefix
  chmod +x scripts/.diff-coverage-prefix
  rm -rf "$art" .out
  hdr prefix.log > "$log"
  {
    echo "runner: scripts/diff-coverage as of $PREFIX_SHA (git show, materialised at scripts/.diff-coverage-prefix)"
    echo "manifest: $N rows; TMPDIR=$PAD (${#PAD} bytes); GOLEAN_COVERAGE_JOBS=$JOBS"
    echo
    TMPDIR="$PAD" GOLEAN_COVERAGE_JOBS="$JOBS" GOLEAN_COVERAGE_ARTIFACTS="$art" \
      scripts/.diff-coverage-prefix "$S/manifest-argmax.tsv" > "$S/prefix.stdout" 2> "$S/prefix.stderr"
    rc=$?
    echo "exit code: $rc   (1 = 'FAIL rows exist, published results ARE authoritative')"
    echo "--- stderr:"; sed 's/^/  /' "$S/prefix.stderr"
    echo "--- stdout (first 12 lines):"; head -12 "$S/prefix.stdout" | sed 's/^/  /'
    echo "--- (i) stray file in the repo root (run_case \"\" → CASE_OUT=.out.tmp → mv .out):"
    ls -la .out 2>&1 | sed 's/^/  /'; echo "  content: $(cat .out 2>/dev/null | cat -A)"
    echo "--- (iii) published results at $art:"
    ls "$art" | sed 's/^/  /'
    echo "  rows total (excl. header): $(( $(wc -l < "$art/latest.tsv") - 1 ))"
    echo "  rows 'worker produced no result': $(grep -c $'\tworker produced no result$' "$art/latest.tsv")"
    echo "  first 3 + last row:"; sed -n '2,4p' "$art/latest.tsv" | sed 's/^/    /'; tail -1 "$art/latest.tsv" | sed 's/^/    /'
    echo "  meta:"; sed 's/^/    /' "$art/latest.meta.tsv"
  } >> "$log" 2>&1
  rm -f .out scripts/.diff-coverage-prefix
  relativize "$log"; echo "wrote $log"
}

stage_postfix() {
  STAGE=postfix
  local log="$HERE/postfix-scale.log" art="$S/art-postfix" rc
  make_manifest
  rm -rf "$art" .out
  hdr postfix-scale.log > "$log"
  {
    echo "runner: scripts/diff-coverage (working tree); same $N-row manifest, TMPDIR=$PAD (${#PAD} bytes), GOLEAN_COVERAGE_JOBS=$JOBS"
    echo
    TMPDIR="$PAD" GOLEAN_COVERAGE_JOBS="$JOBS" GOLEAN_COVERAGE_ARTIFACTS="$art" \
      scripts/diff-coverage "$S/manifest-argmax.tsv" > "$S/postfix.stdout" 2> "$S/postfix.stderr"
    rc=$?
    echo "exit code: $rc   (1 expected: every row is a REAL per-row manifest-stage FAIL by construction)"
    echo "--- stderr:"; sed 's/^/  /' "$S/postfix.stderr"
    echo "--- stray .out in repo root:"; ls -la .out 2>&1 | sed 's/^/  /'
    echo "--- published results at $art:"
    echo "  rows total (excl. header): $(( $(wc -l < "$art/latest.tsv") - 1 ))"
    echo "  rows 'worker produced no result': $(grep -c $'\tworker produced no result$' "$art/latest.tsv")"
    echo "  rows 'too many tab-separated fields' (the constructed per-row fail): $(grep -c 'too many tab-separated fields' "$art/latest.tsv")"
    echo "  distinct ids: $(cut -f2 "$art/latest.tsv" | sed 1d | sort -u | wc -l)"
    echo "  first 2 + last row:"; sed -n '2,3p' "$art/latest.tsv" | sed 's/^/    /'; tail -1 "$art/latest.tsv" | sed 's/^/    /'
    echo "  meta fan-out keys:"; grep '^fanout_\|^jobs' "$art/latest.meta.tsv" | sed 's/^/    /'
  } >> "$log" 2>&1
  relativize "$log"; echo "wrote $log"

  # The empty-pool path (sub-defect i + iii together): a fake xargs that
  # behaves like GNU xargs WITHOUT -r on empty stdin — drains stdin, runs
  # the command once with no argument — regardless of how the rows are
  # enumerated. This is the shape scripts/test-lane-validation G5 pins.
  log="$HERE/postfix-emptypool.log"; art="$S/art-emptypool"
  local fb="$S/fakebin-xargs-no-r"
  mkdir -p "$fb"
  cat > "$fb/xargs" <<'EOF'
#!/bin/bash
# bash, not sh: dash drops BASH_FUNC_* exported functions on exec.
cat >/dev/null
while [ $# -gt 0 ]; do
  case "$1" in
    -0|-r) shift ;;
    -P|-n) shift 2 ;;
    *) break ;;
  esac
done
exec "$@"
EOF
  chmod +x "$fb/xargs"
  printf 'g5-a\tCorpus/coverage/exec/maps/range-first-key\trangeFirstKey\t-\tok\tmaps,range,keys,loops,nondet\t-\tmembership\twhy\twidth=16\ng5-b\tCorpus/coverage/exec/maps/range-first-key\trangeFirstKey\t-\tok\tmaps,range,keys,loops,nondet\t-\tmembership\twhy\twidth=16\n' > "$S/manifest-emptypool.tsv"
  rm -rf "$art" .out
  mkdir -p "$art"; printf 'stale\n' > "$art/latest.tsv"; printf 'stale\n' > "$art/latest.meta.tsv"
  hdr postfix-emptypool.log > "$log"
  {
    echo "runner: scripts/diff-coverage (working tree); 2 valid rows; PATH-shadowed xargs = 'GNU xargs without -r on empty stdin' (run the command once, no argument); stale results pre-seeded"
    echo
    PATH="$fb:$PATH" GOLEAN_COVERAGE_JOBS=2 GOLEAN_COVERAGE_ARTIFACTS="$art" \
      scripts/diff-coverage "$S/manifest-emptypool.tsv" > "$S/emptypool.stdout" 2> "$S/emptypool.stderr"
    rc=$?
    echo "exit code: $rc   (2 expected: infrastructure, nothing published)"
    echo "--- stderr:"; sed 's/^/  /' "$S/emptypool.stderr"
    echo "--- stray .out in repo root:"; ls -la .out 2>&1 | sed 's/^/  /'
    echo "--- artifacts dir after the run (stale pair must be GONE):"; ls -la "$art" | sed 's/^/  /'
  } >> "$log" 2>&1
  relativize "$log"; echo "wrote $log"
}

case "${1:-all}" in
  mechanism) stage_mechanism ;;
  prefix) stage_prefix ;;
  postfix) stage_postfix ;;
  all) stage_mechanism; stage_prefix; stage_postfix ;;
  *) echo "usage: $0 [mechanism|prefix|postfix|all]" >&2; exit 2 ;;
esac
