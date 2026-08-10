#!/usr/bin/env bash
# Rocq oracle leg: extract verdi-raft's handlers at the N=3 counter
# instantiation, build the OCaml replay driver, and run it over the
# committed fixture. Lane-local runner (merge-window queue item 5:
# lives under compat/verdi/extraction, not scripts/ — the latter is
# mainline-owned). Fail closed at every step.
#
# Toolchain (lane log, parking-ledger resolution 2026-08-10):
#   - Coq 8.18.0 in the repo-local opam switch deps/opam-coq818/_opam
#   - deps/verdi-raft theories built quick-mode (.vos) at the pinned rev
# Override with:
#   GOLEAN_COQ_BIN            bin dir containing coqc/ocamlc
#   GOLEAN_VERDI_RAFT_THEORIES  built verdi-raft theories dir
set -euo pipefail
cd "$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd ../../.. && pwd)"

COQBIN="${GOLEAN_COQ_BIN:-$REPO_ROOT/deps/opam-coq818/_opam/bin}"
VR="${GOLEAN_VERDI_RAFT_THEORIES:-$REPO_ROOT/deps/verdi-raft/theories}"
FIXTURE="${1:-../fixtures/handlers-n3.tsv}"

fail() { echo "oracle-build: FAIL: $*" >&2; exit 1; }

[ -x "$COQBIN/coqc" ] || fail "no coqc at $COQBIN — install the repo-local switch (lane log toolchain record) or set GOLEAN_COQ_BIN"
[ -x "$COQBIN/ocamlc" ] || fail "no ocamlc at $COQBIN"
[ -f "$VR/Raft/Raft.vos" ] || fail "no built Raft.vos under $VR — build verdi-raft ('scripts/capped make quick' at the pin) or set GOLEAN_VERDI_RAFT_THEORIES to a built copy"
[ -f "$FIXTURE" ] || fail "no fixture at $FIXTURE — a run that checks nothing must not pass"

export PATH="$COQBIN:$PATH"

# -vok: load .vos for dependencies (the theories are quick-built) and
# fully process this file, which executes the Extraction command.
# (-vos alone skips it: side effects are deferred in .vos compilation.)
coqc -vok -Q "$VR" VerdiRaft ExtractRaftHandlers.v \
  || fail "coqc on ExtractRaftHandlers.v failed"
[ -f RaftHandlers.ml ] || fail "extraction produced no RaftHandlers.ml"

ocamlc RaftHandlers.mli RaftHandlers.ml driver.ml -o oracle-driver \
  || fail "ocamlc build of the driver failed"

EXPECTED=$(grep -cv '^#' "$FIXTURE")
./oracle-driver "$FIXTURE" | tee last-run.log
JUDGED=$(sed -n 's/^oracle: \([0-9]*\) cases:.*/\1/p' last-run.log)
[ "$JUDGED" = "$EXPECTED" ] \
  || fail "judged $JUDGED cases but the fixture has $EXPECTED rows — refusing a partial run"
echo "oracle-build: OK ($JUDGED cases judged)"
