# Raft W1 campaign log

Lane: `raft-w1` (worktree `.claude/worktrees/raft-w1`), supervised arc
under the standing merge/audit protocol. Charter: master plan
(`docs/2026-08-15_raft-master-plan.md`) §W1.1 — multi-package lowering,
the critical path's head. Owns `Corpus/` + `baselines/` for the lane's
duration. Conventions: derivation-anchored entries, judgement calls
(JC) one-liners, park-quality if budget ends.

## §CROSS-READ — spec-truth campaign integration points (operator, 2026-08-18)

Recorded verbatim-in-substance from the operator cross-read; these
bind raft-lane work but reorder nothing:

1. New latitude/envelope entries for raft's choice sites (W3.1
   election jitter, W5.2 network chaos) MUST use the
   `check-spec-anchors` citation convention — now a gate step.
2. W4 trace-differential triage routes through
   `docs/spec-divergence-ledger.md`'s schema, including the SpecError
   question and `gc-divergence-tolerated`'s usage-vs-implementation
   split.
3. The W1.3 refusal inventory (this arc's tracker probe output)
   should be cross-referenced against
   `docs/spec-archaeology/spec-examples-dispositions.tsv` to rank
   raft-pulled gaps vs language-wide gaps — added as a column to the
   probe inventory where cheap.
4. covmap (`deps/covmap`, `docs/2026-08-17_covmap-pilot.md`) is the
   recorded candidate mechanism for W2's subject↔upstream delta
   tracking (a note for W2, not this lane's scope; §4 of the identity
   design note cites it for the vendoring-delta ledger).

## 2026-08-18 — slice 1: guardrails (committed RED)

- Derivation: master plan §W1.1 + guardrails-first contract. Family
  `Corpus/coverage/exec/multipkg/*`: cross-package function call,
  type+method, consts (untyped/typed/iota), BUG-010 same-name
  identity witnesses (type + func, comma-ok), the panic-form witness,
  diamond import (exactly-once init), cross-package init order (the
  spec's path-sorted schedule vs import-declaration order).
- Every expectation hand-computed, then go-run-confirmed via a
  scratch GOPATH assembly (`artifacts/scratch-multipkg-probe/`):
  25 / 47 / 123 / 20100 / 321 / 1023 / 12313; panic message verbatim
  `interface conversion: interface {} is inner.T, not inner.T (types
  from different packages)`.
- Landed as 8 honest FAILs. Today's verbatim refusal is at stage
  go-run — the ORACLE leg dies first (`cannot find package "..." in
  any of $GOROOT/$GOPATH`), because the harness assembles only the
  main package; the frontend's own single-package refusal
  (`type-check: could not import`) sits behind it and becomes visible
  once the oracle leg learns GOPATH synthesis (slice 3).
- New canonical tag `multipackage` (tags.tsv).
- Full `scripts/ci --diff` re-pin in the same commit: 8 new FAIL rows,
  zero other drift (reason in the baseline header).
- JC: corpus subpackage import paths are CASE-RELATIVE, dot-free,
  import-driven-discovered (nested case dirs stay inert) — argued in
  the identity note §6/§7.
- JC: panic-form witness included KNOWINGLY as a will-stay-red pin of
  the rendering residue (identity note §3.3).

## 2026-08-18 — slice 2: the identity design note

- `docs/2026-08-18_multipackage-identity.md` (design of record):
  path-keyed TypeId/FuncId grammar + injectivity argument; BUG-010
  fix = qualifier `pkg.Path()` at the one boundary constructor;
  `checkPackageNameCollisions` retires in favor of the dotted-path
  grammar guard; rendering residue argued honestly (display-vs-
  identity separation is a GoCore change, out of scope, filed as
  BUG-059 with the pinned witness); raft vendors at SHORT dot-free
  paths (path == name ⇒ exact rendering, oracle-shared tree);
  cross-package init = the spec-pinned Go 1.21+ schedule, one
  concatenated `$pkginit`; fail-closed register (dot imports of
  source packages refuse at the loader; the stdlib dot-import defect
  stays recorded and untouched; shims stay main-package-only).
