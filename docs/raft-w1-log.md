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

## 2026-08-18 — slice 4: the tracker smoke probe (W1.3 discovery instrument)

Measurement, NOT a milestone claim (arc brief step 5). Two probe tiers
under `artifacts/probe-tracker-{verbatim,shimpb}/` (gitignored probe
artifacts; every deviation from upstream is `[probe delta: ...]`-marked
in the copies). Base: `deps/raft` @ 56e3200, packages tracker + quorum
(+ raftpb), imports rewritten `go.etcd.io/raft/v3/X` → `X` (the §4
canonical short-path form).

**Tier 1 — verbatim vendor.** Refuses at raftpb's protobuf runtime,
verbatim: `type-check: .../raftpb/confchange.go:22:2: could not import
google.golang.org/protobuf/proto (can't find import: ...)`. NOTE FOR
THE §8.6 RULING: at the pinned rev the runtime is
google.golang.org/protobuf (raft has already migrated off gogo) — the
scoping doc's "gogo-rev pin" option means pinning BACKWARD.

**Tier 2 — struct-only raftpb stand-in** (ConfState only — the sole
raftpb type tracker's non-test code touches; labeled probe artifact,
NOT a plainpb proposal). Refusal inventory, in discovery order, each a
W1.3 sweep item (cross-ref column per the §CROSS-READ item 3 against
`docs/spec-archaeology/spec-examples-dispositions.tsv`):

| # | Refusal (verbatim)                                    | Site                                   | Class | Cross-ref |
|---|-------------------------------------------------------|----------------------------------------|-------|-----------|
| 1 | `selector call Fprintf is not a method value`         | quorum majority.go String/Describe, tracker Config.String, Progress(.Map).String | rendering (quorum-pilot omission precedent; no-op-Logger/quarantine lane) | timezone-stringer row: fmt blocks are recorded honest-red class |
| 2 | `c[0].String undefined` after omission                | quorum joint.go JointConfig.String/Describe | cascade of 1 | — |
| 3 | `selector call FormatUint is not a method value`      | quorum quorum.go Index.String          | rendering | — |
| 4 | `selector call FormatInt is not a method value`       | quorum voteresult_string.go (generated stringer) | rendering | — |
| 5 | `builtin copy in statement position`                  | tracker inflights.go:93 `copy(newBuffer, in.buffer)` (Inflights.grow) | LANGUAGE GAP: copy's result may be discarded; frontend admits only expression position | spec-examples-decl/copy-forms covers the expression form language-wide — this is the statement-position residue |
| 6 | `selector call Sprintf is not a method value`         | tracker progress.go:181 `panic(fmt.Sprintf(...))` (SentEntries) | SEMANTIC-PATH fmt: one of the scoping doc's measured non-logger Sprintf sites; needs the W1.2+ fmt story (shim / hand-rolled), not quarantine | timezone-stringer row (same class) |

Post-inventory state: the FULL tracker+quorum tree (6 funcs, 39
methods, 15 TypeDefs) exports clean, and the machine RUNS it:
`probeTracker` (Progress literal + fields) → 7; `probeCommitted` —
the REAL `quorum.MajorityConfig.CommittedIndex` over a main-package
`AckedIndexer` implementation (cross-package interface satisfaction +
the slices.Sort extern) → 5 on {8,5,3}, correct median. Also
observed en passant: `new(p.AutoLeave)` (Go 1.26 new-with-value, in
ConfState()) EMITS cleanly — language-wide corpus coverage exists
(bools/short-circuit-funclit/admit-new*), but the tracker path is
unexercised until W4 promotes cases.

JC: probe iteration stopped at export-clean + two run probes — deeper
exercise (ProgressTracker maps, Visit's sortkeys) is W4 stage-2's job
with real differential cases, not a probe's.

## 2026-08-18 — slice 3: the implementation lands (guardrails FLIP)

- Derivation: identity note §1/§5–§7, implemented exactly.
  - Frontend loader (`tools/nativefrontend/load.go`): import-driven
    local-package discovery, chained importer (locals then stdlib),
    per-package `types.Info`, spec-order unit list (path-sorted
    ready-first; main last). Fail-closed: dot imports of source
    packages, dotted local paths, stdlib shadowing, `main` qualifier
    collision, cycles.
  - Identity boundary (`tools/nativefrontend/identity.go`):
    `pkgQualifier` = import path; `funcWireName` / `globalWireName` /
    `initFuncWireName`; `checkKeyPathGrammar` (dotted-path refusal)
    replaces `checkPackageNameCollisions` — BUG-010 CLOSED.
  - Emitter: per-unit decl/global emission in init order; one
    concatenated `$pkginit`; qualified call/selector/store/&-alias
    arms (`emitQualifiedCall`/`emitQualifiedSelector` + lvalue +
    addressOf); mono stencils carry their declaring unit; D5 markers
    now stdlib-only.
  - Oracle leg: `coverageharness` copies imported local packages to
    `<out>/gopath/src/<path>`; `diff-coverage` hands the tree to Go's
    own resolution (`GOPATH=`, absolute).
  - `check-coverage` husk gate: imported-package subdirs exempt by the
    pipeline's own discovery rule (unimported go-file dirs still husk).
- Flip: 7 guardrails + `interfaces/imported-package-name-collision`
  (BUG-010's pin) go GREEN; new same-slice guardrail
  `multipkg/cross-var` (qualified store/compound/&-alias, sequenced
  reads) green; `multipkg/same-name-identity-panic` moves to its TRUE
  stage (FAIL/differential — identity verdict right, message qualifier
  path-vs-name), filed as BUG-059. Golden pins byte-identical
  (`check-golden` green) — the feared BUG-010 re-key wave did not
  materialize (main + single-segment stdlib have path == name).
- Full `scripts/ci --diff` + re-pin: 2082 cases, 1947 PASS / 135
  FAIL, zero drift beyond the ten predicted rows. Fast gate PASS end
  to end after re-pin.
- JC: cross-package var STORE initially fail-closed with a junk
  message ("field address on anonymous struct type") — upgraded to a
  real qualified-lvalue arm + the cross-var guardrail rather than a
  cosmetic refusal.
- JC: evaluation-order trap avoided in cross-var (mutating call beside
  an unsequenced read is spec latitude, not a strict-lane target) —
  reads sequenced explicitly.

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
