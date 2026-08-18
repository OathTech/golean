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

## Numbering (corrected 2026-08-18, audit finding F4)

Slice numbers in this log are the COMMIT slices, and each heading
names its commit. The original entries had drifted: the identity
design note was written up as "slice 2" though it landed inside the
guardrails commit, which pushed the implementation and probe entries
to 3 and 4 against commit messages that said 2 and 3. Entries are in
commit order below; the audit-fix round follows them.

## 2026-08-18 — slice 1 (`e3c353e1`): guardrails RED + the identity design note

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
- The design note landed in this SAME commit (it is the
  guardrails' derivation, written before implementation):
  - `docs/2026-08-18_multipackage-identity.md` (design of record):
    path-keyed TypeId/FuncId grammar + injectivity argument; BUG-010
    fix = qualifier `pkg.Path()` at the one boundary constructor;
    `checkPackageNameCollisions` retires in favor of the dotted-path
    grammar guard; rendering residue argued honestly (display-vs-
    identity separation is a GoCore change, out of scope, filed as
    BUG-059 with the pinned witness); raft vendors at SHORT dot-free
    paths (path == name ⇒ exact rendering, oracle-shared tree);
    cross-package init = the spec-pinned Go 1.21+ schedule, one
    concatenated `$pkginit` (that schedule was then IMPLEMENTED over
    the local packages only — audit F1 / BUG-060; §5 of the note and
    the loader are corrected in the audit-fix round below);
    fail-closed register (dot imports of
    source packages refuse at the loader; the stdlib dot-import defect
    stays recorded and untouched; shims stay main-package-only).

## 2026-08-18 — slice 2 (`19ae5439`): the implementation lands (guardrails FLIP)

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

## 2026-08-18 — slice 3 (`e5f44abd`): the tracker smoke probe (W1.3 discovery instrument)

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

Post-inventory state: the whole probe program (7 funcs, 40 methods,
16 TypeDefs — counts CORRECTED in the audit-fix round, derivation
below) exports clean, and the machine RUNS it:
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

**Wire counts, reproduced** (audit finding F3; re-exported
`artifacts/probe-tracker-shimpb` and counted the wire's top-level
arrays):

- `funcs` = **7**: tracker 4 (`NewInflights`, `MakeProgressTracker`,
  and the two lifted func literals `Config.Clone$lit0` /
  `ProgressTracker.QuorumActive$lit0`) + main 2 (`probeTracker`,
  `probeCommitted`) + the synthesized `$pkginit`.
- `methods` = **40**: quorum 8 (JointConfig 3, MajorityConfig 3,
  AckedIndexer 1, mapAckIndexer 1) + tracker 31 (Inflights 7,
  Progress 10, ProgressTracker 11, StateType 1, Config 1,
  matchAckIndexer 1) + main 1 (`mapAckIndexer.AckedIndex`, the probe's
  own AckedIndexer implementation).
- `types` = **16**: raftpb 1 (ConfState) + quorum 6 + tracker 8 +
  main 1.

The originally recorded 6 / 39 / 15 each dropped exactly one item —
`$pkginit`, main's one method and main's one type — i.e. they counted
the imported tree and the two probe entry points but not the
synthesized initializer or the main-package helper. The claim the
sentence makes ("exports clean") is unaffected; the numbers are now
the whole exported program's, and reproducible by counting those
three arrays.

## 2026-08-18 — audit fix round, F1a: the init-order stdlib omission, RED first

- Derivation: pre-merge audit finding F1 (HIGH), guardrails-first
  contract — the reproduction lands as a corpus case BEFORE the code
  moves, so the defect is pinned by a red rather than by prose.
- New case `Corpus/coverage/exec/multipkg/init-order-stdlib` (two
  subjects): `rec` (recorder), `bbb` imports rec and pushes 2, `aaa`
  imports rec AND `sync` (blank import — ordering effect only, no
  sync semantics required) and pushes 1, main imports all three.
- Hand-derivation: `rec` is ready from step one and "rec" < "sync", so
  the lex-first-ready rule initializes rec BEFORE sync; at the step
  after rec, `aaa` is still blocked on sync while `bbb` is ready, and
  no ready package sorts before "bbb" — so bbb goes first. Observed
  schedule 21, push counts A=2/B=1 (marks 201). Oracle-confirmed by
  `go run` under a GOPATH assembly: `seq= 21 marks= 201`.
- The machine answers 12 / 102 — the loader's initialization list
  ranges over LOCAL packages only, so `sync` is not in it and `aaa`
  looks ready. Landed as 2 honest FAILs at stage `differential`
  (a WRONG ANSWER, not a coverage gap).
- Filed BUG-060 with both ids, so the reds are explained rather than
  raising the untriaged ceiling (still 25/25).
- Control: `multipkg/init-order` still PASSES — its local-only
  expectation was correct AS WRITTEN, because that case imports no
  stdlib package. The two cases are complements, and the old one is
  kept exactly as-is.
- Full `scripts/ci --diff` + same-commit re-pin: 2084 cases, 1947 PASS
  / 137 FAIL, drift = exactly the two new ids, nothing else.

## 2026-08-18 — audit fix round, F1b/c/d: the list is built over ALL packages

- Derivation: `spec#Program_initialization` orders "the list of all
  packages" of the COMPLETE program; `spec#Program_execution` defines
  that as main "with all the packages it imports, transitively". The
  stdlib packages are nodes in that list whether or not we model them.
- `tools/nativefrontend/load.go`: new `specInitOrder` builds the node
  set as the source units PLUS the transitive closure of their
  non-source imports, takes each node's edges from its import
  DECLARATIONS, runs the spec's lexicographic-first-ready walk over the
  whole set, and drops the non-source nodes only after they have taken
  their positions. They emit NO initializer — their bodies are not
  modeled — and only the ORDERING EFFECT lands, which is computable
  from the import graph alone. Type-check order (a separate, weaker
  requirement — any dependency order works) stays local-only;
  conflating the two was the defect.
- JC: non-source edges come from `go/build`, NOT
  `types.Package.Imports()` (the auditor's suggested route). Measured
  at Go 1.26: export data is neither a subset nor a superset of the
  import clauses — `sync`'s lists `internal/abi`, which sync does not
  import, and omits `runtime`, which it does. go/build reports the
  actual clauses, is 20x cheaper (25 ms vs 465 ms for fmt's closure),
  and needs no force-load walk (export-data stubs come back with an
  EMPTY `Imports()` until separately imported — probed before relying
  on either).
- Fail-closed: an import path go/build cannot resolve REFUSES the
  export (a missing edge silently perturbs the schedule, which is the
  whole class of this bug); a cycle in the full list refuses; and the
  loader now CHECKS rather than assumes that the list ends at main
  (main.go reads `units[len-1]` as the main unit).
- Cost: a single source unit short-circuits before touching the import
  graph (one package, one position), so every single-package case —
  the overwhelming majority of the corpus — keeps exactly the old path
  and cost. Only multi-package cases pay the closure walk.
- Flip: both `multipkg/init-order-stdlib` rows go GREEN (12 -> 21,
  102 -> 201, matching `go run`). Control `multipkg/init-order` PASSES
  throughout, unchanged. BUG-060 closed.
- Full `scripts/ci --diff` + re-pin: 2084 cases, 1949 PASS / 135 FAIL.
  Drift = exactly those two flips; ZERO blast radius, nothing else
  moved (no single-package case, no other multipkg row).
- F1d, the raft shape: re-ran the tier-2 tracker probe
  (`artifacts/probe-tracker-shimpb`) through the frontend. The emitted
  unit order CHANGED, and to the spec's answer:
    - before: `quorum, raftpb, tracker, main`
    - after:  `raftpb, quorum, tracker, main`
  Derivation: `quorum` imports `math` + `slices`; the raftpb stand-in
  imports nothing; `tracker` imports raftpb + quorum + slices. raftpb
  is ready from step one, `quorum` is not ready until `slices` has
  run, and "raftpb" < "slices" — so raftpb takes its position first,
  even though "quorum" < "raftpb" lexicographically. The old
  local-only list saw both as ready at step one and took the
  lexicographic order, giving quorum first. Wire counts are unchanged
  by the fix (7 funcs / 40 methods / 16 types before and after).

## 2026-08-18 — audit fix round, F2: the husk-gate exemption scan is scoped to imports

GATE-INFRA DIFF — flagged for the record (CLAUDE.md: gate/lint changes
get their own delta-review attention).

- Defect: `scripts/check-coverage`'s multi-package exemption scanned
  the WHOLE file text for quoted strings, so any string literal that
  spelled a sibling directory's name exempted that directory. The husk
  gate exists to catch a nested case dir with .go files and no
  metadata — invisible to case discovery — and this made it go quiet
  on exactly that.
- Fix: `_import_paths` parses IMPORT DECLARATIONS only (both forms;
  comments stripped first; the optional leading identifier covers
  named, blank and dot imports — all real imports). Paths that could
  escape the case dir are dropped with the same shape guard the
  frontend loader's `localDirFor` uses.
- Reproduction, before and after, against the SHIPPED code (fixture
  `artifacts/probe-huskgate`: main.go imports `helper`, carries the
  literal `"forgotten"`, and `forgotten/` has .go files, no metadata,
  no importer):
    - old: exempt {forgotten, helper}, husks {} — silent;
    - new: exempt {helper}, husks {forgotten} — loud.
- All 14 pre-existing live exemptions still hold (plus the 3 dirs this
  round's `init-order-stdlib` adds, and 4 intermediate dirs on the way
  to `blue/inner` and `red/inner`, for 21 exempt dirs total):
  cross-const/limits, cross-func-call/mathutil,
  cross-type-method/counter, cross-var/store, diamond-import/{base,
  left,right}, init-order/{alpha,beta,reclog},
  same-name-identity/{blue,red}/inner,
  same-name-identity-panic/{blue,red}/inner.
- The scan bias is fail-CLOSED by construction: a shape the parser does
  not recognize drops an exemption and husks loudly (a visible red),
  never the reverse.

## 2026-08-18 — audit fix round, F3/F4 + the recorded non-findings

- F3: the tracker probe's wire counts corrected to the reproduced
  7 funcs / 40 methods / 16 TypeDefs, with the by-unit derivation
  shown in the slice-3 entry (the originally recorded 6 / 39 / 15 each
  dropped one item — `$pkginit`, main's one method, main's one type).
- F4: slice numbering realigned to the commits (see the Numbering
  section), and the identity note's §8 blast-radius prediction
  corrected from 8 rows to 9, with the note that `multipkg/cross-var`
  joined DURING the implementation slice rather than being predicted.

Two auditor observations recorded as NON-FINDINGS, so they are on the
record rather than in a transcript:

1. **Build-constraint asymmetry (pre-existing, unchanged by this
   arc).** Both pipeline legs select corpus files by the same rule —
   "`.go` and not `_test.go`" (`nonTestGoFile` in the frontend,
   the same suffix test in `tools/coverageharness`) — and NEITHER
   applies Go's build constraints, while the oracle's `go run` does.
   A corpus file carrying a `//go:build` line or a `_GOOS.go` name
   would therefore be lowered by the frontend and skipped by Go. No
   corpus file has one today (checked: zero `//go:build` / `// +build`
   lines under `Corpus/`), and the asymmetry predates the
   multi-package work — the single-package frontend had the same rule.
   Recorded, not fixed, and worth noting alongside its opposite: the
   F1b initialization list DOES honor build constraints for stdlib
   packages, because `go/build` applies them, which is what keeps the
   list in agreement with the oracle on this host.
2. **The dropped baseline column-header line (harmless by code).**
   The slice-2 re-pin dropped `result<TAB>id<TAB>stage` from
   `baselines/native-full.tsv`; the file at `main` has it. Harmless
   because every reader skips it explicitly:
   `scripts/coverage-baseline-diff` has `$1 == "result" { next }` on
   both the baseline and the results pass, `scripts/check-coverage`
   skips `p[0] != "result"`, and `check-bugs.sh` matches on `$2 == id`
   so the row can never be an id. Restored anyway in the F1b re-pin,
   for format parity with `main`.

## 2026-08-18 — delta-review fix round, slice 1: the pruned-schedule guardrails (RED)

The delta review found that the F1b fix — build the initialization list
over ALL packages of the complete program — is still not gc's schedule.
Guardrails first: three cases pin what gc actually does, hand-verified
with `go run`, landed RED, baseline re-pinned in the same commit.

**The ground truth** (read in `deps/go/src`, Go 1.26.5, and confirmed by
`go run` on each probe):

- `cmd/compile/internal/pkginit/init.go`, `MakeTask`: a package emits a
  `..inittask` record only if it has residual initialization WORK or an
  inittask-bearing import —
  `if len(deps) == 0 && len(fns) == 0 && path != "main" && path != "runtime" { return }`.
  `fns` is what survives `cmd/compile/internal/staticinit`: a variable
  initializer folded into the data section leaves nothing to run, and an
  `init` function with an empty body is dropped. `deps` is the imports
  that themselves bear inittasks.
- `cmd/link/internal/ld/inittask.go`, `inittaskSym`: the linker walks
  exactly those records, popping the lexicographically first READY one
  BY SYMBOL NAME (`lexHeap` compares `ldr.SymName`; the record for
  package p is `objabi.PathToPrefix(p) + "..inittask"`).

So the schedule is a lexicographic-first-ready walk over a **pruned**
node set, ordered by a **mangled** key — two divergences from the
spec's literal "list of all packages, sorted by import path", both
observable from Go source.

**The cases** (`Corpus/coverage/exec/multipkg/`):

- `init-order-pruned` — the decisive STATIC-vs-DYNAMIC pair, two
  subjects over the same shape. `sm` imports `zst` (`var X = 5`,
  statically folded, NOT a node) and is ready at step one: `rec.S == 12`.
  `dm` imports `zdy` (`func init() { Y = 5 }`, a real node) and must
  wait: `rec.D == 21`. The dynamic subject is the CONTROL — the
  unpruned model gets it right by accident, which is exactly why the
  static one alone would not have been decisive. Machine: 21 / 21.
  Go: 12 / 21. `static` RED, `dynamic` PASS.
- `init-order-pruned-stdlib` — pruning applies to the stdlib too. The
  minimal divergence found by the 120-seed randomized differential
  harness (`artifacts/delta-review-probe/gen2.py`, seed 46): two
  packages whose only imports are the recorder and one blank stdlib
  import each — `sync/atomic` and `unicode/utf8`, both of which have no
  init work at all and therefore gate nothing. Machine 21, Go 12. RED.
  Complement of `init-order-stdlib`, where `sync` DOES have work and
  its ordering effect is real; the pair says it is not "importing a
  stdlib package" that delays you, it is importing one gc schedules.
- `init-order-tiebreak` — the sort key is the symbol name.
  `"x" < "x-y"` as import paths, but `"x-y..inittask" < "x..inittask"`
  as symbols ('-' = 0x2d < '.' = 0x2e), so gc initializes `x-y` first.
  Both packages are ready at step one, so the tie-break is the only
  thing deciding the order and the observation IS the tie-break.
  Machine 12, Go 21. RED.

**Drift:** exactly the four new ids, nothing else. Every pre-existing
multipkg row holds, `init-order-stdlib/{seq,marks}` included. Full run
2088 cases, 1950 PASS / 138 FAIL.
