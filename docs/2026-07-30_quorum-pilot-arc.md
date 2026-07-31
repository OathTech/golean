# Arc: the quorum pilot (2026-07-30) — the sprint arc

Decided with the user 2026-07-30, immediately after the proof-corpus
catch-up arc merged (`main` @ e844c9c; corpus 787/471, untriaged 31,
Audit sweep 5006). This arc FUSES arcs 3 and 4 of the recorded sequence
(`docs/2026-07-25_arc-sequence.md`) — the interfaces campaign and the
quorum pilot — into one long arc with an external milestone, on the
user's direction: the machinery (two-program golden pins, proof-corpus
discipline, parallel runner, audited gates) is in place to sprint.

## THE GOAL

**A kernel-checked theorem about etcd-io/raft's real `CommittedIndex`**,
proven over the pinned actual lowering of the real `quorum` package
source, with the differential green on that package against etcd's own
test values — the first "Verdi results, but on real code" artifact
(F5 tier 1, `TODO.md`).

## Why this goal (recorded so the alternative is visible)

- It forces BOTH project-priority tracks at once: coverage (interfaces —
  the 48-case unlock and the raft blocker, since `AckedIndexer` is an
  interface; multi-package lowering; the stdlib-extern policy) and proof
  depth (`AckedIndex` returns `(Index, bool)`, so the sprint FORCES the
  `GoFuncSpec` arity widening — W1/prediction-3 debt stops being
  deferrable).
- The rejected alternatives: a pure interfaces campaign (no external
  success criterion), R4 concurrency (sequenced after the sequential
  story is proven on real code; BUG-002's fix wants that foundation),
  a pure proof-depth sprint (machinery with nothing real to aim at).

## Phases

0. **Statement first (the widening-loop discipline — this phase gates
   the rest).** Write the target theorem STATEMENTS as `def ... : Prop`
   targets, not results: (a) the `CommittedIndex` property (the returned
   index is committed by a majority quorum of the config against the
   acked indexes — exact form pinned against the real code, not from
   memory); (b) the interface-dispatch `GoFuncSpec` statement; (c) the
   `(T, bool)` / multi-result `GoFuncSpec` arity form. Plus the negative
   twins. This pre-declares the proof-corpus entries so the campaign
   cannot accumulate silent calculus debt. DEPENDS on `deps/raft` being
   cloned (the user is doing this in a separate thread) — statements are
   pinned against the real source, never reconstructed.
1. **Interfaces, guardrails first.** Fix defined-vs-alias identity
   (BUG-004's root — `type T int` currently lowers as an alias, erasing
   identity); retire raw-mangled-name dispatch for `TypeId`/method-set
   identity (the recorded green-on-junk risk — expect intentional
   transient reds, recorded per practice); type asserts + type switches
   frontend-side; differentially validate the dormant Gobra-era machine
   half (`toInterface`/`typeAssert`/dynamic dispatch). Seed corpus: the
   48+ interface-blocked cases + edge enumeration per the three-layer
   strategy. Design comparison against `deps/perennial`
   `new/golang/defn/interface.v` recorded in this doc's build log.
   **Interim mini-audit at phase-1 exit** (semantics dimension at
   minimum): interfaces touch the trust surface hardest, and a
   dispatch-identity defect discovered at phase 4 would be expensive.
2. **The real-code frontend.** Multi-package lowering; the stdlib-extern
   decision note (what `quorum` actually imports — check early whether
   `majority.go` still hand-rolls its insertion sort, which would spare
   a `sort` extern; decide how far externs reach before generics
   monomorphization is ever needed); order-insensitive map-fold
   observations for map-range nondeterminism (the D2 decision bites
   here — record it).
3. **Quorum through the differential** against etcd's own test values
   (`quorum` package tests as the oracle corpus). Every gap found
   becomes a corpus case FIRST (guardrails before tool buildout, as
   always).
4. **The proof.** Pin the actual lowering of the relevant `quorum`
   source (golden-pin mechanism, program #3+); walk `CommittedIndex`;
   discharge the phase-0 statements. Spec-surface widenings land here
   with witnesses in the same commit.

## STANDING CHECK: over-specialization (user directive 2026-07-31)

The pilot's danger mode is OVER-FITTING to the target: machinery that
pattern-matches on exactly what `CommittedIndex` needs instead of
modeling Go. The discipline, applied at every slice and EVERY audit
loop (interim and final — it is an explicit audit dimension from now
on):

- **Semantics changes must be probe-derived from Go, never
  case-derived from the corpus.** A fix whose justification is "makes
  case X pass" without an independent Go probe is the anti-pattern
  (the hash-phrasing fix is the positive example: 18-shape probe
  first).
- **Laws are stated at GENERAL Go shapes; the target appears only in
  WITNESSES.** A law premise that hardcodes a quorum name, value, or
  program fragment is over-fit (per-shape v1 scoping — key-only
  range, unary GoFuncSpec — is fine when the scope is a general Go
  shape and the widening is recorded as owed).
- **Frontend special cases must be capability-scoped, not
  target-scoped**: `slices.Sort`-at-integer-elements names a language
  capability with a fail-closed boundary; "the function quorum calls"
  would not be. The `calledIfaceMethods` anchor bug was exactly this
  class (anchors for what the target happened to call) — caught by
  the interim audit, fixed to declarations-to-fixpoint.
- **Corpus balance**: every new capability gets NON-quorum edge cases
  too, so green means "the capability works", not "the target works".

- **The concrete generality test (user, 2026-07-31): compare against
  Goose/Perennial's machinery** (`deps/goose`, `deps/perennial/new/
  golang/defn/*.v`). For each piece we build, ask: is our shape at
  least as general as their treatment of the same construct — and
  where it is narrower, is the narrowing a RECORDED v1 scope with a
  widening path, or an unacknowledged target-fit? (We may legitimately
  cover MORE than they do — e.g. our nondet map-range order where
  their model may fix one — that direction is fine; the failure
  direction is narrower-than-Goose without a record.)

Reviewers in every audit of this arc get this as a named dimension:
"find where the machinery is shaped by the target rather than by Go,
using Goose/Perennial's design as the generality reference."

## Out of scope

- Goroutines / channels / R4-R5 (BUG-002 remains the recorded blocker).
- Floats/complex (IEEE doctrine — own arc).
- Generics beyond what the phase-2 extern-policy note explicitly
  decides.
- Multi-node / network modeling (F5 tier-1 scoping only).

## Exit criteria

- Phase-0 statements proven over the pinned actual lowering; negative
  twins hold; all referenced from `proofs/Audit.lean`.
- `quorum`-package differential green against etcd test values; every
  interface machine rule exercised by at least one corpus case (no
  read-only-validated rules — the panicFrameDeferNil lesson).
- Every new law witnessed same-commit; sweep clean; untriaged ratchet
  not up; gate green.
- Full pre-merge audit (the unconditional ask) + merge sign-off.

## Process notes for this arc

- Long arc, one branch (`quorum-pilot`); interim slice gates stay green
  throughout; the phase-1 interim mini-audit is IN ADDITION to the
  final pre-merge audit, not a substitute.
- `deps/` restructure landed with this doc: reference checkouts move
  from sibling `../deps/` to gitignored in-repo `deps/` (CLAUDE.md
  updated) so the sandbox workdir grant covers them.

## Build log

- 2026-07-30: arc opened; branch `quorum-pilot`; this plan of record +
  the `deps/` restructure. Phase 0 blocked on the `deps/raft` clone
  (user, separate thread).
- 2026-07-30: `deps/` populated. **Phase-0 source discoveries** (all
  from reading `deps/raft/quorum/`, revising plan assumptions):
  1. `CommittedIndex` calls **`slices.Sort` (generic)** — the
     remembered hand-rolled insertion sort is gone from current
     etcd-io/raft. The phase-2 extern-policy note now has its central
     exhibit: a generic stdlib callsite on the critical path (`cmp` and
     `math.MaxUint64` ride along).
  2. **`Index` is a defined type** (`type Index uint64`) and
     `MajorityConfig` is a defined map type with METHODS —
     defined-type identity (BUG-004) and method-on-defined-type
     lowering are both directly on the goal path, not just
     interface-adjacent.
  3. `AckedIndex` returns `(Index, bool)` — confirms the multi-result
     forcing; `GoFuncSpec2` defined at phase 0 as the statement shape.
  4. `quick_test.go` contains etcd's own reference implementation
     (`alternativeMajorityCommittedIndex`, quickchecked 50k cases
     against the main one) — the declarative spec below is pinned to
     BOTH implementations' shapes, and `testdata/majority_commit.txt`
     is a ready-made oracle-value table for phase 3.
  5. Also on the path: `var stk [7]uint64` + array-to-slice
     (`stk[:n]`), `make([]uint64, n)`, map range with order-insensitive
     fill (sort follows — the D2 observation shape), uint64
     conversions.
- 2026-07-30/31: **Phases 1–3 LANDED** (see
  `docs/2026-07-30_interfaces-campaign-design.md` and
  `docs/2026-07-30_quorum-extern-policy.md` for the designs of record):
  - Phase 1 (interfaces campaign, commit 85f3659): identity + boxing +
    dispatch + asserts; corpus 471 → 525 passes, zero regressions;
    BUG-006 fixed, BUG-004 item 2 fixed, BUG-007 (promotion) opened;
    interim Opus mini-audit launched at exit per the plan.
  - Phase 2: `math.MaxUint64` was free (constant folding);
    `slices.Sort` landed as the `sortSlice` machine op (exact for
    integer elements; everything else fails closed) with guardrail
    cases first; single-package vendoring decided over true
    multi-package for the pilot (extern-policy note §scoping).
  - Phase 3: `quorum/committed-index-real` — the REAL etcd-io/raft
    `CommittedIndex`/`AckedIndexer`/`Slice` vendored VERBATIM (README
    records the delta), driven by etcd's own
    `testdata/majority_commit.txt` rows: **17/17 PASS against `go run`
    on the real source** — interface dispatch, defined-type identity,
    nondet map ranges, the sort extern, MaxUint64, all through the one
    chain.
- 2026-07-31: **Interim mini-audit RETURNED — 13 confirmed (1 critical,
  6 major), 1 refuted; the audit-warranted call vindicated.** The
  critical: interface satisfaction is VACUOUSLY TRUE for any interface
  with no recorded method requirements — `x.(error)` answers true/false
  depending on whether an unrelated line in the package calls
  `.Error()` (probe: machine 1, Go 0; generalizes to every
  non-package-declared interface; aimed square at the raft error
  idiom). The differential was 806/806 GREEN through all 13 — the
  "unexercised paths" class exactly as CLAUDE.md describes it. Fix
  wave in flight (wire-level interface method-set declarations with
  signature checking, fail-closed on unknown interfaces, compound
  unhashable keys, Go-exact hash-panic phrasing by map emptiness,
  render/message fidelity, **T method sets, BUG-007 comma-ok honesty),
  guardrail-case-first, with a full-run re-pin. All findings and probe
  evidence preserved for the final pre-merge audit's record.
- 2026-07-31: **Phase 4 OPENED.** Golden pin #3 landed:
  `GoldenQuorum.quorumLowered` — the real CommittedIndex lowering
  (1390-line repr, GENERATED literal file, byte-identical both links,
  check-golden 3/3). Remaining phase-4 plan, in order:
  1. **The nondet lifting core** — `mapIterNext` chooses ANY index of
     the remaining snapshot AND allocates the iteration variables
     (`bindIterVars` = pushScope + fresh cells): the first
     nondeterministic WP law (the D2/D3 "bites at the first nondet
     feature" moment). Shape: the law's premise supplies the
     continuation for ALL (idx, allocated addresses); safety = one
     witness successor. `wp_lift_step` already quantifies successors —
     only the determinism-pinning (`step_det`) is replaced by the
     ∀-successor obligation.
  2. Per-construct laws with same-commit witnesses: `sortSlice` (the
     spec is "cells hold a sorted permutation"; concrete instances
     suffice for the walk), mapGet/mapLookup comma-ok, dispatch through
     the interface anchor (`enterFrame`+`dynamicDispatch?` — a
     `wp_call_dynamic` law), `Stmt.typeAssert`, uint64
     conversion/normalization steps, map-literal build.
  3. The walk: `committedThreeSpread() = 102` (or a smaller driver
     first — `committedOneKnown() = 12` has a 1-entry map = trivial
     nondeterminism; do THAT first, then the 3-voter with its 3!
     orders) at `GoFuncSpec` strength over `quorumLowered`, through
     `goSpec_of_wp`; negative twin; tie to `committedIndexRef` via the
     phase-0 instances. The general
     `committedIndexRef_meets_spec` math theorem is delegated
     (in flight) and upgrades the concrete result to the declarative
     spec.
  4. Audit refs; manifest rows; gate; then the arc's FINAL pre-merge
     audit ask (the stop point).
- 2026-07-30: **Phase 0 LANDED** — `Specs/QuorumTargets.lean`:
  `IsCommittedIndex` (committedness + maximality + empty-`MaxUint64`
  convention), executable reference `committedIndexRef` (structural
  sort, so etcd's datadriven values pin by `rfl`), non-vacuity
  instances incl. maximality discharged on the 3-voter example +
  negative twins (102 committed; 103 and 101 both refuted);
  TARGET `committedIndexRef_meets_spec_statement` (phase-4 critical
  path: machine walk lands on the ref, this upgrades to the spec);
  `GoFuncSpec2` statement shape (discharge machinery = phase 4, no
  applicability claimed). Audit pins added for the instances; the
  `*_statement` defs stay unpinned targets by design.
- 2026-07-31: **Phase-4 item 2 (per-construct laws) LANDED** —
  `proofs/GoLeanProofs/Laws/QuorumOps.lean`, all witnessed same-commit
  on statements `rfl`-projected out of `GoldenQuorum.quorumLowered`
  (`QuorumPin.{rangeStmt,sortStmt,mapLookupStmt}`):
  - the **wide-statement (`stmtOpK`) walk**, which had NO laws at all
    (`wp_stmt_op_first`, `wp_stmt_op_shift_target`,
    `wp_stmt_op_shift_plain`, `wp_stmt_op_apply_store`,
    `wp_stmt_op_apply_read_store₂`) — every wide statement
    (`makeSlice`/`appendSlice`/`mapAssign`/`clearSlice`/`typeAssert`…)
    now enters through these;
  - `wp_sort_slice` + witness `wp_sort_slice_srt` on the REAL
    `slices.Sort(srt)`, `[3,1,2] ↦ [1,2,3]`. **Machine fact worth
    recording:** a slice's elements live in ONE backing cell (element
    locs are `Loc.index base i`, and `storeLoc` routes them through the
    base cell), so `sortSlice` is a SINGLE-cell step — the planned
    "own c0,c1,c2 individually / big-sep over element cells" shape is
    not what the machine does;
  - `wp_map_lookup` (comma-ok) + the new one-read/two-write lifting core
    `wp_read_store_step₂` (`Lifting.lean` topped out at one read + one
    write); the core derives the two targets' disequality from ownership
    (`pointsTo_ne`), so callers need no aliasing side-condition;
  - `wp_map_range_snapshot` (+ nil form) — the state-reading step that
    feeds `Laws/Range`'s nondeterministic `mapIterK` law.
- 2026-07-31: **BLOCKER RECORDED — the ghost state does not pin
  `σ.types`, and the quorum walk cannot proceed without it.**
  `GoCoreGS`/`stateInterp` pin `σ.functions` and `σ.methods` only. But
  `bindParams` normalizes each argument at its DECLARED type,
  `allocDecls` defaults results at theirs, and
  `concreteMethodForDynamic?` compares a box's dynamic tag against
  `canonicalTy σ method.recv` — all of which resolve `.defined` names
  through `TypeEnv.lookup σ.types` and fail closed on an unknown name.
  Every quorum entry point has `.defined`-typed parameters/results
  (`main.MajorityConfig`, `main.mapAckIndexer`, `main.Index`), and a Go
  method receiver is always a defined type. So a house-style premise
  `∀ σ, σ.functions = … → σ.methods = … → P σ` about ANY of them is
  FALSE (pick a σ with those pins and a hostile `types`), and a law
  carrying one would be VACUOUS — exactly the class the non-vacuity gate
  exists to catch. Consequences: (a) `wp_call_dynamic_enter` was NOT
  written (a scaffold would have been vacuous); (b) NO frame-entry law
  for this program is stateable today, so the `CommittedIndex` walk
  (item 3) is blocked, not just the dispatch step; (c) the
  `wp_map_lookup` witness stores into a `uint64`-typed cell where the
  lowering declares `main.Index` (recorded in its docstring).
  `typeEnv_pin_is_load_bearing` (`Laws/QuorumOps.lean`, Audit-pinned) is
  the kernel-checked demonstration: the same value at the same declared
  type normalizes to `.ok` under the program's type env and to
  `unsupported` under an empty one.
  **The fix** (arc-level, deliberately not smuggled into the laws
  commit): add `types : TypeEnv` to `GoCoreGS`, add
  `σ.types = GoCoreGS.types GF` to the state interpretation, and update
  the `obtain ⟨hfns, hmeths, hwf⟩` destructurings in `Lifting.lean`,
  `Laws/{Call,Range,Loop,Unwind}.lean` plus `Adequacy.lean`/
  `SurfaceExit.lean`'s construction sites. Nothing else about the laws
  changes: their `∀ σ` premises simply gain the `σ.types = …` hypothesis
  and become dischargeable by computation against the pin.
- 2026-07-31: **Phase-4 types-pin slice LANDED** — the recorded blocker
  above is FIXED, and a second, sharper one was found and fixed with it.
  1. **The `σ.types` ghost pin** (trusted surface). `GoCoreGS` gains
     `types : TypeEnv`; the state interpretation's pure conjunct becomes
     `σ.functions = prog ∧ σ.methods = methods ∧ σ.types = types ∧
     HeapWf σ`. Ripple size: **11 destructuring sites** across
     `Lifting.lean` (4), `Laws/{Call,Init,Range,QuorumOps,Unwind}.lean`
     (7), plus 4 `GoCoreGS` construction sites and 4 `Hwp`/`Hext`
     premise lists in `Adequacy.lean`, the 4 `Hwp` premises in
     `SurfaceExit.lean`, and the discharge sites in
     `Specs/{GoldenSurface,GoldenRecover}.lean`. The `∀σ` premises of
     `wp_store_step`, `wp_store_step₂`, `wp_read_store_step₂`,
     `wp_assign_store`, `wp_call_enter_arg1`/`ret1`, `enterFrame_cap1`
     and the `stmtOpK` apply cores now carry the pin hypothesis (strictly
     weaker premises).
     **The Surface judgments gained a `types : TypeEnv` parameter**
     (`GoTriple`/`Progress`/`GoInvariant`/`GoSpec`/`GoFuncSpec`/
     `GoFuncSpec2`) and the golden statements pin it to their program's
     `typeDefs` — matching what the executable driver seeds
     (`StepFn.runFunctionWithContextM`). The old empty default silently
     restricted every surface judgment to programs with no named types;
     all existing golden/recover statements stay TRUE and green.
  2. **`wp_call_dynamic_enter₂`** (`Laws/Call.lean`) — frame entry
     through an interface ANCHOR, with witness
     `wp_call_dynamic_enter_ackedIndex` on the REAL
     `main.AckedIndexer.AckedIndex` dispatch of the pinned lowering.
     Supporting general machinery: `wp_alloc_step₄` (first
     multi-allocation lifting core), `bindParams₂`/`allocDecls₂`,
     `allocMany`/`HeapWf.allocMany`, `heapToMap_set_base₂`/`₄`,
     `insert_eqv`, `execState_pin_eq`.
  3. **SECOND BLOCKER, found and fixed: `BEq Ty` was OPAQUE.** `Ty` is a
     nested inductive (`funcType` carries `List Ty`), and Lean's derived
     `BEq` for nested inductives is an opaque function — no equation
     lemmas, no `unfold`, no `decide`, not even `rfl` on two identical
     closed types. Dynamic-type identity is decided by `==` on `Ty`
     (`concreteMethodForDynamic?`, `typeAssert`, boxing, interface
     satisfaction), so **no dispatch fact was kernel-provable at all** —
     the entire interface half of the proof story was unreachable, and
     the derived function was also a `partial`-flavoured definition in
     the semantic core. Fix: `Ty.eqb`/`Ty.eqbFuel`/`Ty.eqbListFuel` in
     `GoLean/GoCore/Value.lean` — total, transparent, fuel-bounded
     (1024), fails CLOSED on exhaustion; `deriving BEq` dropped from
     `Ty`. Runtime change, so the FULL differential was re-run:
     **846/846 identical to `baselines/native-full.tsv`** (581 pass /
     265 fail, unchanged set; negative lane 309/309). Baseline NOT
     re-pinned — nothing moved.
  4. **Phase-4 item 3 (the walk): the recorded FALLBACK, not the full
     result.** `Specs/GoldenQuorumWP.lean` holds the target STATEMENTS
     (`quorumOneKnownFuncSpec_statement`, its negative twin,
     `quorumAckedIndexFuncSpec2_statement`) as `def … : Prop` in the
     phase-0 idiom, plus the PROVEN math half:
     `committedIndexRef_oneKnown` (`= 12`, `rfl`),
     `isCommittedIndex_oneKnown` (via the proven
     `committedIndexRef_meets_spec`), and the negative twin at 11. The
     machine walk is NOT discharged; what it still needs is listed in
     the file header and in the proof-corpus manifest's owed list
     (allocating wide-op apply core for `makeMap`, `makeSlice`/
     array-to-slice, two-result frame exit, ~200-step composition). No
     `sorry`, no scaffold claiming more than it proves.

  **Over-specialization check (standing item §STANDING CHECK), per new
  law — is the STATEMENT target-free?**
  - `wp_alloc_step₄` — TARGET-FREE. Any four cells, any successor config
    as a function of the four fresh addresses. Narrowing: length fixed
    at 4 (the general shape is a list; `allocMany` already is). Recorded
    as owed.
  - `bindParams₂` / `allocDecls₂` — TARGET-FREE. Any two params/results,
    any state. Arity-specialized, widening owed.
  - `wp_call_dynamic_enter₂` — TARGET-FREE. Anchor id, concrete callee,
    dynamic type, parameter/result names and types, and all values are
    law variables; only the arity (2 params / 2 results) is fixed, as in
    the existing `wp_call_enter_arg1`/`ret1`/`cap1` family.
  - `wp_read_store_step₂`, `wp_stmt_op_apply_*`, `wp_map_lookup`,
    `wp_store_step`(`₂`), `wp_assign_store` premise widenings —
    TARGET-FREE (they only GAINED the general `σ.types` pin hypothesis).
  - `execState_pin_eq`, `insert_eqv`, `heapToMap_set_base₂/₄`,
    `allocMany`, `HeapWf.allocMany` — TARGET-FREE, no program mentioned.
  - `Ty.eqb` — TARGET-FREE: a language-level structural equality on Go
    types.
  - Quorum names appear ONLY in: `Laws/QuorumOps.lean`'s `QuorumPin`
    projections and witnesses, and `Specs/GoldenQuorumWP.lean`'s target
    statements. No law statement, machine rule or frontend path names
    `main.*`.

  **Goose/Perennial comparison, per new mechanism** (`deps/perennial`
  `new/golang/defn/*.v`, `deps/goose`):
  - *Dispatch entry*: Perennial resolves a method with the semantics
    function `methods : go.type → go_string → val → func.t`
    (`postlang.v:106`, used through the `rcvr @! type @! method`
    notation) — receiver- and arity-generic, because the result is a
    GooseLang closure and calls are curried, so no arity family arises
    there. Ours is arity-specialized (2/2) for the
    same reason the `cap1` family is: GoCore's `enterFrame` allocates one
    cell per parameter and per result in ONE step, so the WP law must
    name them. NARROWER; widening recorded (see `wp_alloc_step₄`'s scope
    note).
  - *Allocation core*: Perennial allocates via `ref`/`alloc` one
    location at a time and composes with `wp_bind`; GoCore's frame entry
    is atomic over 4 allocations, which has no Perennial analogue —
    ours covers MORE per step (and is the granularity ledger's frame
    entry entry).
  - *Type identity*: Perennial boxes as `interface.mk_ok from v` and
    compares dynamic types with a plain `EqDecision` on `go.type`
    (`postlang.v:183`, `interface.v`'s `go_eq_interface`) — decidable and
    fully reasoning-friendly in Rocq despite `go.Named`'s list argument.
    Ours reaches the same place only AFTER replacing the derived opaque
    `BEq Ty` with `Ty.eqb`; before that we were strictly WORSE than
    Perennial on exactly this axis, which is the sharpest argument that
    the fix was not optional. Ours additionally fails closed on depth
    exhaustion, which Perennial's structural decision does not need.
  - *`σ.types` pin*: Perennial's `go_type` resolution is syntactic (no
    ambient type environment), so there is no analogue; the pin is a
    consequence of GoCore carrying named-type declarations in the state.
    Ours covers MORE state, at the cost of the pin.
- 2026-07-31: **Phase-4 slice 5 LANDED — the FIRST `GoFuncSpec2`
  discharge (W1 paid), the two-result frame exit, and the `methods`
  ghost pin.** `GoLean.Surface.quorumAckedIndexFuncSpec2` is a THEOREM:
  the real `main.mapAckIndexer.AckedIndex` of the pinned lowering, at
  `GoFuncSpec2` strength on a concrete one-entry receiver — "in any
  admissible heap, beside any frame, `m.AckedIndex(3)` leaves `12` and
  `true` in the caller's two cells". The walk is
  `wp_ackedIndexCall → wp_ackedIndex_body` (`Specs/GoldenQuorumWP.lean`),
  composed only from general laws.
  1. **New general laws** (`Laws/Call.lean`), each witnessed same-commit:
     the multi-operand call walk `wp_call_target_next`,
     `wp_call_targets_done_arg`, `wp_call_arg_next` (there were NO
     operand-shift laws — the golden program has at most one operand per
     kind); `wp_call_enter₂`, the STATIC 2-parameter/2-result frame entry
     (witness `wp_call_enter_ackedIndexImpl` on the pinned method — the
     exact complement of the dynamic-dispatch witness: same method, other
     dispatch answer); and **`wp_frame_return₂`**, the two-result frame
     exit, on the new one-step core `wp_read₂_store₂_step` (two owned
     cells read, two written in order; the targets' disequality comes
     from ownership, so no aliasing side-condition).
  2. **`wp_init`'s premise widened** to carry the `σ.types` pin — the
     unpinned `∀σ` form is FALSE at every named Go type (`defaultValue`
     resolves `.defined` through `TypeEnv.lookup` and fails closed), so
     the quorum body's `idx : main.Index` declaration was unreachable and
     a scaffold would have been vacuous there. Same class as the
     types-pin slice's finding; strictly weaker premise, all callers
     unchanged but for an extra `_`.
  3. **SECOND TRUSTED-SURFACE PIN: `methods`.** The Surface judgments
     (`GoTriple`/`Progress`/`GoInvariant`/`GoSpec`/`GoFuncSpec`/
     `GoFuncSpec2`) and the exit pipe (`SurfaceExit.lean`) built their
     `ExecState` with `methods := #[]`. `enterFrame` consults the method
     table on EVERY call, so every surface judgment was silently
     restricted to programs with no methods — no interface dispatch at
     all, which is precisely the fragment the raft target lives in. They
     now carry the program's `methods`, matching what the executable
     driver seeds (`StepFn.runFunctionWithContextM`). Ripple: 5 judgment
     definitions, 4 exit-pipe premise lists + 2 `ExecState` constructions,
     and the golden/recover/quorum statement sites (the golden and
     recover programs' tables are `#[]`, so those statements are
     unchanged in content). `Adequacy.lean` needed nothing — it was
     already generic in `σ.methods`.
  4. **A FALSE target, found and corrected (recorded, not patched
     quietly).** The phase-0 `quorumAckedIndexFuncSpec2_statement` passed
     `#[]` arguments to a two-parameter method: `enterFrame`'s arity
     check fails closed, the configuration is STUCK, so `Progress` — and
     with it the whole statement — was FALSE, not merely unproven. Root
     cause: `GoFuncSpec2` hardcoded the caller environment to the two
     `$callres` bindings, so an argument expression could denote nothing
     but a literal and a method with a heap-carried receiver (i.e. every
     Go method) was UNSTATEABLE. Fix: `GoFuncSpec2` gains a caller
     `argEnv` (the receiver's binding, exactly as a Go callsite names a
     local); `argEnv = []` is the phase-0 shape verbatim. The
     postcondition was also strengthened from the one-sided
     `b = true → n = 12` (satisfiable by a method that never finds
     anything) to `n = 12 ∧ b = true`. Both corrections are recorded in
     the statement's own docstring and in `proofs/Audit.lean`.
  5. **Vacuity guard, same commit:** `quorumAckedIndexPre_satisfiable`
     exhibits a concrete four-cell heaplet satisfying the discharged
     precondition (a `GoSpec` whose `InitialSplit` no state can meet is
     true of anything — the failure class the gate exists for), on the
     new general `sat_sep_insert`.
  6. **NOT done, still owed for the driver walk** (unchanged from the
     previous entry minus the exit): the ALLOCATING wide-op apply core
     (`makeMap`/`makeSlice` allocate inside `applyStmtOp`), array-to-slice
     (`stk[:n]`), the nondeterministic map-range composition, and the
     ~200-step assembly. Deliberately not half-landed here.
  Gate: `scripts/ci` PASS (846/846 differential unchanged, 309/309
  negative, 44 eval tests, Audit sweep 5792 declarations axiom-clean).
  **No runtime file changed in this slice** — proofs and docs only.

  **Over-specialization check (standing item §STANDING CHECK), per new
  law — is the STATEMENT target-free?**
  - `wp_call_target_next` / `wp_call_targets_done_arg` /
    `wp_call_arg_next` — TARGET-FREE and arity-FREE: any function id, any
    operand lists, any values, any continuation. These are the general
    call-operand handoffs; nothing about a program appears.
  - `wp_call_enter₂` — TARGET-FREE. Callee, parameter/result names and
    types, values and the caller's target locations are law variables;
    only the arity (2 params / 2 results) is fixed, as in the whole
    `wp_call_enter_arg1`/`ret1`/`cap1`/`dynamic_enter₂` family. Widening
    owed (recorded on `wp_alloc_step₄`).
  - `wp_frame_return₂` / `wp_read₂_store₂_step` — TARGET-FREE. The store
    facts are premises (the machine's own cell-conditioned computations),
    so the law is general in the cells' TYPES, not just their values —
    an `(int, bool)` pair is only how the witness instantiates it. Arity
    2 fixed; n-ary widening owed. The FALL-path twin is owed too.
  - `wp_init`'s widened premise, and the `methods` pin on the Surface
    judgments — TARGET-FREE: both only add a general hypothesis about the
    ghost state / the program's own tables.
  - `sat_sep_insert`, `heaplet_get?_*` — TARGET-FREE heaplet algebra.
  - Quorum names appear ONLY in: `QuorumPin` projections, the witnesses
    (`wp_call_enter_ackedIndexImpl`), the walk
    (`wp_ackedIndex_body`/`wp_ackedIndexCall`) and the target statement.
    No law statement, machine rule or frontend path names `main.*`.

  **Goose/Perennial comparison, per new mechanism** (`deps/perennial`
  `new/golang/defn/`, `deps/goose`):
  - *Call-operand handoffs*: no analogue. GooseLang calls are curried
    applications whose argument evaluation is `wp_bind`-composed out of
    the ordinary expression rules, so there is no operand-plan
    continuation and no shift laws; GoCore's CEK call form makes each
    handoff a machine step, so each needs a law. Ours is MORE
    fine-grained (and the granularity is what makes the atomicity ledger
    checkable); theirs is more compositional.
  - *Two-result exit*: Perennial returns multi-value results as a TUPLE
    value from an ordinary call, destructured by pure projections
    (`new/golang/defn/` — no frame-exit family exists there at all).
    GoCore writes the caller's cells INSIDE the exit step (Go's
    call protocol as the machine models it), which is why the arity shows
    up in the law and why both cells move atomically — a granularity
    ledger entry, not an accident. Ours is NARROWER (arity-bound) and
    covers MORE per step; the honest comparison is that Perennial pushed
    the arity into the value language while we push it into the law.
  - *`methods` pin*: same shape as the `σ.types` pin's comparison —
    Perennial resolves methods syntactically (`methods : go.type →
    go_string → val → func.t`, `postlang.v:106`), so no ambient method
    table and no pin; GoCore carries the table in the state, so the
    surface judgment must pin it or silently speak about a
    method-free program. Ours covers MORE state, at the cost of the pin.
