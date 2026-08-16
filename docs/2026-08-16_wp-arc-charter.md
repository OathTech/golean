# The WP arc — proof automation and library regularity (2026-08-16)

Status: CHARTERED (user-directed). THE AIM, in the user's words: *"build
proof automation that makes everything easier and more regular (and
structure the existing lemmas so they're easily discoverable by an
agent working on proof N+1)."* This arc builds INFRASTRUCTURE ONLY.

**NON-GOALS, absolute:** no example is moved — no headline restatement,
no harness change, no gallery-claim change, no corpus/baseline change,
no designation, no GoCore/frontend change. (Retrofitting example PROOF
INTERNALS — replacing private duplicate lemmas with kit delegations and
deleting the copies, the P6 rule — is in scope and is the point;
everything a reader or the oracle sees is frozen.) No search-based
automation (the standing principle below). Statements and axiom pins
byte-identical at every commit of this arc.

**THE STANDING PRINCIPLE (compute-and-emit):** golean-wp automation is
compute-and-emit — the interpreter is the decision procedure. Any
search component must be finite-table, probe- or evaluation-grounded,
and fail-closed, with failure legible at generation time. No open simp
sets, no backtracking search, no unbounded defeq. The line moves only
by recorded user decision.

Primary design input: `docs/2026-08-16_wp-library-design.md` (the R5
report). Process rules inherited from the campaign (trip report §
lessons + addendum): manifest discipline for record edits; every
summary number derivation-anchored; cross-doc cites unit-anchored or
commit-qualified; one writer per worktree; §12 consumer rules
(≥2 landed consumers per lift, fixtures, P6 rollback, measured
deltas); Audit/Kit.lean pins for every new public kit surface.

## Slice 1 — lift wave 1 (pure lifts; every shape pre-drafted in the
campaign ledger, risk nil)

In dependency order: the op-fact/`unorm` families (incl. the
`intKind_normalize_idem` LIFT-OUT-OF-HeapBridge item — the recorded C4
resolution) → `SliceMem.familyF`/`familyOf` + signed variants +
`prefixPadL`/`takePad` → `swapList` surgery + count algebra →
`Frame/Threshold.lean` (the five-site frame/rebase layer) →
`FuelMeasure.stepFnIter_iterate_bail` (five consumers) → GAP-RESLICE +
`stepFn_return_frame` + the queue glue combinators. DONE: every lifted
family has ZERO surviving example-local copies (grep-verified per
lift); measured line/time deltas recorded per lift; Kit pins added.
Projected from the ledger: ~2,500–3,000 landed lines deleted;
sort-class marginal cost 3,300 → ~2,400.

## Slice 2 — lift wave 2 (new shapes; consumers 2–5 each, all landed)

The footprint pack (`FreshFrom` algebra, `set_comm`-with-presence, the
heap battery) + the call-span combinator → GAP-APPEND, element-kind
generic, spill capacity existential → `StringMem` (values only, no
heap half) → growing-heap front support → the `derive_entry_eq` string
arm → GAP-C1b (parameterize `MapLoops` over the remaining three
statement constants). Same DONE per lift as slice 1.

## Slice 3 — library REGULARITY (early; the Guide comes LAST)

Naming + module conventions normalized across StepKit/SliceMem/MapMem/
MapLoops/FuelMeasure/StringMem/Frame; sealed-API sections consistent;
docstring cross-pointers in place. (AMENDED 2026-08-16, operator review
finding 1: the Kit Guide and its acceptance test move to the CLOSING
slice — a guide written before the evaluator and sugar land describes
a library that no longer exists by arc-end, and gets written twice.)

## Slice 4 — the mirror symbolic evaluator (Route B; the centerpiece)

**Gate: the DOMAIN DESIGN NOTE ships first and the user reviews it
before any commutation proof starts.** The note fixes: the value
typeclass split (CONSTRUCTORS build symbolic terms; INSPECTIONS quit
predictably — branches, control-feeding equality, choice consumption,
addresses computed from symbolic values); the symbolic term
representation (computable, decidable-quit); v1 scope = symbolic
SCALARS over a concrete heap skeleton (the straight-line window
fragment — no forking, no path conditions, no symbolic map keys); the
quit-condition catalog.

Then: `stepFn'`, the mirrored parametric step (proof-land, GoCore
untouched — Route B by user ruling: *"it'd be nice to do this without
touching the trust surface"*); the concrete-instance equivalence
`stepFn' @ GoValue = stepFn` (arm-by-arm, rfl-shaped) — LANDED IN A
DEFAULT BUILD TARGET so mirror drift FAILS THE BUILD, not a review
(operator review finding 4);
the symbolic instance = the evaluator; per-operation commutation
lemmas; and THE REFINEMENT THEOREM (which ships, per the standing
non-vacuity gate, IN THE SAME COMMIT as its discharge witness — a real
window from a shipped example, evaluated by `symEvalWindow` and
transported to a `stepFnIter` fact; no witness ⇒ scaffold, marked so):

    symEvalWindow S = some S'  →  ∀ ρ, stepFnIter n (γ_ρ S) = γ_ρ S'

— the ∀ρ universality IS the full-precision claim (the value-domain
frame rule: the machine is parametric in values it never inspects; the
third member of the γ-square family after the address-frame theorem).
Quit-minimality is DOCUMENTED, not proven (an over-eager quit costs
automation, never soundness). **Outside-the-TCB is verified, not
asserted**: no `Sym*` constant in any headline statement closure (the
existing walker), and the deletion test extended — removing the whole
symbolic layer leaves every statement elaborating.

**Acceptance: matmul, measured in two stages** (operator review
finding 5 — the snapshot predates the gap closure, G4 and the fix
rounds): (a) restore from `refs/snapshots/gc-proofs-a/
matmul-machine-layer` and RETROFIT to the current kit first, recording
that cost/shrinkage as the baseline; (b) THEN produce the segment
layer via the evaluator and land `matmul_ok` COMPLETE, gated, pinned —
so the evaluator's contribution is measured separately from retrofit
value. The GAP-RFL-COST class closes on the artifact that discovered
it. Fallback if the evaluator runs long: probe-driven
emission (`derive_seg` mode (a)) is the recorded interim, but the
evaluator is the arc's deliverable.

## Slice 5 — emission + instantiation sugar (after slice 4)

`go_iterate`/`go_bail`/`go_rebase`/`go_run` instantiation helpers over
the slice-1/2 lemmas; evaluator-backed segment emission; the storm
lint (syntax-level, speedbump standard). Scope trimmed to what slices
1–4 leave standing.

## The raft cross-read checkpoint

When the user's raft plan merges: STOP after the current slice,
cross-read, and re-cut slice 4+/5/6 priorities against what raft pulls.
**PARKED PENDING THIS CHECKPOINT (explicitly, so nothing is silently
lost — operator review finding 2):** key-generic `MapMem`/`MapLoops`
(the wordfreq `*W` mirror is the landed second instantiation; raft's
node-id-keyed maps are the expected puller), element-kind-generic
`SliceMem` (the i64/bool mirror families), the address-shift
simulation (rle's `n ∈ [4,8]` domain gap; any data-dependent
allocation), struct-coverage examples. Each enters the arc ONLY by
this checkpoint's re-cut or a recorded user pull.
Recorded as a decision point, not a drift opportunity.

**CHECKPOINT DISCHARGED AT KICKOFF (2026-08-16)** — the raft master
plan (`docs/2026-08-15_raft-master-plan.md`) landed on `main` before
this arc started; the cross-read verdict: **no re-cut**. Findings of
record:
1. **Raft's pre-push phase pulls no WP items.** The plan's W1–W6 are
   frontend/subject/differential/statement work — essentially no Lean
   proving before P3 (the push), which is exactly what this arc
   enables. The parked list stays parked. One prediction revised:
   raft's state maps are uint64-keyed (`map[uint64]*Progress`), so
   key-generic MapMem may matter LESS than expected at P3, while a
   VALUE-side/struct-cell generalization may matter more — reassess
   when P3 is chartered, not now.
2. **The shim-registry retirement trigger will fire in raft W1.2**
   (`slices.SortFunc` = the second shim instance; the overrides note's
   wart-retirement rule). That refactor belongs to the raft frontend
   arc, NOT this arc — recorded so neither lane grabs it by accident.
3. **Sequencing constraints, both directions:** (a) this arc is
   ownership-disjoint from raft's W1/W2/W4 lanes (proofs-only vs
   frontend/corpus) — they may run in parallel; (b) slices 1–2's
   retrofits touch gallery proof files, so they must COMPLETE before
   the re-envelope arc's re-proof wave (W3.2) starts — same files;
   (c) the evaluator's quit-at-choice design insulates it from
   W3.2's `Choices` reshape except through the mirror itself, where
   the default-build drift theorem makes the exposure visible and
   the mirror update is a known, budgeted cost of that wave.

## Slice 6 — DISCOVERABILITY close-out (LAST, covering the final
library)

1. **The Kit Guide** (`docs/kit-guide.md`): situation-indexed, not
   module-indexed — "you are at X → use Y → fixture Z" for every proof
   situation the 24 examples exhibit (entry; counted loop; two-exit
   loop; loop-local allocation → threshold frame; map count; map
   range; append/growth; recursion/call span; footprint; composition;
   readout; bounds) PLUS the evaluator and sugar the arc added. Each
   row: the kit form, its hypotheses' shape, the named fixture, the
   storm rules that apply. The campaign ledger is the source; the
   guide is the distillation — one page an agent reads FIRST.
2. **The discoverability acceptance test**: a fresh agent, given ONLY
   the Kit Guide + a new example's corpus half, produces a proof plan
   naming the right kit forms without reading any example module. Run
   as a real dry-run brief; gaps found are guide bugs, fixed before
   DONE. (The next real example built after this arc is the field
   measurement.)

## Long-cycle apparatus (the arc MAY run as a long-cycle autonomous
goal, per the CLAUDE.md practice; user decision at kickoff)

- **Judgment calls delegated** inside the boundaries below; material
  calls one-line-logged. Resolve by the recorded principles;
  honesty beats velocity beats elegance.
- **HARD BOUNDARIES**: the NON-GOALS above, plus no gate weakening, no
  re-pin laundering, no merge/push/designation — the arc ends at
  branch-complete with the audit ask POSED. The design-note gate
  (slice 4) is a USER checkpoint: the evaluator's commutation proofs
  do not start until the user has reviewed the domain design note.
- **EMERGENCY EXIT**: always permitted; park record + report on use.
- **Log**: docs/wp-arc-log/ (per-slice files + INDEX, campaign
  conventions: derivation-anchored numbers, unit-anchored cites,
  checkpoints every ≤5 units, SHAs on unit entries).
- **Lanes**: one writer per worktree (HARD); kit-file edits serialize
  (slices 1–2 are single-lane); slice 4's new modules may run beside
  slice 3's regularity pass (disjoint files); Audit/Kit.lean is
  append-only across lanes.

## DONE (the conjunction)

1. Slices 1–2: every listed family lifted, zero surviving copies,
   deltas measured, pins landed.
2. Slice 3: regularity landed (conventions + sealed APIs + pointers).
3. Slice 4: the design note user-reviewed BEFORE commutation proofs;
   the refinement theorem proven WITH its discharge witness;
   outside-the-TCB verified by walker + deletion test; the
   equivalence/drift theorem in a default build target;
   **matmul COMPLETE and gated, two-stage measured**.
4. Slice 5: shipped or explicitly trimmed with reasons.
5. Slice 6: the Kit Guide exists; the dry-run acceptance ran and its
   findings are fixed.
6. Gates green at tip (fast ci per commit; no corpus changes = the
   standing full record carries; EXISTING axiom pins byte-identical to
   04fec3c1 throughout; additions — slice-1/2 Kit pins, matmul's —
   per the Kit-pin convention).
7. Arc log current (docs/wp-arc-log/, conventions above); the
   arc-end audit ask POSED (sized to: kit correctness = the refinement
   theorem's statement/witness review, discoverability, records).
