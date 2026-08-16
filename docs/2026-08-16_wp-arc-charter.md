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

## Slice 3 — DISCOVERABILITY (the user's second aim; its own slice)

The library is only leverage if the agent on proof N+1 FINDS it.
Deliverables:
1. **The Kit Guide** (`docs/kit-guide.md`): situation-indexed, not
   module-indexed — "you are at X → use Y → fixture Z" for every proof
   situation the 24 examples exhibit (entry; counted loop; two-exit
   loop; loop-local allocation → threshold frame; map count; map
   range; append/growth; recursion/call span; footprint; composition;
   readout; bounds). Each row: the kit form, its hypotheses' shape,
   the named fixture to copy from, the storm rules that apply. The
   campaign ledger (g1.md) is the source; the guide is the
   distillation — one page an agent reads FIRST.
2. **Naming + module regularity**: conventions normalized across
   StepKit/SliceMem/MapMem/MapLoops/FuelMeasure/StringMem/Frame;
   sealed-API sections consistent; every kit module's docstring points
   at its guide section and vice versa.
3. **The discoverability acceptance test**: a fresh agent, given ONLY
   the Kit Guide + a new example's corpus half, produces a proof plan
   naming the right kit forms without reading any example module.
   Run it as a real dry-run brief; the gaps it reveals are guide bugs
   to fix. (The next real example built after this arc is the field
   measurement.)

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
`stepFn' @ GoValue = stepFn` (arm-by-arm, rfl-shaped, the drift alarm);
the symbolic instance = the evaluator; per-operation commutation
lemmas; and THE REFINEMENT THEOREM:

    symEvalWindow S = some S'  →  ∀ ρ, stepFnIter n (γ_ρ S) = γ_ρ S'

— the ∀ρ universality IS the full-precision claim (the value-domain
frame rule: the machine is parametric in values it never inspects; the
third member of the γ-square family after the address-frame theorem).
Quit-minimality is DOCUMENTED, not proven (an over-eager quit costs
automation, never soundness). **Outside-the-TCB is verified, not
asserted**: no `Sym*` constant in any headline statement closure (the
existing walker), and the deletion test extended — removing the whole
symbolic layer leaves every statement elaborating.

**Acceptance: matmul.** `matmul_ok` landed COMPLETE from its snapshot
(`refs/snapshots/gc-proofs-a/matmul-machine-layer`) with its segment
layer produced via the evaluator (emitted or evaluator-transported),
gated, pinned — the GAP-RFL-COST class closed on the artifact that
discovered it. Fallback if the evaluator runs long: probe-driven
emission (`derive_seg` mode (a)) is the recorded interim, but the
evaluator is the arc's deliverable.

## Slice 5 — emission + instantiation sugar (after slice 4)

`go_iterate`/`go_bail`/`go_rebase`/`go_run` instantiation helpers over
the slice-1/2 lemmas; evaluator-backed segment emission; the storm
lint (syntax-level, speedbump standard). Scope trimmed to what slices
1–4 leave standing.

## The raft cross-read checkpoint

When the user's raft plan merges: STOP after the current slice,
cross-read, and re-cut slice 4+/5 priorities against what raft pulls
(expected: call-span/compositional spec-overrides, key-generic
MapMem, struct coverage, possibly the address-shift simulation).
Recorded as a decision point, not a drift opportunity.

## DONE (the conjunction)

1. Slices 1–2: every listed family lifted, zero surviving copies,
   deltas measured, pins landed.
2. Slice 3: the Kit Guide exists; the dry-run acceptance ran and its
   findings are fixed.
3. Slice 4: the refinement theorem proven; outside-the-TCB verified by
   walker + deletion test; **matmul COMPLETE and gated**.
4. Slice 5: shipped or explicitly trimmed with reasons.
5. Gates green at tip (fast ci per commit; no corpus changes = the
   standing full record carries; axiom pins byte-identical to
   04fec3c1 throughout, matmul's new pins excepted).
6. Arc log current (docs/wp-arc-log.md, campaign conventions); the
   arc-end audit ask POSED (sized to: kit correctness = the
   refinement theorem's review, discoverability, records).
