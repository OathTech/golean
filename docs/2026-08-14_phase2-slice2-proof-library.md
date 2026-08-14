# Examples phase-2, slice 2 — proof-library wave: slice record (2026-08-14)

Status: IN PROGRESS. Charter: `docs/2026-08-14_examples-phase2-arc-charter.md`
§"Slice 2" (brick-wp-informed, TRIMMED to consumer-backed items). Three
items, one commit each: (1) this brick-wp W1–W7 mapping, (2) sealed
interfaces for `StepKit`/`SliceMem` (the W6 convention adapted to
Lean 4), (3) the P4 entry-equation macro, attempted properly. Standing
rules: the active-abstraction loop (form note §12) — this slice is the
reference-transfer the user asked for ("perhaps worth reviewing for
inspiration"), filtered through §12's consumer rule, which is NOT
waived here (brick-wp's arc waived its second-occurrence rule by its
user's direction; ours stands, which is why this slice is trimmed).

## §1 The brick-wp W1–W7 mapping (read 2026-08-14, `deps/brick-wp`
@ `2420249`, READ-ONLY)

Source: the ergonomics arc `docs/2026-08-13_ergonomics_arc_charter.md`
in that repo (all waves done, commits `38c3f40`…`968018c`), its
`docs/sealed-interface-kit.md`, `theories/WpTactics.v`,
`theories/CallReady.v`, `theories/GhostModules.v`, `theories/NdUnits.v`.
Context for the transfer: brick-wp is an Iris/Rocq WP stack over C++
where every example is a WP walk; our shipped examples use the DIRECT
segment method (conditioned `stepFn` facts + `with_unfolding_all rfl`
segments + fuel measures) with the Iris WP lane kept separate
(`Laws/`, `Ghost.lean`). Analogues therefore land in the direct-method
kit, not necessarily in a tactic.

| wave | what brick-wp built | our analogue | status |
|---|---|---|---|
| W1 call-layer bridges (`wp_fptr_of_spec`, `_fupd`: module lemma + linkage ⟹ the call-site goal in one lemma) | The call boundary in one conditioned step: `StepKit.stepFn_call_enter` (frame entry keyed on its `enterFrame` fact — 3 consumers: EmptyRun, Reverse/HarnessV, WordCount/HarnessR). WP lane: `wp_call`'s pure `findFunctionIn?` premise over the pinned program (`Ghost.lean` `GoCoreGS.prog`; `docs/2026-07-20_call-law-design.md`) is the same "table bridge" move — turn linkage into a discharged pure fact. | **EXISTS** (both lanes) |
| W2 `wp_provide_call` (the ~10-line fs_spec provision ritual as ONE tactic; evars pinned by unification) | The entry-equation dance (~15–30 lines of post-prelude state/env/cont defs + a do-syntax-mirror statement + `with_unfolding_all rfl`, repeated in 10 modules) as one macro invocation: `derive_entry_eq`. | **BUILT THIS SLICE** — the P4 item; outcome recorded in §4 below |
| W3 call-readiness combinators (`call_ready1/2/3` over any spec; covariance for nesting a later call's readiness in an earlier take-away) | The entry-glue layer already exists as named lemmas with many consumers: `stepFnIter_chain`, `runConfig_of_stepFnIter`, `runConfig_next_stop`, and `harness_readout_of_total` (the "client walks away with the returned value" shape — the D1 readout twins, 10 consumers). The genuinely W3-specific part — CHAINED client calls with readiness nested in Φ — has ZERO consumers here: every shipped harness makes exactly one subject call, and the direct method composes segments by fuel arithmetic, not by continuation-passing readiness. | **EXISTS** (entry glue); chaining shape **not applicable** — no consumer, §12 forbids the speculative lift |
| W4 generic ghost modules (Excl registry + capacity credits, `registryG`/`creditsG`) | None. The ghost ladder is pinned at rung 0 by ruling (form note §11-era rulings; harness-style scoping §0/§10): shipped statements carry NO ghost state. Our `Ghost.lean` `GoCoreGS` is WP-lane state interpretation, not module-state registries. Zero consumers. | **Not applicable at rung 0** — reopen when the ghost rung-1 annotation arc lands (it is designed, not built) |
| W5 nd-monad unit shapes (Mret/Muse spec lemmas; tactic learns to split ⌜⌝∗⌜⌝ pures) | Our nondeterminism is the `Choices` stream, not a monad the proof engages: choice-free segments are stated at symbolic `ch` and thread it unchanged (every raw segment in every module); the one choice-adjacent step shape is `StepKit.stepFn_snapshot` (map-range snapshot). Nothing plays the unit-shape role because `stepFn` is deterministic GIVEN `ch` — the collapse brick-wp needed does not arise. | **EXISTS** (structurally different; nothing owed) |
| W6 sealed-interface kit (`Module Type` + opaque ascription; functor clients; telescope rule; "specs transparent, state sealed") | Sealed public APIs for the two kit modules consumers actually depend on, `StepKit` and `SliceMem`: a PUBLIC-API contract section in each module docstring (what consumers may name, what is internal), internals `private` where reference counts allow. Lean 4 difference recorded honestly: Rocq's opaque ascription is KERNEL-enforced; Lean's `private` hides names without sealing definitional transparency, so the seal here is name-level + review discipline, and the statement layer has its own frozen closure (§11) which no kit name may enter (§12b). | **BUILT THIS SLICE** — item 2, §2 below |
| W7 rollback (the example re-based on W1–W6; measured deltas; scenario statements unchanged) | The §12 active-abstraction loop IS this, as a standing per-lift rule rather than an arc phase: every promotion retrofits ≥2 consumers in the same commit (fixture witnesses), statements/pins unchanged, deltas measured. Slice 1 executed it four times (`stepFn_call_enter`, `stepFn_makeSlice_u64_step`, `storeTarget_arrayLocal_u64`, `normalizeValueForTy_arr_u64`). | **EXISTS** (as standing discipline) |

Transfer verdict: the two waves with live pull here are W2 (the
ritual-to-one-invocation move — our P4) and W6 (the sealed-API
convention — our item 2). W1/W3/W5/W7's roles are already filled by
direct-method equivalents; W4 waits on the ghost rung the campaign has
not taken. The deeper pattern brick-wp validates is the one §12
already encodes: promote from worked examples, retrofit in the same
commit, measure — their charter waived the two-consumer rule for one
arc and paid for it with synthetic tests; we keep the rule and pay by
deferring W3/W4-shaped machinery until demand exists.

## §2 Sealed interfaces for StepKit and SliceMem (W6 adapted) — see
the commit for the diff

Recorded in this file after landing; see the module docstrings for the
normative contracts.

## §3 P5 / P8: closed for now (recorded per the slice brief)

* **P5 — the setup-loop induction schema** (scale-out record §8, row
  P5: one parameterized induction over the family function + backing
  addresses, predicted ~250–350 lines, consumers reverse/minmax/
  binsearch/isort/wordcount) and **P8 — frame-rebase-into-garbage at a
  threshold** (row P8: retire-prefix-into-frame lemma family,
  isort ×3 + binsearch's variant) remain OPEN LEDGER CANDIDATES with
  **no current demand**: the phase-2 swap layers went
  PLACEMENT-CONCRETE by measured decision (slice-1 record, swap 1:
  address-generic segments cannot close by `rfl` when nearly every
  step touches a cell — ~10× the source for seconds-cheap layers whose
  layouts differ anyway), so no new instantiation of either shape
  materialized this arc, and the copy-loop schema was separately
  closed as an empty-shareable-part non-lift (slice-1 ledger).
  CLOSED-FOR-NOW, reopenable by the campaign the moment a new example
  family re-creates the repeated-instantiation grind these rows
  predicted (that grind, not taste, is the reopen signal — §12d).
