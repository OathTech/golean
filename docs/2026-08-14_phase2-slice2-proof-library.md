# Examples phase-2, slice 2 — proof-library wave: slice record (2026-08-14)

Status: COMPLETE (three items, one commit each). Charter: `docs/2026-08-14_examples-phase2-arc-charter.md`
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
| W2 `wp_provide_call` (the ~10-line fs_spec provision ritual as ONE tactic; evars pinned by unification) | The entry-equation dance (~15–30 lines of post-prelude state/env/cont defs + a do-syntax-mirror statement + `with_unfolding_all rfl`, repeated in 10 modules) as one macro invocation: `derive_entry_eq`. | **BUILT THIS SLICE** — the P4 item; outcome recorded in §3 below |
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

## §2 Sealed interfaces for StepKit and SliceMem (W6 adapted) — LANDED

The normative contracts are the "PUBLIC API — the sealed interface"
sections of the two module docstrings; this is the record of what
moved.

* **`SliceMem`** — three internals went `private`, each at ZERO
  external references (grepped across `proofs/` + `compat/` before the
  move): `validateSlice_ok`, `sliceIndexLoc_ok`,
  `normalizeListWith_u64` — the decomposition steps of the public
  index/store facts. One dedup as part of the seal: the module carried
  a `private mem_of_mem_set` that was a VERBATIM duplicate of the
  public `mem_set_of_mem` (the slice-1 record's privacy gotcha, now
  moot); the public lemma is hoisted to the store-fact section and the
  duplicate deleted. Everything else stays public — every remaining
  name has external consumers (e.g. `unorm_of_range` ~96 uses,
  `applyStrictOp_indexGet_slice` ~44).
* **`StepKit`** — nothing could go private: every theorem has ≥3
  external consumers (`stepFnIter_one` ~197 uses). The seal is the
  docstring contract: the API grouped and enumerated, statements (the
  conditioned-fact hypothesis shapes + the abstract-`σ` E-form) are
  the dependable surface, proof bodies are not, additions go through
  §12.
* Both contracts state the Lean-vs-Rocq honesty note: `private` hides
  names without sealing definitional transparency (no `Module Type`
  opaque ascription here), so the seal is name-level + review
  discipline; the statement layer keeps its own kernel-checked gate
  (statement-TCB closure), and §12b bans kit names from headline
  statements regardless.
* NO functional changes: statements untouched, axiom pins byte
  identical (in-build Audit gate green), `scripts/ci` PASS.

## §3 P4 — the entry-equation macro: SHIPPED (`derive_entry_eq`)

The twice-deferred "real elaborator project", attempted properly under
the strict guard (>5 stuck iterations → stop and record) now that it
had 10 real consumers (every harness entry equation is the same
do-syntax-mirror + `with_unfolding_all rfl` dance). It did NOT need
the guard: a working prototype on the first consumer (fib) took 4
iterations; both fixture retrofits landed on the next two.

**The deliverable**: `proofs/GoLeanProofs/EntryEq.lean`, a command
elab modeled on brick-wp's W2 `wp_provide_call` (a multi-step ritual
as one invocation):

```
derive_entry_eq gcdh_entry_eq gcdLowered gcdHarnessFunc hSeedI hc₀
```

derives and emits, in the caller's namespace: the post-prelude
`ExecState` def (argument cells at `0…p−1` receiving already-
normalized values, result cells at their `defaultValue`s after them,
`nextAddr` counted), the start `Config` def (body under the entry
barrier frame, one scope in reverse-declaration order), and the entry
equation at fully symbolic arguments/fuel/choices, proved by
`with_unfolding_all rfl`. The layout is COMPUTED from the `Func` by
evaluating the same executable pieces the interpreter's prelude uses
(`defaultValue`; the `bindParams`/`allocDecls`/`pinResultLocs` order
mirrored by construction) — no probe run needed for the entry layer
anymore. The state/cont names are caller-chosen — the module's own —
so every downstream segment lemma keeps its spelling: that is what
made the retrofits zero-churn.

**Untrusted method, and the `#eval`-before-`decide` guard mechanized**:
the macro only GENERATES declarations the elaborator/kernel then check
(no gate integration, no statement-layer contact — the entry equation
is §11 glue, and §12b keeps every emitted name out of headline
closures). Because a FALSE entry equation handed to
`with_unfolding_all rfl` is the recorded 60 GB failure mode, the macro
EVALUATES both sides of the derived equation at a concrete probe point
(all args 1, fuel 100000, empty stream) with the compiler before
emitting, and refuses on mismatch — a mis-derived layout fails in
milliseconds with a message, never in the kernel. Scope is fail-closed
and explicit: ≥1 scalar-integer parameters, defaults quoted for
scalars / arrays-of-scalars / nil slices+maps; anything else is a hard
error naming the piece.

**Fixture consumers retrofitted in the same commit** (per §12a — two
prove it; mass-retrofit deliberately NOT done):

| module | before | after | consumer churn |
|---|---|---|---|
| `Examples/Fib.lean` (`fibHSeed`/`fibHC₀`/`fibH_entry_eq`) | 30 lines hand-written | 9 (comment + invocation + import) | ZERO — `fib_total`'s `rw [fibH_entry_eq, …]` unchanged |
| `Examples/Gcd.lean` (`hEnv₀`+`hSeedI`/`hc₀`/`gcdh_entry_eq`) | 37 lines hand-written | 10 | ZERO — `gcd_ok`'s rw chain unchanged |

Net `−44` source lines on two consumers (git: +20/−64), and the
derived layer is no longer transcribed knowledge: the binder-type
change (the emitted statement binds parameters at `Int`; the old
hand-written forms bound `Nat` with casts in the argument array) is
absorbed by unification/coercion at the existing `rw` sites, which is
why no consumer line moved. Costs (proof-costs / lake timings): Gcd
module 0.9 → 1.5 s, Fib 5.0 → 5.6 s — the ~0.6 s is the macro's two
compiler evaluations (layout + validity probe) per invocation; peaks
unchanged (Fib's pre-existing 1.9 GiB class is its segment layer, not
the entry). Axiom pins byte-identical (Audit `#guard_msgs` green);
`lean_verify`-equivalent check on the prototype: emitted theorem's
axioms `[propext, Quot.sound]`.

**The mechanical follow-ups, recorded not done** (8 remaining entry
equations): the five other FLAT-state modules (`mmh_entry_eq`,
`wcH_entry_eq`, `iharness_entry_eq`, `harness_entry_eq` (binsearch),
`revH_entry_eq`) retrofit exactly like fib/gcd. The three
PROGRAM-generic modules (`Reverse/HarnessV`, `MinMax/HarnessR`,
`WordCount/HarnessR`) spell their entry state compositionally
(`rSt rProg (rHeap0 …) 5`) and instantiate σ-generic runs lemmas at
that spelling, so a retrofit there either states the runs
instantiation at the macro's flat emitted def or adds one
`show`-defeq bridge line at the single consumer — mechanical, but not
zero-churn; do it when those modules are next open anyway.

**Where the elaborator pushed back** (recorded for the next macro):
syntax atoms cannot contain spaces/`:=` (the planned
`(state := foo)` named-argument surface was dropped for plain
positional idents); binder-position splices need an exact
`TSyntaxArray [\`ident, \`Lean.Parser.Term.hole]` (an `Array Ident`
does not coerce — wrap explicitly); `open Meta` makes `Config` and
`mkConst` ambiguous inside quotations (qualify `Machine.Config`);
unsafe evaluation goes behind `@[implemented_by]` opaque wrappers.
None of these is a wall; total 6 iterations end to end.

## §4 P5 / P8: closed for now (recorded per the slice brief)

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
