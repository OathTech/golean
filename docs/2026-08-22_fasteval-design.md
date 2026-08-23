# FastEval — the verified fast-twin evaluator (campaign Arc 2, U4)

Route (d) of `docs/2026-08-22_campaign-arc2-witness-route.md` (§6.4,
§6.5 gate PASS, §6.7 charter). Everything here is **[AGENT]** design
under the constitution §5 latitude; §3.1 governs: FastEval is an
ACCELERATOR — untrusted method, bridged by kernel-checked refinement,
**never in any statement closure** (Sym's position exactly). No
GoCore/frontend/scripts changes anywhere in this design.

## 1. The three discoveries the design rests on (all measured/verified)

1. **The heap funnel.** Every heap access in the semantic core goes
   through THREE functions — `loadLoc`, `storeLoc` (`Ops.lean`),
   `ExecState.alloc` (`State.lean`) — and `Heap.lookup`/`Heap.set`
   are only ever applied at `.base` locations (field/index locs
   resolve inside VALUES). Verified by a precise token-closure census
   over the core (U4 survey; the closure reachable from `stepFn` that
   touches the heap is 59 defs, but the funnel is 3).
2. **The heap list is address-ascending, append-only.** `alloc` =
   fresh `.base nextAddr` + `Heap.set` (which APPENDS on a missing
   key, `State.lean:99`); the run never frees (probe C:
   `heapLen = nextAddr` at every sample). So the concrete heap at
   every reachable state is exactly
   `[(.base 0, c₀), …, (.base (na−1), c_{na−1})]` — and the
   abstraction function can be a RANGE DUMP.
3. **The trie is kernel-cheap** (§6.5 gate: 9.4 ms/op, 0.44 MB/op at
   36k entries, structural recursion only — `WellFounded.fix` does
   not usefully kernel-reduce, so every FastEval function is
   STRUCTURAL).

## 2. The two design moves that collapse the surface

**(a) One-directional refinement (the Sym-quit philosophy).** The
witness is an ∃-statement: we only ever need
> `stepFast σF c ch = .ok (c', σF', ch') → stepFn (γF σF) c ch = .ok (c', γF σF', ch')`

— never the converse. Therefore every arm/helper the run does NOT
exercise is a FAIL-CLOSED STUB (`throw (.internal "fastEval-stub: …")`)
whose sim case is VACUOUS. A stub hit during the fast run errors the
run honestly (caught compiled, pre-kernel, fail closed) — it can
delay, never lie. The mirrored surface is chosen by MEASUREMENT:
probe D (the exercised-arm census) lists exactly the configuration
shapes 711,616 + 1,382 steps hit.

**(b) The lazy γ-view for pure helpers.** Mirrored code calls every
non-heap-touching helper (the `normalizeValueForTy`/`defaultValue`/
`valueEq`/type towers — none in the heap closure) at the state
`γF σF` — the GENUINE abstraction image, passed as a term. Kernel and
elaborator whnf force structure fields ON PROJECTION ONLY: a helper
that never reads `.heap` never forces the range-dump. Consequences:
no pure-helper mirror, no heap-irrelevance lemma family, and the sim
proofs line up SYNTACTICALLY (both sides call the same helper at the
same state term).

## 3. The definitions

Module layout (`proofs/GoLeanProofs/FastEval/`, namespace
`GoLean.FastEval`; aggregator-imported; every docstring carries the
never-in-a-statement-closure line):

- **`Heap.lean`**: `HeapT` — the bench's binary trie
  (`leaf | node (v : Option HeapCell) (l r)`), canonical LSB-first
  bit keys via fuel-structural `keyBits` (fuel 64: addresses are
  machine-scale, and the WF bound keeps them < 2^64 trivially);
  `HeapT.get/set`; `WF t na := ∀ a, (t.get a).isSome ↔ a < na`
  (contiguity — probe C's measured shape, and what `alloc`
  preserves); `γH t na : Heap := (List.range na).map (fun a =>
  (.base ⟨a⟩, (t.get a).getD dummy))` — the range dump (the `getD`
  default is unreachable under WF; it keeps `γH` total).
- **`State.lean`**: `ExecStateF` (tables verbatim + `heapT` +
  `nextAddr`); `γF σF : ExecState := { types := σF.types, …,
  heap := γH σF.heapT σF.nextAddr, nextAddr := σF.nextAddr }`;
  `WFF σF := WF σF.heapT σF.nextAddr`.
- **Primitive lemmas** (the only place list-vs-trie reasoning lives):
  - `γH_lookup : WF t na → a < na → Heap.lookup (γH t na) (.base ⟨a⟩) = t.get a`
    (and the miss form for `a ≥ na`);
  - `γH_set : WF t na → a < na → γH (t.set a c) na = Heap.set (γH t na) (.base ⟨a⟩) c`;
  - `γH_alloc : WF t na → γH (t.set na c) (na+1) = γH t na ++ [(.base ⟨na⟩, c)]`
    plus `Heap.set_missing_append` (the `State.lean:99` fact) so
    `allocF` commutes with `ExecState.alloc`;
  - WF preservation for both.
- **`Ops.lean` (fast)**: `loadLocF`/`storeLocF`/`allocF` — mirrors
  with `.base` arms on the trie; `storeLocF`'s create-on-missing arm
  is a STUB (the run never writes an unallocated base; a hit would
  break γ-ordering, so it must refuse — recorded). Sims:
  `loadLocF_ok`, `storeLocF_ok`, `allocF_eq` from the primitive
  lemmas + the funnel (field/index arms recurse structurally exactly
  as the originals).
- **`Step.lean`**: the mirrored helper tower (probe-D-selected arms
  of `storeTarget`/`assigneeExpr`/`indexTargetLoc`/`applyStrictOp`/
  `applyStmtOpCore`/`applyRhsOp`/`applySyncOp`/`mapAssignValue`/
  map-iter machinery/`enterFrame`+`bindParams`+`allocDecls`/defer
  plumbing/`loadMany`+`storeMany`) and `stepFast` itself, arm by
  probe-D arm, everything else stubbed.
- **`Sim.lean`**: per-helper `_ok` lemmas + `stepFast_ok` (the
  per-step refinement) — the per-arm TEMPLATE (recorded in
  `docs/campaign-arc2-log.md` for the wave):
  1. statement: `<f>F σF a₁ … = .ok r → <f> (γF σF) a₁ … = .ok (mapγ r)`
     with `WFF σF` a hypothesis where the def touches the heap, plus
     the WF-preservation conjunct when the def can write;
  2. proof: `unfold <f>F <f>`, follow the def's own `match`/`do`
     split; heap arms rewrite by the primitive lemmas; pure-helper
     calls are syntactically shared (move (b)) so they `rfl` through;
     recursive arms use the IH (structural, same measure as the def);
     STUB arms close vacuously (`simp` on the `.error = .ok` hyp);
  3. no `sorry`, no `partial`, no `native_decide`; `#print axioms`
     pin in the same commit (kit convention).
- **`Iter.lean`**: `stepIterF` (the fuel iterator) +
  `stepIterF_ok : stepIterF n σF c ch = .ok (c', σF', ch') →
  stepFnIter n (γF σF) c ch = .ok (c', γF σF', ch')` (induction on
  `n` over `stepFast_ok` + WF threading), and `stepIterF_chain`.

## 4. The run plumbing (assembly, §6.7 item 4)

1. Reflect the post-prelude state INTO TRIE FORM:
   `twinCheckpointF% 0` (the `StateWire` reflector extended with a
   compiled list→trie conversion; emits `(heapT, na, config, ch)`).
   Kernel-check ONE γ-equality at that small state:
   `γF σF₀ = s₃` (~600 cells — cheap), where `s₃` is pinned by the
   prelude equation (`runProgramSetupM … = .ok (c₀, s₃, locs, ch₁)`,
   the measured-32 s K=0-class kernel fact).
2. Fast segments: `stepIterF nᵢ ⟨ckptFᵢ⟩ Cᵢ chᵢ = .ok (Cᵢ₊₁, ⟨ckptFᵢ₊₁⟩, chᵢ₊₁)`
   — each end EQUALS the next reflected literal (kernel-checked
   structurally), chained by `stepIterF_chain` into ONE fast-run
   equation; segment count from the mid-build gate's measured
   retention.
3. ONE application of `stepIterF_ok` transports the composed run to
   `stepFnIter 711616 s₃ c₀ ch₁ = .ok (.next .stop-shaped …)`; the
   kit (`runConfig_of_stepFnIter` + `runConfig_next_stop`) folds it
   into `runConfig`, the prelude equation completes `twinRun N [] =
   .ok r`, and the readout values discharge `CompletionWitness`.
   Fuel is re-derived by the chain arithmetic — the probe's 711,616
   is scaffolding, never trusted.

## 5. The mid-build measurement gate (§6.7 item 3 — unchanged)

After `stepFast` covers probe D's arm set: extend the reflector with
the trie emitter, reflect the 350k checkpoint in trie form, run ONE
`stepIterF` segment (~2,000 steps) compiled first (expected `.ok` —
no stub hits; a stub hit names the arm to add), then kernel-checked
under cap + timeout + RSS poll. Numeric trigger: projected full run
≤ ~60 CPU-h proceeds to assembly; a miss PAUSES against §6.6 (the
Sym convergence), never pushes through.

## 6. Risks, named

- **A stub the run needs** — caught compiled (fail closed), costs an
  extension round, never soundness.
- **Non-heap per-step kernel cost** — the §6.5 known unknown; the
  mid-build gate exists for it.
- **`γH`-forcing leaks** — a mirrored def that accidentally passes
  `γF σF` somewhere that DOES read the heap would force the dump;
  cost, not soundness (the term is the true image). The mid-build
  gate's RSS curve would expose it.
- **Sim-proof elaboration cost on big arms** (`stepFn`'s 697 lines) —
  mitigated by per-helper factoring: `stepFast_ok` cases delegate to
  helper `_ok` lemmas, so no single proof re-traverses everything.
