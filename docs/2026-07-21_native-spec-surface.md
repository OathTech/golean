# The native spec surface: human-readable theorems over interpreter states, Iris strictly internal

**Date: 2026-07-21 (arc `exit-infra`).** Design of record for how specifications
enter and leave the proof stack. Written after the existential-address episode
(below) surfaced an *interface* gap, not a one-theorem gap. This note pins the
interface so we never hack a property through the boundary again.

## 1. The motivating failure

`golden_interp_computes_two` proves: every terminating run's final heap
contains **∃ a**, a cell at `a` holding `int 2`. The property we *meant* is
"**the result cell** holds 2". The final heap also contains `x`'s cell and
`$res0`'s cell, both holding 2 — the statement cannot distinguish "returns 2"
from "computed 2 somewhere"; a buggy program returning 7 but touching 2 in a
temporary would satisfy it.

The failure was NOT in the separation-logic layer. The Iris walk is
location-precise throughout: `wp_frame_return_int` — the SL assignment rule
for the result store — establishes `ta ↦ 2` for the *specific* caller target
cell. The precision was dropped at the adequacy readout, because (a) the
target cell was allocated *inside* the run (behind the `∀ ra` fresh-allocation
quantifier, so the WP proof cannot name it), and (b) `adequate`'s φ is a pure
predicate over the final state fixed before the run, with no way to say "the
location this run bound `r` to".

**Principle (user-pinned, recorded): a theorem's value is exactly its
statement.** "The information exists elsewhere in the development" is worth
nothing to a consumer of the theorem and is never an acceptable defense of
weak scope. This is the statement-level twin of the non-vacuity gate.

## 2. The aim

> Use Iris as reasoning infrastructure without the Iris nonsense escaping and
> making the specifications impossible to understand by humans. Prove theorems
> in a natural separation-logic style over interpreter states, discharge them
> via Iris internally, and end with natural postconditions at the Go
> interpreter level. Ride the same technique all the way to full proofs of
> complex Go programs (the raft target).

Two sharpenings, adopted after discussion:

**(a) The readability requirement is a *vocabulary criterion*, checkable per
statement.** Surface statements may mention only interpreter-level objects:
`ExecState`, concrete heap fragments, Go values, program syntax, `execStmt`
runs. `ℓ ↦ v` and `P ∗ Q` **over concrete heaplets** pass — they are
first-order definable and are the honest human vocabulary for disjoint heap
ownership. What must never appear in a surface statement: `IProp`, `WP`,
masks/`CoPset`, later credits `£`, fancy updates `|==>`/`|={E}=>`, ghost
names, resource algebras, step-indices. That is the precise line "no Iris in
statements" (docs/2026-07-20_end-state-theorem.md) was groping toward.

**(b) The native layer is a *readout format*, not a logic.** We do NOT
re-prove frame/bind/composition rules natively — composition is what Iris is
for, and a native proof calculus would be a second, worse logic to maintain.
Component specs live and compose *inside* Iris (as WP lemmas); finished
results are *exported* through a once-proven transfer theorem. Corollary:
there are exactly two boundary crossings (precondition in, postcondition
out), and they are proven once, generically, by induction on the assertion
language — never per-program.

**(c) Two surface registers, one internal proof.** Component-level exports
(reusable function specs) are SL-shaped: `{x ↦ m} inc(&x) {x ↦ norm(m+lit)}`.
Whole-system theorems (the Verdi-style results) are typically *plainer* than
SL — pure first-order predicates over designated observables ("the output
cell holds 2", "all committed logs agree"), no `∗`, because disjointness of a
closed system's internals is not part of what the human wants asserted.
Verdi's own results are plain predicates over traces. Both registers are
instances of the same surface (a pure postcondition is the `⌜φ⌝` case of the
assertion language); the system register is the degenerate-but-preferred form
for end-to-end theorems.

## 3. The architecture: three layers, two crossings

```
  S  (surface)    GoTriple P prog Q        — native SL over interpreter runs
                  φ-form corollaries       — plain predicates over σf
        │  reflection (P in)         ▲  extraction (Q out)
        ▼                            │        [Layer B: proven ONCE]
  I  (internal)   Iris: WP walks, framing, composition, adequacy
                  — the ONLY layer where Iris vocabulary is legal
```

### Layer S — the surface language

- **Heaplets**: `Heaplet := Nat ⇀ HeapCell` (finite partial maps, matching
  `heapToMap`).
- **Assertions**: a small *deep-embedded* language `HProp`:
  `emp | pure (φ : Prop) | pointsTo (ℓ : Nat) (c : HeapCell) | sep P Q |
  ex (α) (f : α → HProp)` — with satisfaction `sat : Heaplet → HProp → Prop`
  giving the standard heaplet semantics (`sep` = disjoint split). Deep
  embedding is deliberate: both boundary crossings are proven by induction on
  `HProp` syntax, once.
- **The triple** (v1 sketch as first staged; **superseded 2026-07-21 by
  the shipped frame-closed form** — `GoTriple` in
  `proofs/GoLeanProofs/Surface.lean` quantifies over a frame `F` via
  `InitialSplit` and concludes net frame preservation; see
  `docs/2026-07-21_spec-space.md` §6 and the statement-shape trio. The
  sketch below is kept for the design history):

  ```
  GoTriple (P : HProp) (env₀) (prog : Stmt) (Q : HProp) : Prop :=
    ∀ σ₀, sat-exactly σ₀.heap P → HeapWf σ₀ → (program side conditions) →
    ∀ fuel σf ch', execStmt fuel σ₀ env₀ prog = .ok (.normal σf, ch') →
      ∃ h ⊆ heapToMap σf.heap, sat h Q
  ```

  Postcondition is **intuitionistic** (`Q` holds of a *sub*-heaplet): final
  heaps legitimately contain dead-frame cells (frames pop the env, not the
  heap), and `Q` describes the observables, framing the garbage away. This is
  the standard affine reading and matches Iris's affinity.
- **Progress** is a separate conjunct/companion (the `adequate .NotStuck`
  side), not smuggled into the triple.
- **System-register corollaries**: when `Q`'s footprint is a designated cell,
  the triple specializes to a plain predicate (`loadLoc σf (.base ⟨0⟩) =
  .ok (.int 2 .int)`) — the preferred form for end-to-end theorems.

### Layer B — the boundary (built once, the actual new work)

- **Embedding** `⟦·⟧ : HProp → IProp`, structural: `pointsTo ℓ c ↦ ℓ ↦ c`,
  `sep ↦ ∗`, `pure ↦ ⌜·⌝`, `ex ↦ ∃`.
- **Reflection (precondition in)**: extend the adequacy entry to the standard
  `heap_adequacy` shape — allocate the ghost heap *empty* and
  `genHeap_alloc_big` the initial heap, yielding `genHeapInterp σ₀ ∗
  [∗ map] ℓ ↦ c ∈ heapToMap σ₀.heap, ℓ ↦ c`; a once-proven lemma turns
  `sat`-footprint + the big-op into `⟦P⟧` (∗ frame cells). **Checked
  2026-07-21: iris-lean ships `genHeap_init_names` and `genHeap_alloc_big`
  (`gen_heap_alloc_big`)** — this crossing rides the standard kit; our
  `go_heap_adequacy` proof already hand-allocates the auth, so the `_own`
  variant is a contained rework of its ghost-allocation prelude.
- **Extraction (postcondition out)**: `genHeapInterp (heapToMap σf.heap) ∗
  ⟦Q⟧ ⊢ ⌜∃ h ⊆ heapToMap σf.heap, sat h Q⌝`, by induction on `Q`:
  each `↦` extracts a lookup fact by auth/frag agreement
  (`pointsTo_loadLoc`'s generalization); for `sep`, *validity* of combining
  full-ownership fragments yields genuine disjointness of the sub-heaplets —
  so the native `∗` is honestly reconstructed, not approximated.
- The existing `go_heap_adequacy` (Ψ/φ form) becomes an internal lemma the
  generic exit theorem consumes; per-program `Hext` entailments disappear.

### Layer I — internal (exists today)

WP laws (the SL assignment rule family: `wp_assign`, `wp_store_via_ptr`,
`wp_frame_return*`; allocation: `wp_init_int`, `wp_call_*`; pure control),
the walks, `wp_strong_adequacy_gen`. Nothing changes here; the golden walk
(`wp_incViaCallLowered_ret2`) is already ∀-general over the target cell and
consumes the reflected `↦` unchanged.

### Per-program obligations (the anti-hack invariant)

For any new verified program, the *only* per-program work is:
1. the correspondence side conditions (fragment-shape checks — mechanical);
2. the WP walk (the real proof);
3. instantiating the generic exit theorem with concrete `P`/`Q`.

**If a property ever seems to need a new adequacy variant, a bespoke φ
construction, or an env/address side-channel — that is a design smell: stop
and extend the surface language instead, in Layer B, once.** This invariant
is what "ride the technique to complex programs" cashes out to.

## 4. Decisions of record

- **D1 — Surface vocabulary criterion** as in §2(a). Enforced by eyeball at
  review time now; a lint (grep surface files for `IProp`/`WP`/`£`) is cheap
  and worth adding to `scripts/ci` when the surface module lands.
- **D2 — Readout format, not logic** (§2(b)). No native frame rule, ever.
- **D3 — Intuitionistic postconditions** (sub-heaplet `sat`). Exact-heap
  postconditions are not a goal; dead-frame cells are expected.
- **D4 — v1 preconditions are exact-footprint** (`P` describes `σ₀.heap`
  exactly). Right for closed drivers; the `P ∗ frame` initial-state
  generalization is a later, easy widening (big-op splits).
- **D5 — Observables are named by driver convention**: the driver runs
  against a seeded initial state whose designated cells `P` names (e.g.
  output cell at `⟨0⟩`, env binding `r ↦ ⟨0⟩`), mirroring what the
  differential runner does (`runNamedFunction` writes results into caller
  cells). v1 assertions are heap-only; a `var x ⇓ v` sugar layer (env
  resolution at readout) is a tracked widening — note the final config is
  env-erased (`withLocals []`), so var-level readout must thread the driver
  env, another reason heap-cells-first.
- **D6 — Partial correctness + NotStuck; termination out of scope of this
  surface.** Step-indexed Iris does not give total correctness; tier-2 raft
  properties (convergence/liveness) will need their own machinery decision
  (F5's explicit stretch) — flagged, not built.
- **D7 — Negative instances live at the surface**: with pinned observables,
  refutation twins are corollaries (`loadLoc = .ok 2` refutes
  `loadLoc = .ok 3` for every terminating run) — the widening loop's
  should-be-unprovable instances get *stated* natively too.
- **D8 — The `*_computes` theorems are superseded, honestly**: the
  existential-address forms remain true and stay (they are consumed by
  nothing), but the ledger/TODO language must say "computed-somewhere" for
  them; the *lowering target* is claimed only by the pinned-observable
  triple.

## 5. Staging (widening-loop form)

**Step 0 — intended proofs (write first):**
- `GoTriple (r ↦ 0-cell) [[("r",⟨0⟩)]] (r = incViaCall()) (r ↦ 2-cell)` over
  the golden lowering, plus its system-register corollary
  `loadLoc σf (.base ⟨0⟩) = .ok (.int 2 .int)`;
- negative twin: the same with 3, refuted;
- non-vacuity witness: the triple instantiated on a concrete satisfying run.

**Then:** (1) `HProp` + `sat` + `⟦·⟧` (new surface module, Iris-free
statements); (2) `go_heap_adequacy_own` — initial-heap handover via
`genHeap_alloc_big`; (3) reflection + extraction lemmas by `HProp`
induction; (4) the generic exit theorem (`goTriple_of_wp`); (5) seeded
golden driver + its correspondence witness (nonempty-initial-heap `StInv`);
(6) instantiate — the golden walk is reused as-is; (7) ledger/TODO honesty
pass per D8.

Scale: (2)–(4) are the substance; (1) and (5)–(7) are mechanical. One arc.

## 6. The raft connection

This surface is the language F5's step-0 specs get written in: component
triples for step/handler functions (SL register, composed in Iris), system
theorems as plain predicates over designated state cells (election safety,
log matching, commit agreement as `sat`-facts over the state machine's
observable cells). The seeded-observable driver convention generalizes to
"the harness owns the observable cells; the system under proof runs against
them" — which is also how the differential runner already frames execution.
Multi-thread readout (thread-pool adequacy, per-thread postconditions) is
the F4 gate's concern and does not change this interface's shape.
