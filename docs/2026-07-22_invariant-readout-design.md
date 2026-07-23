# The invariant readout: design note (2026-07-22)

Design-of-record for the **invariant-readout arc** (queued in `TODO.md`; the
"raft-shaped exit door" from the spec-surface arc). Written before code, per
the discuss-first rule. Companion to `docs/2026-07-21_native-spec-surface.md`
(the surface architecture) and `docs/2026-07-21_spec-space.md` (the spec
ladder). Fault-model companion: `docs/2026-07-22_fault-model.md`.

## 1. What the judgment is — and what tradition it belongs to

The target is a new surface judgment, roughly:

```
GoInvariant funcs env₀ P I :=
  ∀ initial splits of P (as in InitialSplit),
    ∀ (c', σ') with Steps … (c', σ'),
      ∃ hI : Heaplet, hI.sub (heapletOf σ'.heap) ∧ sat hI I
```

i.e. **every relation-reachable configuration** — mid-call, mid-expression,
wherever control is — has a sub-heaplet satisfying `I`.

**Naming honesty (decision):** this is *not* a separation-logic notion, and
the surface must not present it as a triple variant or "SL with a standing
invariant."

- Reynolds/O'Hearn sequential SL has **no such judgment**: triples speak only
  of terminal states; even "framed state is untouched throughout" is a fact of
  the soundness proof's semantics, not a sentence of the logic. Loop
  invariants are program-point assertions, a different thing.
- Per-state meaning first appears in O'Hearn's CSL (resource invariants, held
  except inside critical regions — per-state because concurrent interference
  makes "between steps" observable; Brookes' soundness theorem is where the
  per-state split lives). Iris generalizes these to atomic-step invariants
  (`inv N I`, masks).
- The judgment above natively belongs to the **invariance tradition**:
  Floyd/Ashcroft, Owicki-Gries global invariants, TLA (`Inv ∧ [Next] ⇒ Inv′`),
  and **Verdi** — safety as invariance of a transition system. `Rel.Step` is
  the transition system; `GoInvariant` is invariance over it. Our north star
  ("the Verdi results, but on real code") is literally this shape.

Separation logic contributes exactly two things: (a) the **assertion
language** for `I` (footprint-local; sub-heap satisfaction = `I ∗ true` —
this quantifier is load-bearing, see §3); (b) the **internal proof
mechanism** (§2). Docstrings say so.

## 2. The mechanism: `wp_invariance` + persistence as transport

iris-lean ships the exact exporter: `wp_invariance_gen` /`wp_invariance`
(`.lake/packages/iris/Iris/Iris/ProgramLogic/Adequacy.lean:317-352`, a direct
port of Coq Iris's theorem). Shape:

- `Hsteps : ([e1], σ1) -·->ₜₚ* (t2, σ2)` — **any** reachable configuration,
  not a terminal one;
- the WP premise has **trivial postcondition** `True` (the triple's `Q` plays
  no role in invariance);
- the conclusion `φ` is produced by a wand that receives **only**
  `stateInterp σ2` and may leave invariants open
  (`∃ E, |={⊤,E}=> ⌜φ⌝`).

Why Iris invariants specifically (and not triple-carried assertions): the
extraction wand receives *only* the state interpretation. Owned resources —
the `↦` fragments held inside the WP — never reach it. The one kind of
resource that crosses is a **persistent** one, and the invariant token
`inv N I` is persistent. So the proof pattern is:

1. allocate `inv N I` from `P`'s resources at the start (`inv_alloc`,
   `Iris/Instances/Lib/Invariants.lean`);
2. the WP proof opens/closes the invariant around each atomic step that
   touches `I`'s footprint (`inv_acc`) — this discipline is the *price* that
   keeps the token meaningful;
3. the extraction wand captures the persistent token, and at any reachable
   `σ2` opens it against the state-interp auth to conclude the pure heap
   fact. Opening yields `▷I`; our `I`s are first-order heap facts, hence
   timeless, so the later strips.

**Key observation (recorded so nobody re-derives it):** in a *sequential*
setting, Iris invariants buy nothing internally — one could carry `I`
through triples by hand. Their entire payoff here is at the adequacy
boundary: **persistence is what lets a fact survive to the readout at
arbitrary reachable states.** They are a transport mechanism for invariance
properties, dressed in CSL clothing. They additionally become the real CSL
thing when goroutines arrive — a happy alignment, not the current
motivation.

Layer discipline as before: `inv`/namespaces/masks/`▷` are **Layer I only**;
the surface sentence is first-order over the interpreter. The vocabulary
criterion (D1) applies unchanged.

## 3. What `I` represents: the three-way heap partition

At any moment the heap splits:

1. **`I`'s footprint** — cells the program *may mutate*, but only under the
   per-step discipline: every atomic step maps an `I`-satisfying state to an
   `I`-satisfying state. (An invariant is NOT a frame — frames forbid
   mutation entirely; invariants license it. The golden example's cell 0 is
   *written*, 0 → 2, and stays inside `I`.)
2. **Working state** — everything else the program owns: scratch, half-built
   structures, callee machinery. Mutated arbitrarily; *invisible* to the
   invariance statement at intermediate states (this is what the sub-heap
   quantifier `∃ hI ⊆ heap` buys); described by the triple only at the end.
3. **The frame** — untouched, per frame closure.

So `I` is the **protocol-governed portion** of the state — the part whose
intermediate values are promised to an observer — same role as a lock
invariant. For raft: currentTerm/votedFor/log with well-formedness +
term-monotonicity (+ eventually the abstract-view safety facts); working
state = message buffers, iteration state, temporaries.

"Not the whole thing" is **necessary**, not just permitted: if `I` covered
everything the program mutates, per-step preservation would force `I` down
to the reachability predicate itself — true and useless. Choosing the
boundary and strength is the classical inductive-invariant problem (same as
TLA/Verdi): strong enough to imply the safety property, loose enough that
every single step preserves it.

**Granularity pressure and the ghost-state out (deferred):** if the protocol
state needs a multi-step update (append entry, then bump index), raw
physical `I` is broken in between. Outs: weaken `I` (cheap, coarsens the
statement) or move the sharp invariant to an **abstract state** tied to
physical cells by ghost state, updating the abstract view at one chosen
physical step (linearization-point idiom) — the intermediate physical states
map to the same abstract state. Ghost machinery is queued AFTER this arc;
the v1 golden invariant is chosen to need neither (one atomic write).

## 4. Enforcement is proof-theoretic (not language isolation)

Recorded after discussion (2026-07-22): ownership is a **bookkeeping fiction
of the proof system** over a fully global memory — Go goroutines share one
heap and can physically dereference any address; `Rel` must say so. What
protects the working state is that another thread's *proof* cannot refer to
it: the WP load/store rules demand a points-to, obtainable only from one's
own precondition or an invariant opening. A thread touching un-owned state
faces an undischargeable obligation — **racy-on-the-junk programs are
unverifiable, not impossible.** If a second thread legitimately needs the
state, it must move into a shared invariant — changing the spec, visibly.
No language isolation guarantee is assumed anywhere (this is original-SL
heritage: Reynolds built it for unmanaged C heaps). Soundness/adequacy is
what cashes the fiction out over the interleaved semantics.

Consequence for F4 (see also the fault-model note): CSL-style verification
yields data-race freedom, and Go's memory model promises SC behavior for
DRF programs — so an interleaving `Rel` is honest for exactly the programs
the logic can verify. Weak memory is owed only if we ever target
deliberately racy code (we don't plan to). F4 must pin this scope
explicitly.

## 5. Scope decision: readouts, not interfaces (composition stays internal)

**Our surface statements are adequacy READOUTS of reasoning that lives in
Iris; they are not composition interfaces.** Two independently exported
`GoInvariant` theorems about two libraries are closed first-order facts
about whole-program reachability; they do not link into a fact about a
program using both libraries — the quantifiers are already discharged.

- Composition happens at **Layer I**, where it works as designed: disjoint
  namespaces, world satisfaction carrying all invariants, and (when needed)
  abstract predicates (Parkinson-Bierman style, `isLock γ l R`-idiom)
  packaging a library's invariant token behind an exported persistent
  predicate. Classical anchor for hiding: O'Hearn's resource-invariant
  hiding / hypothetical frame rule.
- The composable artifact today is the **WP lemma, not the exported
  theorem** — exactly how the golden work already behaves
  (`wp_incViaCallLowered_ret2`: one walk, four statement shapes). Compose in
  Iris, read out at the exits.
- A *surface-level* composition rule (statements that chain) is what the
  contextual-refinement candidate would restore (refinements compose;
  readouts don't). That decision binds at the first real library spec —
  `docs/2026-07-21_spec-space.md` §7, row added 2026-07-22. Nothing in this
  arc forecloses it: the internal invariants/abstract predicates are the
  ingredients a compositional surface would repackage.

This is the razor's second horn doing its job: the invariance statement
serves *semantically simple explanation* now, explicitly not *composition
interface* yet.

## 6. The v1 arc: deliverables and the golden discharge

Same anti-hack rules as the spec-surface arc (per-program work = shape
checks + WP proof + generic exit instantiation ONLY):

1. **Surface judgment** `GoInvariant` (Surface.lean, Iris-free), presented
   per §1 as invariance over `Rel`, with the sub-heap reading.
2. **Generic exit theorem** `goInvariant_of_wp` (SurfaceExit.lean): from a
   WP proof with `I` allocated as an Iris invariant, via `wp_invariance`
   (or, if ergonomics demand, `wp_strong_adequacy_gen` directly — the
   spec-surface arc already climbed that hill once with
   `go_heap_adequacy_own`; expect the same kind of work to thread our
   `GoCoreGS` state interp through `wp_invariance`'s ∃-stateI form).
   Non-vacuity: ships with its golden witness in the same commit.
3. **Golden discharge**: *at every reachable configuration of the seeded
   golden driver, cell 0 holds `int 0` or `int 2`* — never 1, never
   garbage, never retyped or deallocated, even mid-call. The miniature of a
   Verdi register invariant. Chosen because the single write-step 0 → 2
   makes the physical invariant hold with no ghost state.
4. **Consistency corollary (intended):** invariance subsumes per-state frame
   preservation — a frame is an invariant you never open. Deriving
   "F intact at every intermediate state" for an untouched F is a good
   check that the pipe is assembled right (today's `F.sub` frame closure is
   terminal-state only, by explicit design).
5. **Docstrings/ledger**: statement-honesty throughout; Audit.lean entries;
   the WP-side proof burden (open/close around each touching step) recorded
   as the known cost, with the ghost-state out queued.

Known unknowns going in: ergonomics of `wp_invariance`'s existentially-
quantified state-interp premise vs our fixed `GoCoreGS`; whether the
`▷`-strip needs a timelessness instance for `HProp`-embedded assertions or
per-case handling; whether `.panicked`-as-stuck interacts with the trivial
postcondition (it shouldn't — Progress already covers it — but check).

## 7. Build record (2026-07-22, same day — the unknowns resolved)

All resolved favorably; the arc built in one pass:

- iris-lean ships everything needed: `wp_invariance_gen`
  (`ProgramLogic/Adequacy.lean:317`), `inv`/`inv_alloc`/`inv_acc`
  (defined directly in accessor form), `instTimelessPointsTo`,
  `elim_modal_timeless`, and mask-generic WP laws throughout.
- **One real architectural finding:** `wp_atomic` is INAPPLICABLE to
  GoCore — it requires the expression to step to a *value*, which works
  in HeapLang only via the bind rule isolating atomic sub-expressions;
  our `Config`s are whole-machine states, never values mid-program. The
  route instead: open the invariant inside the lifting lemmas' own
  `={E,∅}` fupd slots (`wp_store_step₂_inv`), with the goal's `▷`
  absorbing the invariant's later and a timeless strip for the
  reducibility side. If GoCore ever grows an evaluation-context/bind
  structure, `wp_atomic` becomes available — not needed for now.
- Delivered: `GoInvariant` + `goldenInvariant_statement` +
  `goInvariant_mono_pre` (Surface, Iris-free); `embed_timeless`
  (bridge); `go_heap_invariance` (adequacy); `wp_store_step₂_inv`
  (lifting core, invariant content generic via `hopen`/`hclose`);
  `wp_frame_return_inv` (frame-exit form); walk refactor
  `wp_incViaCallLowered_frame` (+ `_call` rederived statement-unchanged,
  `_inv` added); `goInvariant_of_wp` (generic exit; `nroot` namespace,
  v1 single-invariant); `goldenInvariant` (the discharge and the
  non-vacuity witness). Audit ledger `✓ Invariance`; sweep axiom-clean.
- Queued from §6: the frame-subsumption corollary (needs an
  HProp-of-heaplet fold — new surface vocabulary, deliberate decision);
  multi-invariant namespaces; ghost/abstract-state machinery.
