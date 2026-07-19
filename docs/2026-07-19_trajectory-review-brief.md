# Trajectory review brief — `native-frontend` branch before merge (2026-07-19)

This is the **audit target** for the pre-merge adversarial review (practice:
`docs/2026-07-19_review-merge-practices.md`). Reviewers should attack the claims
below against **primary sources** (the real tree, the proof/interpreter files),
not this prose. The branch is 56 commits ahead of `main`; it does not land until
the audit's surviving findings are addressed and merge is signed off.

## 1. Ground-truth (verified 2026-07-19, re-verify — do not trust this list)

- Core `lake build`: green, 36 jobs, dependency-free manifest (iris-free).
- Proofs `lake --dir=proofs build`: green, 184 jobs.
- `lake exe gocore-eval-tests`: 40/40 ok.
- Differential (native frontend, `GOCACHE=/private/tmp/go-build`): append slice
  17/17 fail (all `stage=frontend-export`, feature-blocked, not interpreter);
  range slice 44 cases 22 pass / 22 fail; quorum 39 cases 37 pass / 2 fail (the
  2 are `interfaces/acked-indexer` at `frontend-export` — deferred dispatch).
  Failing-id sets **identical** before/after the oracle-externalization refactor.
- Axiom check (`#print axioms`) clean (`propext`, `Classical.choice`,
  `Quot.sound`; no `sorry`/`native_decide`) for: `wp_seqn`, `wp_assign`,
  `pointsTo_loadLoc`, `heapToMap_set_base`, `get?_heapToMap`, `go_adequacy`.

## 2. What the branch contains (the arc under review)

The Iris proof layer + an oracle-free interpreter substrate:

- **In-repo `proofs/` package** — iris-lean as a pinned git dep; golean core
  stays iris-free. Toolchain bumped 4.29→4.31.
- **Reshape A** — `Config` is state-free; `Step : Config → ExecState → Config →
  ExecState → Prop` (Iris `Expr` can't carry the heap).
- **Bare `Language` instance** on the real `Config`/`ExecState` (CK machine, no
  ectx) — `ToVal`/`PrimStep`/`val_stuck`.
- **WP laws over the real `Step`** — `wp_seqn` (pure), `wp_assign` (heap store),
  `pointsTo_loadLoc` (read law) — plus **`go_adequacy`** (`adequate .NotStuck`).
  gen_heap keyed by base-address `Nat`; `heapToMap` projection (a `foldr`, so it
  matches `Heap.lookup` first-match unconditionally — no heap-uniqueness needed).
- **Reshape B slice 1** — `choices` removed from `ExecState`; the interpreter
  threads `Choices` externally through the statement cluster; relation/proofs
  compare oracle-free state.

## 3. Dimensions to attack (one decorrelated reviewer each)

- **Proof correctness (inside).** Are the WP laws real theorems about the real
  `Step`, or do the instances (`ToVal`, `PrimStep`, `IrisGS_gen`, `StateInterp`)
  or the `heapToMap` bridges quietly encode something trivial/false? Do the
  axioms actually stay clean when rebuilt? Is `go_adequacy`'s ported functor
  bundle sound, or does an instance mismatch make it vacuous?
- **The `hred` caveat (inside).** `wp_assign`/`pointsTo_loadLoc` assume an
  operational side condition because locals aren't in the state interp. Is the
  caveat honestly scoped, or does it hollow out the law? Is the stated discharge
  path (locals-in-state-interp / resolved-Config) actually viable?
- **Oracle externalization (inside).** Does the external `Choices` threading
  reproduce the old global-`choices` semantics *exactly* (calls, loops, nested
  ranges, non-empty streams — which the differential corpus does NOT exercise,
  since it runs `choices=[]`)? Any path where a choice is consumed/dropped
  differently than before?
- **Architecture / is-it-the-right-thing (outside).** Bare `Language` + CK
  machine vs. ectx; the state-free `Config`; oracle-external interpreter — judged
  independently against the north star (etcd-io/raft quorum safety). Is this the
  skeleton that scales, or a local optimum?

## 4. Open design decisions for the review to adjudicate

1. **hred discharge fork** — resolved-Config (HeapLang-style, bigger `Rel.lean`
   change) vs. locals-ghost-map (proof-layer-local, second heap). Deferred.
2. **Relation feature-modeling policy** — Reshape B slice 2 (existential
   `mapRange`) needs map values in the relation (currently zero map support).
   How much of each feature to model relationally vs. lean on the interpreter?
   This is the first instance of the general policy toward raft.
3. **Merge-invariant scope** — the quorum feature set vs. every interpreter
   feature (review C5).
4. **Depth vs. breadth** — proof-layer depth vs. native-frontend feature coverage
   (append/new/range-over-string/interface-dispatch are all frontend-blocked).

## 5. Merge recommendation (pending audit)

The branch is a coherent, per-commit-validated milestone and a good place to
land — **after** the adversarial audit clears it. Next front (relation
feature-modeling, slice 2) opens the decisions in §4 and should start only once
the review has set direction.
