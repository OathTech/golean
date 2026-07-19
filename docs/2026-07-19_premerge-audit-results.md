# Pre-merge audit results — `native-frontend` branch (2026-07-19)

Adversarial audit per `docs/2026-07-19_review-merge-practices.md`, balanced scale:
4 decorrelated reviewers (D1 proof-correctness, D2 hred-honesty, D3
oracle-equivalence, D4 architecture) + one independent verifier (default-refute).
13 findings; verifier **11 CONFIRMED, 2 UNCERTAIN**. Encoded as a `Workflow`
(run `wf_b78b814b-6b7`). Synthesis below; I spot-checked the load-bearing
survivor (D2-4) against the source myself.

## What is genuinely strong (credited)

- **D3 (oracle externalization) found NOTHING.** The reviewer traced the external
  `Choices` threading against the pre-refactor `git show e085959^` and found no
  path where the stream is dropped/reset/duplicated or consumed out of order —
  including the non-empty-stream paths the differential corpus never exercises.
  The Reshape B slice-1 refactor is clean.
- **All target theorems are axiom-clean and non-vacuous where claimed.** Rebuilt:
  core 36 jobs, proofs 184 jobs; `#print axioms` = `[propext, Classical.choice,
  Quot.sound]`, no `sorryAx`. `ToVal`/`val_stuck` genuinely non-vacuous;
  `go_adequacy`'s functor bundle line-for-line mirrors iris-lean's
  `heap_adequacy` (a mismatch would fail `exact Hwp`).
- **The `heapToMap` bridge lemmas survived every counterexample** the reviewer
  tried (duplicate base keys, non-base locs, empty heap). The `foldr`-first-match
  reasoning holds.

## Real findings → resolution

**Overclaims corrected in the record (this commit):**

- **D2-4 / D2-5 (major): `wp_assign` is a SCAFFOLD, not a usable law.** Its `hred`
  hypothesis is *unsatisfiable* for any real assign — `hred` quantifies `∀ σ₁`
  constrained only on `σ₁.heap`, but a variable LHS needs `σ₁.locals`, so an
  empty-locals `σ₁` meets the antecedent and admits no step. No instance exists;
  the earlier "discharged per-call for a variable LHS" claim was **false**.
  Docstring + `TODO.md` 3b.2 corrected. *(I re-derived this from the source —
  confirmed.)*
- **D1-1 (major): `go_adequacy` excludes panicking runs.** `.panicked` has no
  outgoing `Step`, so `adequate .NotStuck` treats it as *stuck* — any Go panic
  makes `Hwp` unprovable, contradicting Rel.lean's "panics are behavior".
  Docstring + `TODO.md` 3b.3 corrected to "non-panicking runs only".
- **D1-2 / D1-3 (minor): WP-law inventory overstated.** Only `wp_seqn` is an
  unconditional standalone WP law; `wp_assign` is `hred`-conditional (see above)
  and `pointsTo_loadLoc` is an ownership⟹pure-fact lemma, not a WP. Corrected.
- **D4-13 (minor): roadmap is stale** — still frames Gobra as the frontend
  (dropped) and the native frontend as unrealized critical-path risk. Staleness
  banner added; full rewrite tracked.
- **D2-8: task #21's completed title misrepresented** ("discharge hred") — `hred`
  is not discharged. Task subject/description corrected; real work = new task #23.

**Deferred structural work (new/existing tasks, correctly next-phase):**

- **#23 (3b.4): model locals in the state interp** → make `hred` dischargeable and
  `wp_assign` a real Hoare law. Load-bearing; D2-7/D4-12 note locals are a
  name-shadowing push/pop scope stack **split across `Config.frame` and
  `ExecState.locals`** — harder than the heap wiring.
- **#24: admit panicking terminals** (panics-as-values/obs) so adequacy covers
  real Go runs.
- **D4-10 (confirmed): the interpreter⇄relation correspondence is unprovable in
  the current shape** (partial interpreter + hand-written relation, no proven
  link) — already tracked in `Correspondence.lean`'s header and gated on
  totalization (task #14/#18).
- **D4-11 (confirmed): `ExprR` is big-step-folded into atomic `Step` premises**;
  WP laws assume pure non-panicking expressions. A known shape cost; relevant to
  the relation feature-modeling policy (trajectory decision).

**UNCERTAIN (judgment, for the trajectory decision, not a merge blocker):**

- **D4-9: is Iris/gen_heap depth sequenced ahead of quorum-safety needs?** The
  factual scaffolding checks out (no GoCore⇒abstract-raft refinement/invariant
  layer yet), but "separation-logic depth is premature, reorder to a vertical
  slice now" is a prioritization call the verifier could not decide. Carry into
  the next trajectory decision.

## Merge posture

No false theorems, no broken code, no regressions — every "finding" was an
**overclaim in prose/status** (now corrected) or a **tracked structural gap**
(now filed). The branch's substance stands: an axiom-clean Iris scaffold + a
clean oracle-free interpreter substrate. With the record corrected, the branch
clears for **ff-merge to `main` on point-of-merge sign-off**.
