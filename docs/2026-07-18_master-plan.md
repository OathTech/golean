# GoLean master plan — the trust chain (2026-07-18)

Status: **for adversarial review.** This is the authoritative statement of what
we are building and why the current work sequence serves it. It supersedes
scattered rationale in `TODO.md`, `docs/native-frontend-goal.md`,
`docs/nondeterminism-design.md`, and `docs/2026-07-18_totality-fuel-decision.md`
(which remain the detailed sources). If a reviewer finds a load-bearing claim
here to be false, we want to know **before** spending more on interpreter
totality.

---

## 1. The goal

One end-to-end trust chain, culminating in machine-checked proofs of real Go
program properties (north star: `etcd-io/raft` quorum safety, then up the
ladder in `docs/roadmap.md`):

```
 real Go source
   │  (A) native frontend: go/parser + go/types → typed wire → NativeToIR → GoCore
   ▼
 GoCore program
   │  (B) executable interpreter (Eval.lean), differentially validated vs `go run`
   │  (C) relational semantics (Rel.lean), the proof authority
   │      linked to (B) by the correspondence theorem (Correspondence.lean)
   ▼
 (D) Iris-Lean weakest-preconditions over the relation → proofs of properties
```

The deliverable is a *proof about the relation* plus a *justified belief that the
relation faithfully models real Go*, so the proof transfers to the real program.

---

## 2. The two artifacts, and why there are two

The single most important architectural fact: **there are two semantic objects
on purpose.**

- **Interpreter** (`Eval.lean`): a *deterministic-given-an-oracle*, executable,
  fuel-bounded definitional interpreter. Big-step (`execStmt` runs a statement
  to an `ExecOutcome`). It is what the differential suite runs. It resolves
  nondeterminism by consuming a choice stream (`ExecState.choices`, the
  "parser of randomness").

- **Relation** (`Rel.lean`): a *nondeterministic*, non-executable, fuel-free
  small-step relation (big-step `ExprR` for the call-free expression sublanguage
  + small-step `Step` on `Config`/`Cont`). It is the object Iris reasons over.

### Why we cannot collapse them into one executable step function

The relation is **deliberately nondeterministic**: it must relate one `Config`
to *every* successor real Go permits (map/range iteration order = any
permutation; `append` growth cap = any value ≥ new length). Iris soundness
requires this: a proof over the relation must hold for *whichever* behavior the
real program picks, so the relation must **over-approximate** real Go's behavior
set. A nondeterministic relation is not a function, so there is no total
`stepf : Config → Config` with `Step c c' ↔ stepf c = c'`. The executable object
is necessarily *oracle-parameterized*: `interpreter(oracle, c)`. The relation is
then `∃ oracle, interpreter picks this`; the interpreter is one oracle's slice.

This is exactly why a separate executable interpreter exists. Any plan that
proposes "just make the relation executable and test it directly" is wrong on
this point — it silently assumes determinism the semantics must not have.

### Honest status of the nondeterminism (do not overclaim)

**Today, `Rel.lean` is still deterministic.** Its covered subset (scalars,
control flow, direct calls, pointers, arrays, struct fields) has no
nondeterministic construct, so on that subset interpreter and relation coincide
up to oracle-irrelevance. The nondeterminism enters only when maps, `mapRange`,
and `append` land in the relation (planned; see §6 step 2 and the merge
invariant). The two-artifact justification above is therefore a **design
commitment we have not yet exercised**, not a property of the current relation.
A reviewer should decide whether that commitment is right *now*, because it is
the reason we keep and totalize the interpreter rather than retiring it.

Note also that even where nondeterminism does not change the *observation*
(quorum's map folds are commutative — the whole point of the observation-
invariance test), the relation still must permit all iteration orders, because
intermediate states differ and an Iris proof must cover each. So nondeterminism
in the relation is load-bearing even when the differential observation is
invariant.

---

## 3. Why totality — the mechanism

`partial def` in Lean 4 elaborates to an opaque constant with **no equational
lemmas**. You cannot unfold it, invert a `f x = v` hypothesis about it, or
rewrite with it. Consequences that blocked the proof half:

1. `Rel.lean`'s rule premises call substrate functions (`loadLoc`, `storeLoc`,
   `valueEq`, `defaultValue`, `normalizeValueForTy`, `arrayGet`). While those
   were `partial`, **the relation's own rules could not be reasoned about** —
   the relation was not actually a usable proof authority.
2. `Correspondence.lean`'s statements (`execStmt … = .ok … → Steps …`) invert an
   `execStmt` hypothesis, impossible while `execStmt` is opaque.

So totality is not ceremony; it is the precondition for (C) and (D) to exist.

### What is done

- **`Ops.lean` is fully total (zero `partial def`).** This is the review's
  actual blocker resolved: `Rel.lean`'s premises are now unfoldable, so the
  relation is — for the first time — a legitimate proof authority. Needed under
  *any* architecture; not at risk in any fork.
- **The interpreter's expression/value layer is total.** `evalExpr` and all
  expression/assignment helpers form a structural lower cluster (ANF keeps calls
  out of expression position, so it never recurses through fuel).

### What remains

- **The interpreter's statement/call layer** (`execStmt`, `execFunctionCall`,
  `execMapRangeLoop`) — fuel'd upper cluster — is still `partial`. Its
  termination measure is non-trivial (see §5). This is the larger remaining
  half, and the only reason to do it is the correspondence theorem (C↔B).

### The fuel strategy and its seams (attack these)

Totality strategy is **fuel**, chosen over a type-environment-acyclicity
well-formedness proof for uniformity with `execStmt` and reversibility
(`docs/2026-07-18_totality-fuel-decision.md`). Two distinct fuels, with
different blast radius:

- **Interpreter execution fuel** (`execStmt fuel`, seeded 100000): bounds
  call/loop depth so the *interpreter* is a total function. **The relation has
  no such fuel** — it is unbounded. So this fuel is purely a testing-artifact
  concern: a run that exceeds it is visibly "fuel exhausted" (never counted as a
  pass), and it never touches the proof authority. Safe.

- **Type-resolution fuel** (`typeResolutionFuel = 1024`) inside the
  *type-directed* Ops (`normalizeValueForTy`, `valueEq`, `defaultValue`, …).
  These Ops are premises of **both** the interpreter and the relation. So the
  relation inherits a 1024-deep bound on `.defined`-type resolution: for a type
  nested deeper than 1024, `normalizeValueForTy … = .ok v'` is unsatisfiable
  (returns `unsupported`), the relevant `Step` rule cannot fire, and the
  relation is **stuck**. That is an *under-approximation* of Go at depth > 1024.
  For a safety proof, under-approximation is the *unsafe* direction in
  principle. Our defense: (i) 1024 exceeds any real Go type nesting by orders of
  magnitude — Go value-containment cannot cycle, so real depth is tiny; (ii) it
  is *fail-closed and visible* (the interpreter says "type nesting too deep", not
  a silent wrong answer), so it scopes the modeled language rather than hiding a
  bug; (iii) it is reversible to the acyclicity proof. **Reviewers: decide
  whether a scoped-by-fuel relation premise is acceptable, or whether the
  type-directed Ops must be total by acyclicity so the *relation* carries no
  artificial bound even if the interpreter does.**

---

## 4. The soundness argument, with seams named

We want: *a property proved of the relation (D) actually holds of the real Go
program.* This composes several guarantees of different strengths. Naming the
seams is the point of this section.

1. **Frontend faithfulness (A).** Go source → GoCore preserves semantics.
   *Guarantee: trusted + tested (fail-closed on anything unsupported).* Not
   proven. Seam.
2. **Interpreter ≈ Go (B).** For tested inputs, interpreter observations equal
   `go run` observations, and are invariant across oracle streams where Go's
   nondeterminism is observation-irrelevant. *Guarantee: empirical
   (differential), finite input coverage.* Seam: test sufficiency (mitigated by
   the three-layer strategy — isolated features, edge enumeration, integration +
   fuzzing — see `docs/native-frontend-goal.md`).
3. **Interpreter ⟹ relation (C, the correspondence).** Every interpreter run
   (under any oracle) is a path the relation permits: `execStmt … = .ok … →
   Steps …`, and panics correspond to `panicked`. *Guarantee: to be proven.*
   This makes the relation **over-approximate the interpreter**. Direction
   check: this is the safe direction — it forbids the relation from being
   *narrower* than the tested interpreter.
4. **Relation ⊇ Go behaviors (the completeness we actually need for Iris).**
   The relation must permit every behavior real Go can exhibit. This does **not**
   follow from (3) alone: (3) says relation ⊇ interpreter(one oracle at a time);
   we additionally need (a) the oracle range to cover *all* of Go's
   nondeterminism (design claim in `docs/nondeterminism-design.md`: the oracle
   is introduced at exactly Go's nondeterminism points — map/range order, append
   cap — and nowhere else), and (b) the relation to permit all oracle outcomes
   (the merge invariant enforces this as rules are added). *Guarantee: (a) is a
   design argument, tested only indirectly via observation-invariance; (b) is a
   construction discipline.* **This is the deepest seam and the reviewers'
   priority.**
5. **Iris soundness (D).** WP rules are proven sound against `Step`; the
   adequacy theorem yields the property. *Guarantee: proven (once built), on top
   of iris-lean.* Seam: iris-lean toolchain gap (v4.31 vs project v4.29), and
   the `Config`/`Cont` vs Iris `ectx` embedding.

Composed guarantee, stated honestly: *if the frontend is faithful (1, trusted),
and the relation over-approximates Go (4, part design/part discipline), then an
Iris-proved safety property (5) holds of every real Go execution — with the
differential suite (2) as the continuous empirical check that our model has not
drifted from Go, and the correspondence (3) ensuring the tested object and the
proved object cannot silently diverge.*

Over- vs under-approximation, the one-line rule: **safety proofs are sound under
over-approximation (relation does ≥ Go) and unsound under under-approximation
(relation does < Go).** Every modeling choice must be checked against this. The
type-resolution-fuel seam (§3) is the one current place we knowingly
under-approximate (at unreachable depth).

---

## 5. The remaining interpreter-totality measure (the concrete hard part)

Making the fuel'd upper cluster total needs a lexicographic `(fuel, phase,
size)` measure, because two edges are not simple structural descents:

- **Call delegation** `execFunctionCall → execFunctionCallWithLocs →
  execFunctionWithValues` runs at *constant* fuel (no shrinking syntax), then
  `execStmt (fuel-1)` on the callee body. → put the call cluster on a lower
  `phase` than `execStmt`; fuel drops on the final edge.
- **`execStmt(.mapRange) → execMapRangeLoop`** crosses from bounded syntax to
  *unbounded runtime map data* (`remaining` entries), and the loop runs the body
  at the same fuel. → run the map-range body at `fuel-1` (invisible against
  fuel = 100000, and the loop terminates by finiteness of the snapshotted
  entries regardless), so that edge drops fuel; the loop's own recursion
  descends structurally on `remaining`.

This is engineering, not research, but it is the delicate part and must not
silently change fuel accounting in a way a differential case would notice.
(`evalExpr` and the `Ops` list-helpers already validated the pattern: refactor
`for`-loops that hide recursive calls into structural list helpers, then Lean
infers the rest.)

---

## 6. The work sequence and current status

1. **Totality** (in progress). [x] `Ops` fully total. [x] interpreter
   expression layer total. [ ] interpreter statement/call layer total (§5).
   [ ] prove one correspondence lemma on the scalar subset end-to-end.
2. **Relation catch-up + merge invariant.** Grow `Rel.lean` to the interpreter's
   feature subset — slices, maps, `mapRange`, conversions, multi-assign — with
   nondeterminism expressed as the relation permitting all valid behaviors (this
   is where §2's commitment is first exercised and §4's seam (4b) is enforced).
   No interpreter feature merges without its relational rule.
3. **Guardrails.** Strengthen oracle-invariance (exhaustive small-map perms +
   seeded random), golden-wire emitter unit tests, a multi-file corpus case.
4. **Iris `Language` spike.** Instantiate iris-lean from `Step`, prove one WP
   rule, flush out the `Config`/`Cont`-vs-`ectx` embedding and the toolchain gap.

Deferred until the foundation is set: native interface dispatch (last 2 quorum
cases), feature breadth up the raft ladder, `slices.Sort` extern + input
fuzzing.

---

## 7. Questions we most want the review to answer

1. **Is the correspondence direction (§4.3) the right one**, or do we also need
   the reverse (relation ⟹ ∃oracle interpreter) as a soundness-critical
   adequacy result rather than a nice-to-have?
2. **Is seam §4.4 (relation ⊇ Go) adequately discharged** by "oracle at exactly
   Go's nondeterminism points" + the merge invariant + observation-invariance
   testing, or does it need a stronger, more explicit argument/artifact?
3. **The type-resolution-fuel under-approximation (§3):** acceptable as a
   scoped, fail-closed bound, or must the type-directed Ops be total by
   acyclicity so the *relation* carries no artificial bound?
4. **Big-step interpreter vs small-step relation:** is big-step⟹small-step\*
   correspondence the right bridge, or does the shape mismatch make a small-step
   (oracle-parameterized) interpreter worth the rewrite for a definitional link?
5. **Is finishing interpreter totality (§5) the right next investment**, or
   should relation catch-up (step 2) come first so we design the correspondence
   against the *nondeterministic* relation we will actually keep, not the
   deterministic skeleton?
6. **Anywhere the composed guarantee (§4) is weaker than it reads** — any seam
   that is actually unsound rather than merely trusted/empirical.
