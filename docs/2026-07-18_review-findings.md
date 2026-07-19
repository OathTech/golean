# Adversarial review findings — full record (2026-07-18)

Detailed findings from the three-reviewer adversarial attack on
`docs/2026-07-18_master-plan.md`. The synthesis and the resulting reordered
sequence live in that plan's **§8**; this file is the durable record of the
individual findings (severities, concrete failure scenarios, file:line
citations) so nothing is lost to chat. Reviewers: proof-theory, Iris
mechanization, engineering strategy — each briefed adversarially.

**Unanimous verdict: two-object architecture SOUND (do not rethink the
foundation); the §6 work sequence and two GoCore shapes are wrong and must
change before more big-step interpreter-totality investment.**

---

## A. Proof-theory reviewer — verdict (b): sound, fix these first

**A1 (serious, cheap). The adequacy theorem's shape decides whether
under-approximation is UNSOUND or merely proof-blocking — and it is not yet
chosen.** "Fail closed" means two different things: the interpreter fails closed
*visibly* (`.error (.stuck/.unsupported)` → red differential case), but the
relation fails closed *invisibly* ("stuck = absence of rule", `Rel.lean:16-19,
234`; a stuck `Config` is silent, non-terminal per `Config.terminal`
`Rel.lean:354`). Iris safety adequacy has two flavors:
- *Partial* ("if the run reaches a terminal, P holds"): a relation stuck before
  Go reaches a bad state proves P **vacuously → false safety**.
- *Not-stuck/progress* ("every reachable config is a value or steps, and P
  holds"): a stuck-where-Go-steps config makes the proof **fail**, never false.
Concrete: type-resolution fuel at depth > 1024 makes `normalizeValueForTy … =
.ok v'` unsatisfiable (`Ops.lean:289`), so `Rel.lean`'s `assign` (266-270) and
`call` (321-328 via `BindParamsR`→`normalizeValueForTy` 181) premises cannot
fire; the config is stuck and non-terminal. Under partial adequacy that is a
false-safety hole; under not-stuck adequacy it is merely proof-blocking.
**Decision D1: commit in writing to not-stuck/progress adequacy** (Iris's
standard `adequate` includes the not-stuck clause — costs only the commitment).
Also: the 1024 bound is unreachable only for real-Go *value* containment
(structs can't contain themselves by value; pointers stop the recursion); a
frontend/adversary emitting GoCore directly could build a 1024-deep
`.defined→.alias` chain, so the unreachability defense inherits the frontend's
trusted+total status (seam §4.1) rather than being independent.

**A2 (serious / potential blocker for the nondet work). Under-approximation by
MISSING BRANCH is invisible to both progress-adequacy AND the entire empirical
apparatus.** Progress-adequacy (A1) catches stuck-style under-approximation but
NOT a relation that still steps yet omits one of Go's nondeterministic
alternatives. Concrete: the planned map model (`nondeterminism-design.md:126-137`)
snapshots entries and permutes a *fixed* snapshot — but Go permits entries
*inserted* during `for k := range m` to be visited. "Permute the snapshot" misses
that behavior. A safety proof "the key we insert during iteration is never
processed this pass" is TRUE over the relation, FALSE in Go. Nothing catches it:
progress-adequacy (relation still steps), differential test (`go run` shows one
order per run; added-key-visited is never the compared order), observation-
invariance (for commutative quorum folds the observation is invariant across
orders, so the test passes trivially — **zero** evidence about branch coverage,
exactly on the programs where nondeterminism is load-bearing). So §4.4's "tested
indirectly via observation-invariance" overstates: for observation-invariant
programs it is tested by nothing; the merge invariant is unchecked construction
discipline. **Decision D2: a per-nondeterministic-construct completeness
ARTIFACT** ("here are all successor states Go permits from this config + the rule
permitting each"), and decide map-mid-mutation semantics explicitly — Perennial's
read-invalidation/abort (`nondeterminism-design.md:116-118`) vs snapshot-permute;
snapshot-permute is the under-approximating default, do not fall into it.

**A3 (serious; supports plan Q4). A big-step interpreter can only bridge
TERMINATING runs; raft's core is reactive/nonterminating.**
`interpreterSoundStatement` (`Correspondence.lean:34-37`) relates only runs that
terminate at `.next .stop`. A nonterminating Go program fuel-exhausts →
`.error`, so the correspondence hypothesis is never satisfied and the
differential suite can only test terminating harnesses. etcd raft's core is a
reactive `Step(Message)` loop that runs forever; its safety is proved over
infinite executions (Iris handles this via invariants), but the correspondence —
the only tie between tested interpreter and proved relation — covers none of
those, not even finite *prefixes* (a prefix ends in a non-terminal config the
big-step statement cannot mention). Safety is prefix-closed, so "test finite
prefixes + prove over all executions" is right, but needs a correspondence that
covers prefixes ending mid-execution. **Decision D3: step-indexed/prefix
correspondence, or a small-step oracle-parameterized interpreter.**

**A-answers.** Q1: interpreter⟹relation is the correct soundness direction
*between those two objects* (forbids the relation being narrower than the tested
interpreter); the reverse is over-approx-tightness (proof-goes-through, not
soundness). But neither direction bridges to *Go* — Go-faithfulness enters only
through the finite differential seam; "this is the safe direction" is a motte
(true of the interp/rel link, which is not the soundness-critical one — Go ⊆
relation is). Q5 checks: ANF "expressions contain no calls" is **structurally
enforced** (`Expr` `Syntax.lean:45-91` has no call constructor; calls are only
`Stmt.call` 114) and `ExprR` never mutates state, so the big-step-expr collapse
is genuinely safe *now* — latent-fragile if calls or concurrency enter
expressions; panic-as-behavior/stuck is coherent; frame/scope/call rules correct
(break/continue have no `.frame` rule → relies on a trusted "break/continue are
loop-enclosed" well-formedness assumption; callee heap cells not reclaimed on
frame exit — space artifact, not soundness). The proven Correspondence instances
cover ~5% of the interpreter's real surface (no and/or, convert, mod/shifts,
mapGet, slice, len, structLit, toInterface, typeAssert, multi-assign) — honest
status, but (C) currently constrains only a toy subset.

---

## B. Iris-mechanization reviewer — bottom line: Iris goes through, but NOT on Rel.lean's shape as-is

Grounded in the actual `deps/iris-lean` sources.

**B1 (serious, change now). `Config` bakes state into the term → cannot be Iris
`Expr`.** Iris `PrimStep` (`Language.lean:55-57`) is `Expr × State → Obs → Expr ×
State × List Expr → Prop`; the heap MUST be the separate `State` projection
(state interpretation / `genHeap`/`pointsTo` bind against it). Every `Config`
constructor carries `ExecState` (`Rel.lean:224-231`), so there is no state-free
projection and the `ToVal` round-trip law `toVal (ofVal v) = some v`
(`Language.lean:22-28`) is unsatisfiable. **Reshape A: `Expr := control token +
Cont`, heap moved to Iris `State`.** Re-plumbs `Config`, `Step`, and `ExprR`
(which threads whole `ExecState`, reading locals via `lookup` and heap via
`loadLoc` in the same rule, `Rel.lean:103-106`). Locals straddle the split
(`Cont.frame` stores `callerLocals` `Rel.lean:221` while `ExecState.locals` is
read/written throughout) — an `ExprR` premise must reassemble both projections
and re-split; provable, tedious.

**B2 (serious). Config/Cont is NOT an `EctxLanguage` → no `wp_bind`.**
`EctxLanguage` (`EctxLanguage.lean:151-173`) needs an `Ectx` with
fill/comp/empty; a CK machine is the dual (the step dispatches ON the
continuation — `seqNext`, `loopNext`, `frameReturn/Fall` pattern-match `Cont`,
`Rel.lean:240,303-310,330-337`). Use **bare `Language`**: lifting lemmas
(`wp_lift_step`, `wp_lift_atomic_step`, `wp_lift_pure_det_step_no_fork`,
`wp_pure_step_later` — `Lifting.lean:77,156,172,216`) + full adequacy
(`adequate_alt`, `adequate_tp_safe`, `wp_adequacy_gen`, `wp_invariance_gen` —
`Adequacy.lean:247,262,279,318`). Map: `Expr`=control+Cont, `Val`=terminal
control token (`.next .stop`; decide panic=stuck vs value), `State`=heap,
`primStep (e,σ) [] (e',σ',[]) := Step`. **Cost: no `wp_bind`/compositional WP**
(comes only from the `Context`/ectx machinery, `Language.lean:256-338`); prove
statement/function specs by manual induction over statement + continuation
structure. Still get the separation-logic heap, framing, invariants, later
credits — not slick modular WP.

**B3 (serious latent trap). Big-step `ExprR` in a `Step` premise is sound but
forecloses expression-granular WP, and "ANF ⇒ safe" is too weak.** The real
invariant: expressions must be pure, total, deterministic, heap-read-only,
non-allocating, fuel-independent (holds today — no `ExprR` rule stores or
allocates; `deref` only `loadLoc`s `Rel.lean:103-106`, `ref` only looks up
`100-102`). Consequences: no reusable `wp_load`/`wp_store` at expression
granularity (the atomic Iris step is the WHOLE statement; each statement rule
re-derives heap agreement inside one `wp_lift_atomic_step`) → **the spike must
prove a heap-touching ATOMIC statement, not a pure control step**. The trap:
`append` (nondet cap), map/composite literals, `new` (allocation) break `ExprR`
purity the moment they enter `Expr` position, forcing the "refactor expressions
into the configuration language" the `Rel.lean:56-59` comment warns of —
triggered by effects/allocation/nondet, not only calls. Enforce a typed
invariant on what may be `Expr` now.

**B4 (serious, decide now). Oracle-in-`ExecState` breaks the correspondence's
state equality once `mapRange` lands.** `ExecState.choices : List Nat`
(`State.lean:43`) is inside the state, mutated by `consume` (`State.lean:133-137`),
consumed by `execMapRangeLoop` (`Eval.lean:825`). The relation uses the same
`ExecState` but no `Step` rule touches `choices`. Correspondence
(`Correspondence.lean:34-37`) requires the SAME `s'` both sides. On scalars
`consume` never fires; once `mapRange` runs the interpreter's `s'.choices =
<consumed tail>` while the relation leaves them original → the two `s'` differ →
**the conclusion is FALSE as stated**, not merely unproven. Can't fix by making
the relation consume choices (that makes it deterministic-given-choices,
destroying the nondeterminism thesis). **Reshape B: `choices` must leave
`ExecState` into an external oracle stream; the `mapRange` rule quantifies
`∃ idx < remaining.size, …`; the correspondence instantiates that existential
with the oracle's pick.** Decide before step-2 relation catch-up.
`mapRange` correspondence is currently *vacuous* (no `Step` rule) — deferred is
fine, but the plan should say the correspondence is meaningful only after step 2,
and `mapRange` is where oracle-quantification + choices-out-of-state get
validated, not a mechanical extension of the scalar proof.

**B5 (minor for Iris). Nondeterminism in Iris is not a problem.** `primStep` is
a relation; `wp_lift_step` (`Lifting.lean:77`) quantifies the post over ALL
successors — exactly the "invariant for every iteration order" obligation. The
choice's place is an existential in the rule. No observations needed
(`Obs := List Unit`).

**B6 (serious for integration, minor for the spike). Toolchain gap.** Project
`v4.29.1`, iris-lean core `v4.31.0`; iris-lean deps are only `Qq` + `batteries`
at 4.31 (`Iris/lakefile.toml`) — no full Mathlib (their `FromMathlib`/`Std` is
vendored), lighter than `docs/iris-lean-review.md` implies. iris-lean uses the
new module system (`module`, `public import`) — a 4.31 feature; a 4.29→4.31 bump
is mandatory before it's a real dep. Not a spike blocker: instantiate `Language`
+ prove one WP in an isolated worktree pinned to 4.31 + Qq + batteries,
vendoring GoCore types, before touching the main build. Verify up front that
`adequate_alt`/`adequate_tp_safe` (`Adequacy.lean:247,262`) give the safety
statement wanted (they exist — a check, not a risk).

---

## C. Engineering-strategy reviewer — bottom line: reorder, Iris spike first

Grounding: `Eval.lean` ≈ 915 lines (maps, slices, append, mapRange, dynamic
dispatch; statement/call layer still `partial`); `Rel.lean` ≈ 359 lines (scalars,
control, direct calls, pointers, arrays, struct fields; deterministic; **zero**
rules for maps/slices/append/mapRange/interfaces). The relation lags the
interpreter by ≈ half.

**C-F1 (blocker, sequencing). The Iris endgame is scheduled LAST and is the only
unattempted link.** The whole deliverable's value depends on link D (WP →
adequacy → property); every other seam is "trusted/tested/to-be-proven with a
known method." D carries the two architecture-level unknowns (Config/Cont-vs-ectx
embedding, toolchain gap) yet sits after totalizing a 915-line interpreter and
dozens of relational rules whose shape may need to change to fit Iris — "the
textbook formal-methods death." Its precondition is already met (Ops total, the
scalar relation exists). **Pull a minimal Iris vertical slice to the front.**

**C-F2 (serious; answers Q5). "Totalize the whole interpreter + one scalar
lemma" is weak de-risking.** (a) Totalizing `execMapRangeLoop`/`execAppendSlice`/
`dynamicDispatch` produces total functions with no proof consumer for months
(the relation has no rules for those — you cannot even *state* their
correspondence). (b) The scalar lemma validates only the easy half — the
correspondence *statement* changes shape once nondeterminism lands
(`execStmt(oracle) = ok → ∃ path, Steps`), which the scalar lemma never
exercises. The de-risking lemma is the correspondence over the SMALLEST
nondeterministic feature (append-cap, or a 2-element map range) — partially
swaps §6 steps 1 and 2.

**C-F3 (serious). The merge invariant is over-broad — ~50% velocity tax.**
Adopting it now freezes feature progress while the relation catches up on
maps/slices/mapRange/interfaces the proof does not need yet, and taxes every
future feature 2×. **Scope it to the proof frontier**: require the relational
rule only for features the current ladder rung proves over (quorum: uint64
arith, control flow, maps range/comma-ok, slices append/sort — NOT
channels/defer/goroutines/most interface machinery). The differential suite
guards interpreter correctness; the relation need only exist for what you are
about to prove.

**C-F4 (serious). Two artifacts in lockstep = one tested + one UNTESTED
artifact.** The relation is non-executable → no differential test; its only
check is human review + the (unproven-until-per-feature) correspondence. This
breaks hardest exactly at the nondeterministic features where relation and
interpreter diverge by design. **Pick one honestly**: either make the
correspondence lemma part of the "proof-ready" merge bar, or treat the relation
as scratch until proof time — don't maintain unchecked relational rules.

**C-F5 (defense). The two-artifact design and Ops-first totality are correct.**
The nondeterminism argument holds (the Iris relation must over-approximate, so it
cannot be a total `stepf`; a separate oracle-parameterized executable is
necessary). Don't collapse to one. Ops-first was right — zero throwaway risk.

**C-F6 (serious). "Green ⟹ quorum covered" is a category error.** The sufficiency
argument is about the INTERPRETER path (Go vs Lean-interpreter observation
equality); it buys *model fidelity*, not the *safety* guarantee. The north star
is *proving* quorum safety, not executing it — only the proof gives universality.
Secondary: Layer-3 fuzzing and the `slices.Sort` extern are still pending, so the
claim is unmet even for the interpreter today. Keep the three-layer strategy;
stop implying it discharges the north star.

**C-F7 (minor). The type-resolution-fuel seam is eating review attention.** It is
an unreachable, fail-closed corner; do NOT spend an acyclicity-proof rewrite on
it now. Contrast the big-step-vs-small-step shape mismatch (a real risk) — let
the Iris spike force that answer rather than debating it abstractly.

---

## Convergences (why the reorder is trusted)

- **Big-step-totality-next is wrong** — three independent reasons: can't cover
  reactive/nonterminating raft (A3); conclusion goes false at first
  nondeterministic feature via oracle-in-state (B4); scalar lemma de-risks the
  easy half (C-F2).
- **Iris spike should be front-loaded** (C-F1) — but it needs **Reshape A**
  first (B1): `Config`-as-written cannot be Iris `Expr`. So the strategy
  reviewer's "precondition already met" is corrected by the iris reviewer.
- **Two-object architecture + Ops-first totality are correct** — do not collapse
  or rethink (A intro, B implicitly, C-F5).
- **Decisions D1–D3** (A1/A2/A3) are cheap and change what "done" means; make
  them before more totality work.

See `docs/2026-07-18_master-plan.md` §8 for the resulting reordered sequence.
