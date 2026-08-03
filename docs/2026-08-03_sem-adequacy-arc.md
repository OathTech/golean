# The sem() adequacy arc — plan of record (2026-08-03)

Decided in the 2026-08-03 baselining conversation (user + agent, recorded
here per the capture-decisions rule). This arc realizes the project's
statement idiom in its final intended form and supersedes older framings —
see §Supersessions, which edits the living docs in the same commit so no
remnant of the old framing survives as guidance.

## THE GOAL (the user's formulation, verbatim in substance)

We are building a **semantic evaluation function `sem()` over GoCore
programs**: more or less an interpreter — it can terminate or keep going —
with type roughly `GoState → GoState` over configurations of memory and
variables. Specifications are stated ENTIRELY in interpreter-level notions:

    ⟨P terminates⟩ ∧ ⟨state satisfies pre⟩ → sem(P, state) satisfies post

with variants for reasoning about nontermination, and (future) concurrency
handled by an outer fork/join scope — single-threaded pre-state in, forked
execution, join, results read off — so even concurrent specs are pre/post
state statements over `sem`. **Iris is proof machinery, never a
specification idiom.** We build the semantics for fidelity (differential
testing) and use Iris internally. The agent's stronger rendering (below) is
adopted so long as the user's form above is a supported case.

## The decisions

1. **One trusted semantic artifact.** `sem` is `stepFn` iterated under fuel
   (`execStmt` is exactly that wrapper — post-reshape there is no second
   interpreter). This is the differentially validated artifact and the ONLY
   semantics allowed in headline statements.
2. **The Prop-level relation (`Rel.lean` `Step`/`Steps`) is proof
   infrastructure**, exactly like Iris: required because WP needs a
   transition relation, verified against `stepFn` (two-sided at step level:
   `stepFn_sound`/`step_complete`), and — after this arc — absent from
   every headline statement's closure. The deletion test extends to it:
   deleting `Rel.lean` must not change what any headline theorem *says*.
   (This INVERTS the pre-reshape framing "relational semantics = the proof
   authority, interpreter = its test implementation"; see §Supersessions.)
3. **Termination is a first-class interpreter-level notion.**
   `Terminates P s := ∃ N, ∀ fuel ≥ N, ∀ choices, execStmt … = .ok …`
   (uniform bound is right: branching is finite). The headline default is
   the PROVEN-termination (total-correctness) form
   `pre → Terminates ∧ post`; the user's assumed-termination form and the
   nontermination dual (`∀ fuel, fuel-out`) are supported cases. Rationale
   for the default: assumed termination re-admits the vacuity class
   (a diverging wrong program satisfies the assumed form), and proving the
   stronger thing has repeatedly forced honest side conditions out of the
   machine (the `< 2^63` representability bound).
4. **Safety restates interpreter-side.** `Progress` becomes "for all fuel
   and choices, `execStmt` returns only `.ok` or fuel-exhaustion — never
   stuck, never unrecovered panic". Requires splitting fuel-exhaustion
   from genuine stuckness in `GoError` (today both are `.stuck`,
   distinguished only by message text). Invariance (`GoInvariant`)
   restates over `stepFn` iterates. Honesty note kept from the
   conversation: intermediate-state properties are beyond ANY differential
   oracle (Go does not expose our configurations); stating them over
   `stepFn` means they rest on the *tested* presentation of the model.
5. **Concurrency posture (forward decision, not this arc).** The `Choices`
   stream in `sem`'s signature is the scheduler hook; "∀ schedules" is the
   ∀-choices quantifier statements already carry. Fork/join specs stay
   pre/post over `sem`. The differential oracle weakens from equality to
   MEMBERSHIP (Go exhibits one schedule per run; we admit a set) — the
   concurrent corpus must be designed around that from day one.

## Slices

0. **This document + the living-doc scrub** (same commit): AGENTS.md trust
   chain, roadmap.md strategy bullets, CLAUDE.md audit-dimension wording,
   doctrine doc extension. Dated pre-reshape notes stay as historical
   record — they are records, not guidance.
1. **The termination-discharge SPIKE (front-loaded — the arc's main
   risk).** Kernel-evaluate `execStmt` to `.ok` on the pinned lowerings
   (no `native_decide` — banned in proof-facing code; this is honest
   kernel reduction, `rfl`-class). Measure cost golden → recover → quorum
   → committed-index-real. If tractable: `Terminates` discharges by
   computation. If not: fallback is a steps-bounded variant of the walk
   machinery (symbolic, constructive fuel bound) — and knowing which world
   we are in reshapes slices 3–5, hence spike first.
2. **`fuelOut` refinement.** Distinct fuel-exhaustion error (or outcome) in
   the core; differential-neutral by intent; corpus classification cases
   FIRST (guardrails-first), then `--diff`.
3. **The named notions.** `Terminates`, the total `GoSpec` variant, the
   assumed-termination derived form, interpreter-side `Progress`, the
   error-direction correspondence lemma (execStmt stuck/panic error ⇔
   reachable stuck/panicked config) proving old-Progress ↔ new-Progress.
4. **Relation eviction.** Invariance over `stepFn` iterates; every headline
   statement relation-free; statement-TCB gate extended to enforce
   RELATION-freedom exactly as it enforces Iris-freedom (module-of-origin
   check on `Rel`/`Correspondence` proof modules … precise module list
   fixed during the slice).
5. **Retrofit + re-certify.** The designated family upgraded to total form
   where the slice-1 answer makes it payable; unconditional negative twins
   landed; Audit gates updated; **Comparator landmark run mandatory**
   (designated statements change) before the merge ask.

## Build log

- **Slice 1 spike — VERDICT (2026-08-03): tractable after a bounded core
  restructure.** Phase A (compiled): all four pinned programs terminate
  with correct readouts (recover→7, oneKnown→12, threeAll→6, allConfig→6)
  at fuel ≤ 4000, milliseconds. Phase B (kernel `rfl`): stuck — `#reduce`
  tracing found `Acc.rec`, i.e. well-founded recursion, which never
  reduces definitionally. Environment scan of every `GoLean.*` constant
  for `WellFounded.fix`/`Acc.rec`/`._unary` found the COMPLETE
  kernel-irreducible set is four definition families:
  `Ty.mentionsUnsupported`, `defaultValueFuel` (mutual),
  `normalizeValueForTyFuel` (mutual), `valueEqFuel` (mutual) — every one a
  bounded type/value helper, none of them `stepFn`'s spine. Fix: uniform
  depth-structural recursion (`| d+1 => … d` on an explicit Nat), which
  the kernel reduces; signatures preserved via the existing fuel-constant
  wrappers; behavior change confined to how fast internal resolution
  depth is consumed (differential validates neutrality). This is the
  CLAUDE.md "prefer structural recursion so the proof direction stays
  reachable" principle cashing out, three weeks after it was written.

## Exit criteria

- `Terminates` and the total-correctness form exist, with the user's
  assumed-termination form derivable as a special case.
- At least the summit family (`quorumOneKnown*`, `quorumThreeAll*`,
  `committedIndexAll*`, recover, golden) is total-correctness or has a
  recorded reason why not; unconditional negative twins proven for
  whatever the spike makes payable.
- Zero headline statements reference `Rel.*` modules; the statement-TCB
  gate enforces it; `Rel.lean` is deletable-without-meaning-change,
  mechanically.
- `scripts/ci` green throughout; differential 873/873 (plus new fuelOut
  cases); Comparator fresh-clone PASS on the upgraded Challenge.
- The spike's cost numbers and the tractability verdict are recorded here.

## Supersessions (the old framings, edited out in this commit)

| doc | old framing | new |
|---|---|---|
| AGENTS.md trust chain | "relational semantics (the proof authority)"; interpreter as the differentially-validated feeder | interpreter (`stepFn`/`execStmt`) is the semantic authority AND the statement language; relation is proof infrastructure proven equivalent |
| roadmap.md strategy | "proof-facing semantics should be relational, with the executable interpreter treated as a differential-testing implementation of that relation"; "keep the relation broader than the interpreter" | inverted: statements over the interpreter; relation tracks the interpreter exactly (two-sided step correspondence); implementation latitude lives in the `Choices` stream |
| CLAUDE.md audit dimension | "GoCore's machine and relation are the trust surface" | the interpreter is the trust surface; the relation is proof infra whose divergence from the interpreter is a proof-layer bug (still audited — but as correspondence, not as authority) |
| tcb-doctrine doc | deletion test named Iris only; statement ladder had a "relation-quantified" rung | deletion test covers Iris AND the relation; the relation-quantified rung is deprecated, eliminated by this arc |

Dated notes (2026-07-19/20/22 pipeline/end-state/invariant notes, BUGS.md
prose) retain the old framing as historical record of what we believed
then; they are superseded by this document and say nothing normative.
