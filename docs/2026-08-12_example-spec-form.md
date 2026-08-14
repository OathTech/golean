# The example spec form — design note + slice-1 checkpoint packet (2026-08-12)

Status: PROPOSAL for the user checkpoint (verified-examples arc slice 1;
charter: `docs/2026-08-12_verified-examples-arc-charter.md`). The
exemplar is BUILT — iterative fib, proved end-to-end in the proposed
form (`proofs/GoLeanProofs/Examples/Fib.lean` over
`Corpus/coverage/exec/examples/fib/main.go`) — so every option below is
judged against a concrete object, not a sketch. The user decides the
form here before slice 2 scales it.

Scope honesty (the charter's two-questions separation, quoted): "this
arc answers USABILITY: can the reasoning layer carry natural,
human-readable specs through real programs? … all-green here is claimed
as usability evidence only, never as machine-hardening evidence." Every
theorem in this note is a usability exhibit.

## §1 The program

Canonical Go, exactly what a programmer writes — a loop, two locals,
the multi-assign idiom:

```go
func fib(n uint64) uint64 {
	var a, b uint64 = 0, 1
	for i := uint64(0); i < n; i++ {
		a, b = b, a+b
	}
	return a
}
```

Differentially green against `go run` on 6 rows (n = 0, 1, 2, 10, 93,
94 — the last one PAST the overflow boundary, oracle-confirming the
mod-2^64 wrap). The proof subject is the frontend's ACTUAL lowering,
pinned by `scripts/check-golden` (`baselines/golden/fib-lowered.repr`),
so "the theorem is about this Go file" is a checked chain, not a claim.

## §2 THE PROPOSED HEADLINE (decision object) — SUPERSEDED by §11

The headline form below is the slice-1 proposal, kept as the record of
what was decided and why. The FINAL form is the harness ruling in §11
(user, 2026-08-13): headlines run the three-phase Go harness through
`runFunctionWithContextM` from an empty heap and observe only returned
values — no `execStmt`, no `loadLoc` cell readback, no `fibSeed`/`fibEnv`
in the statement. The name `fib_ok` survives the move and now denotes the
harness theorem, so read every occurrence below as the pre-pivot subject.

```lean
theorem fib_ok (n : Nat) (hn : n ≤ 93) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel fibEnv fibSeed ch (fibCall n) = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int (fibSpec n) .uint64)
```

read as: *for every `n ≤ 93` (the largest argument whose Fibonacci
number fits in uint64), running `$callres = fib(n)` completes
normally — no panic, no deadlock, no stuck state, no fuel exhaustion
past one bound, at every nondeterminism-choice stream — and the result
cell holds exactly `fibSpec n`*, where `fibSpec` is the in-module
mathematical reference:

```lean
def fibSpec : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSpec n + fibSpec (n + 1)
```

Beside it, the full-domain TOTAL companion (also shipped; upgraded
from run-conditioned at slice 1.5, when the fuel-measure rule paid the
termination debt — §5c):

```lean
theorem fib_total (n : Nat) (hn : n < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel fibEnv fibSeed ch (fibCall n) = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩)
            = .ok (.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64)
```

*for every value of the Go argument type, execution completes normally
and returns `fibSpec n % 2^64`* — machine-integer honesty (FD-E3):
what Go's wrapping arithmetic actually computes past n = 93. The
run-conditioned readout half remains available as `fib_wraps_seeded`.

## §3 The latitude points — options and recommendations

### L1 — how "no errors / completes" is stated

- **(a) The ∃N-∀fuel≥N idiom, inline** (BUILT): completion at the
  `.normal` terminal past a fuel bound, every choice stream, as a plain
  first-order formula over `execStmt`. Every error class is excluded by
  the `= .ok (.normal …)` equation itself: panic (`.error .panic`),
  deadlock (`.error .deadlock`), stuck/unsupported/internal (`.error
  …`), fuel-out (`.error .fuelOut`), and non-`.normal` completions —
  the interpreter returns exactly one of these, so one equation says
  "none of the bad ones". This is the house `TotalReadout` shape
  (TotalPins precedent), statement-TCB-minimal.
- **(b) A fuel-free named wrapper**: define e.g.
  `CompletesNormallyWith env σ prog (v : GoValue)` packaging (a), state
  `fib_ok` as `∀ n ≤ 93, CompletesNormallyWith … (fibCall n) (.int
  (fibSpec n) .uint64)`. Reads shorter; costs one definition between
  the reader and the interpreter (the reader must open the wrapper to
  see what "completes" means — the statement-TCB walk gains a hop).
- **(c) `Terminates`/`TerminatesNormally` vocabulary**: reuse the
  Surface defs. Same hop cost as (b), and those defs quantify slightly
  differently (state-level, not readout-conjoined), so the headline
  would still need the conjunction.

**Recommendation: (a).** The gallery's whole point is that a reader can
check the claim against base definitions; the ∃N/∀fuel/∀ch spelling is
the honest price of fuel-indexed executability, and it is teachable in
one sentence ("with enough gas, however the scheduler chooses"). If the
user prefers (b) for surface readability, the wrapper should live in
`Surface.lean` and every example use it uniformly — a cheap slice-2
retrofit; the proofs do not change.

### L2 — the domain and the overflow boundary

- **(a) Bounded exact-value total claim** (BUILT, proposed headline):
  `∀ n ≤ 93 … = fibSpec n`. The bound IS the mathematics — fibSpec 93
  is the last Fibonacci number below 2^64 (the module proves
  `fibSpec_lt_of_le_93` from a linear-time pair evaluator, no
  exponential unfolding) — so the domain condition teaches the overflow
  boundary instead of hiding it.
- **(b) Full-domain wrapped claim** (BUILT, as `fib_wraps_seeded`):
  `∀ n < 2^64 … = fibSpec n % 2^64`, run-conditioned. The genuinely
  ∀-input symbolic result — one WP proof covers 2^64 inputs; nothing is
  enumerated. Weaker on the completion side (§4's debt), stronger on
  domain.
- **(c) Only one of the two.** Rejected as less honest: (a) alone
  hides what happens past the boundary; (b) alone hides that the
  bounded claim is total and exact.

**Recommendation: ship BOTH, (a) as the gallery headline with (b)
directly beneath it.** They answer the two questions a reader actually
asks ("does it compute Fibonacci?" and "what about overflow?").

### L3 — how the input is quantified

The input enters as the call's literal argument — `fibCall n =
$callres = fib(n)` with `.intLit n .uint64` — the SAME convention the
differential harness uses to call subjects with args (`cases.tsv`
`args` column), so the theorem quantifies exactly the thing the oracle
tests. The ∀ binds a `Nat` at the Lean level; the driver statement is a
function of it; seed and environment are fixed. Alternatives
considered: quantifying over the seed heap (an input CELL read by the
program) — rejected for v1: it models mutable input state, not
argument passing, and drifts from the harness convention;
`GoFuncSpec`-style quantification (any heap, any frame, any target
cell) — the WP layer (`fibGoSpec`) already delivers most of this
frame-closure internally; surfacing it in the headline costs
readability for generality no gallery reader asked for. The headline
stays at the seeded driver (the differential's exact configuration);
the frame-closed `GoSpec` remains available beneath as `fibGoSpec`.

### L4 — readability devices

- Naming: `fib_ok` (the total claim), `fib_wraps_seeded` (the boundary
  claim), `fibSpec` (the mathematics). Verb-ish suffixes over
  jargon — proposal: `<example>_ok` / `<example>_wraps` as the
  slice-2 convention.
- The statement vocabulary is deliberately tiny: `fibEnv` (one
  binding), `fibSeed` (the pinned program + one zeroed cell),
  `fibCall n` (the driver). Three two-line defs a reader can inhale;
  everything else in the statement is the interpreter itself.
- A `VerifiedExample` bundling structure (program + spec + proof as a
  first-class object the gallery renders from): NOT built. It adds a
  layer between reader and theorem for rendering convenience the
  gallery script can get from naming conventions. Revisit at slice 3
  (the gallery build) if rendering wants it; the checkpoint should not
  buy machinery ahead of its consumer.
- Docstring convention (BUILT, propose as standard): module docstring
  carries the English claim + the scope-honesty paragraph; the headline
  theorem's docstring is the one-sentence English reading.

### L5 — the termination cost — SUPERSEDED at the checkpoint (slice 1.5)

The slice-1 build discharged the headline's completion half by kernel
enumeration (94 `allStreamsOk` runs, ≈2:15 per proofs build) and this
section originally presented pay/trim/build-symbolic options. The
checkpoint RULING (2026-08-12): **enumeration is banned as a proof
method, corpus-wide** — every theorem in the examples corpus is
symbolic in its inputs; kernel enumeration is per-instance evidence
only (corpus oracle rows). The enumeration is DELETED and the symbolic
machinery was built in-slice: the fuel-measure rule family (§5c).
Measured delta: the fib module built in **223 s** with the enumeration
and builds in **≈3 s** with the symbolic proof — the 2:15 vanished,
and the claim WIDENED (completion now covers the full uint64 domain,
so `fib_total` — full-domain total correctness — ships where slice 1
recorded a debt).

## §4 Foundation debt recorded (charter FD-E3 fallback clause)

**Symbolic (∀-input) termination — PAID at slice 1.5** for
measured-loop shapes: the checkpoint ruling promoted this debt to
in-slice work, and the fuel-measure rule family (§5c) now discharges
`Terminates` symbolically — fib's completion covers the full uint64
domain (`fib_total`), no enumeration anywhere. What REMAINS owed in
this direction: recursion (non-loop) termination, nested-loop
composition sugar (the rule composes manually today), and tactic
packaging of the segment/cleanup boilerplate (a golean-wp family,
§5b.1). Consumers: slice 2's loop examples use the rule as-is; the
width arc's re-proof inherits the same machinery.

**The `$forFirst` desugar tax** (reasoning friction, recorded for the
slice-3 friction list): the frontend lowers EVERY `for` loop — even
condition-only `for i < n` — through `while true { if $forFirst … ;
if cond {} else { break }; body }`. Consequences: loop proofs pay ~4×
the machine steps per iteration, the invariant carries the flag cell
and a lagging counter, and `wp_while_inv` (normal-completion bodies)
can prove NO frontend-lowered loop — the break-aware
`wp_while_inv_break` is now the real loop rule (shipped this slice,
witnessed by fib). A frontend lowering that emits `.while cond body`
directly for condition-only loops would simplify every future loop
proof — recorded as input for a frontend arc, not changed here.

## §5 What the ∀-input demand required (new general machinery, all
same-commit-witnessed by fib per the non-vacuity rule)

- `wp_while_inv_break` (`Laws/Loop.lean`) — the break-aware
  while-invariant law (Goose `wp_forBreak_cond`'s break leg): body may
  re-establish the invariant at the back edge OR break establishing a
  break postcondition; the two continuations are handed to the body as
  an additive conjunction; the exit receives `I false ∨ Q`.
  `wp_while_inv` remains as the `Q := False` corner.
- `wp_break`, `wp_breaking_seq` (`Laws/Control.lean`),
  `wp_breaking_loop` (`Laws/Loop.lean`) — the `break` unwinding spine
  (pure-det lifts; nothing could walk a `break` before).
- `wp_assign_many_start` (`Laws/Eval.lean`) — the `.assignMany` spine
  entry (`a, b = b, a+b`); the rest of the multi-target walk was
  already general.
- `wp_call_enter₁₁` + `bindParams₁` (`Laws/Call.lean`) and
  `wp_alloc_step₂` (`Lifting.lean`) — frame entry at the one-argument/
  one-result arity (the ∀-input argument-passing shape).
- Everything else — the invariant-carrying loop walk, the ∀-n `GoSpec`
  through `goSpec_of_wp`, the seeded readout composition — was carried
  by the EXISTING kit unchanged. The `MachineWf` side condition, pinned
  per-seed by `decide +kernel` at the golden pins, is proven
  symbolically for the whole family (`fibSeedWf`: the literal's
  `locSup` is 0 for every n).
- The proof-friction that did NOT become general machinery this slice
  is the seed work list of the golean-wp tactics layer — §5b.

## §5b The golean-wp tactics layer — prior art and growth plan

Supersession note (2026-08-14): the growth plan below assumes the WP
route as the proof method. §11's method freeze settled that differently —
the shipped examples are proved by DIRECT machine-step segments plus
induction, with the WP/Iris layer witnessed separately and deliberately
not consumed in the headlines. So this section records prior art and an
option that was not taken, not the arc's plan; nothing in it was built.

Prior art (user-provided mid-slice, 2026-08-12): `deps/brick-wp` — the
user's own Rocq WP-tactics library for BRiCk/cpp2v C++ proofs
(`theories/WpTactics.v`, ~1900 lines in Layer-0 entailment lemmas /
Layer-1 atoms / Layer-2 composites; `tests/` fixture proofs;
`docs/2026-08-11_industrialization_arc.md` the growth plan). Its core
lesson for this arc: a (more heuristic) WP tactics library built
ALONGSIDE the core reasoning pays off, and its families must come from
a real consumer's proof friction — never speculative design. This
section records the plan; nothing beyond fib's minimal general lemmas
is built this slice (the exemplar + form remain the deliverable).

**1. Consumer-driven growth — the fib proof is the first consumer.**
Its friction list IS the library's seed work list:

- the between-laws modality dance (`fupd_intro`/`inext`/`fupd_intro`/
  credit-drop) — ~70 occurrences; kept as a LOCAL macro (`idance`)
  this slice, the obvious first library atom;
- env-lookup discharge (`simp [LocalEnv.lookup, LocalEnv.declare,
  LocalEnv.pushScope, Scope.lookup]`) — ~20 occurrences, one atom;
- the single-assign spine walk at non-int-literal RHS (bool literal,
  var-to-var) — walked by hand five times; `wp_assign_lit` wants
  `wp_assign_bool_lit` / `wp_assign_var` composite siblings;
- the store-discharge idiom (`storeLoc_int_cell` + normalize collapse)
  — a finisher atom;
- the loop opener (their Wave 5b, ours verbatim): applying
  `wp_while_inv_break` costs ~30 lines of fixed boilerplate — the
  `boolLit true` condition walk, the entry-instance splits, the
  `I false ∨ Q` exit elimination. A `go_loop_invariant I Q` tactic
  leaving exactly (1) entry, (2) body, (3) exit-from-Q goals is the
  highest-value family for slice 2 (every example with a loop pays
  this).

**2. The `stmt_spec` shape (their Wave 5a).** Their industrialized
form — `stmt_spec s P P' := ∀ Q, P ∗ (P' -∗ Q Normal) ⊢ wp s Q`, with
`stmt_spec_seq`/`stmt_spec_frame` composition — is, up to vocabulary,
the house walk shape already: every composed law and both fib segment
lemmas (`wp_fib_body`, `wp_fib_loop_tail`) are continuation-parametric
(`∀ k Φ, cells ∗ (cells' -∗ WP (next k)) ⊢ WP (exec s env k)`). What
we have NOT done is name the shape as a first-class def with reusable
seq/frame lemmas. GoCore's twist, which the fib proof forced: segments
can end at DIFFERENT continuation classes (normal vs `breaking` — the
for-desugar), so our instance of their design question (i) ("should
`P'` be ReturnType-indexed?") is already answered YES:
`wp_while_inv_break`'s body premise is exactly a two-continuation
statement triple, joined by additive `∧`. Recommendation: adopt the
named shape at its FIRST recurrence (slice 2's gcd/binary-search body
segments), with the fib segments retrofit as its witnesses — not this
slice (one consumer is a data point, two is a shape). Their motivation
(2^k operand orderings per statement made per-ordering re-proof
untenable; the triple collapses it to once) becomes ours VERBATIM when
the sequential-width arc widens evaluation-order envelopes — the shape
is future-proof, which is why it should be the slice-2 default rather
than a bespoke per-example lemma zoo.

**3. Goal-guarded dispatch (their batch-4 performance finding).**
Failed statement-level `iApply` typeclass search was 85% of their
`wp_auto` runtime; head-matching each rule on the goal's statement
shape before attempting it cut a consumer rebuild 3:52 → 1:29. Our
`go_walk` already dispatches through a `DiscrTree` over law
conclusions (structurally the same fix), but the v1 resource-threading
policy (`iframe`-based) is exactly where their lesson lands next: the
channel-logic lane's recorded friction flag (P-CL3-5, spurious
`iframe` capture) is the same class — unguarded attempts that
half-match and cost time or misbind. Recorded as a go_walk design
consideration (guard the resource-split attempt on the goal's head
shape; measure before building) — not built this slice.

**4. Fixture-per-family + mechanical coverage.** Their policy: every
tactic family lands WITH fixture tests in the same change, every test
lemma registered in `tests/AuditAssumptions.v` (`Print Assumptions`
per public lemma; the `make audit` target count-matches entries
against the lemma inventory). This is our witness discipline as CI:
their AuditAssumptions registry maps onto `proofs/Audit.lean`'s
`example :=` anchors + `#guard_msgs` axiom pins — with the comparison
honestly cutting both ways: our exhaustive in-build sweep is STRONGER
on axioms (every declaration, not a curated list), their count-match
is stronger on coverage (a family cannot land without its fixture;
our anchors are name-existence tripwires, and witness-citation drift
stays the pre-merge audit's job). Adopted for golean-wp: every tactic
family lands with a fixture walk in the same change, anchored in
`Audit.lean` — the non-vacuity rule extended from laws to tactics.

**5. The untrusted-layer policy.** Their core is a purely untrusted
tactic layer — zero axioms anywhere in `theories/` outside the
quarantined 49-line `TrustedAxioms.v` annex (which their new work
doesn't touch); tactics are method, the kernel checks the output.
Independent convergence with our statement-TCB doctrine and axiom
gate (tactics never appear in statement closures; the classical trio
allowlist; the in-build sweep). golean-wp inherits this posture by
construction: it can only ever make proofs cheaper, never claims
wider.

## §5c The fuel-measure rule family (slice 1.5 — the completion half)

Built at the checkpoint ruling (promoted from §4's parked debt):
`proofs/GoLeanProofs/FuelMeasure.lean`, the symbolic discharge of
`Terminates`, designed as `wp_while_inv_break`'s completion-side twin —
the pair split the loop exactly as the brick-wp `stmt_spec`
convergence (§5b.2) suggested treating statement obligations: the
VALUE half is the Iris invariant walk, the COMPLETION half is plain
induction over the executable.

**Why there is no Iris in the termination half** (ruling, recorded):
standard Iris WP is partial-by-construction — step-indexing/Löb
induction cannot prove termination; iris-lean at our pin has no total
WP (`twp`); the Iris-world alternatives (a twp port, time credits,
Transfinite Iris) are real machinery we do not need, because our
claims are about a fuel-indexed EXECUTABLE function. The split IS the
TCB-grounding principle: Iris stays a proof device for the value half;
completion is boring induction over `execStmtLoop`. A twp port remains
the recorded option if termination-inside-the-logic is ever wanted.

**The rule** (`completesIn_measure_loop`): given a loop-head
configuration and a state family `S : Nat → ExecState → Prop` (the
loop invariant indexed by the REMAINING measure) such that (i) every
`S (μ+1)` state runs one iteration back to the head within `c_iter`
interpreter steps reaching `S μ'` with `μ' ≤ μ`, and (ii) every `S 0`
state completes from the head within `c_exit` fuel, every `S μ` state
completes within `c_iter·μ + c_exit`. Strong induction on the measure;
supporting kit: `CompletesIn` (completion at configuration
granularity), `completesIn_comp` (segment composition),
`stepFnIter_chain`/`execStmtLoop_of_stepFnIter` (fuel-arithmetic
folding), `terminates_of_completesIn` (the `Terminates` bridge).

**The fib instantiation** (the same-commit witness): four run segments
proven by `with_unfolding_all rfl` — pure definitional evaluation of
the interpreter with `n` symbolic, split exactly at the loop's exit
test (the one point control depends on an open term). The
`@[irreducible]` sealing of the value-walk wrappers (de-WF design,
2026-08-03) is why plain `rfl` fails and `with_unfolding_all` is the
documented opt-in; a naive `simp [stepFn]` route measured 2.5 min per
segment, the `rfl` route ≈1.5 s for all four. Measure: `μ = n - m`
(unit decrease); fuel bound `56·n + 113`, verified against the
concrete trace (n=3: 277 steps exactly).

**Instantiation sketches for slice 2** (stated, not built — the
generality check):

- **gcd** (`for b != 0 { a, b = b, a%b }`): measure `μ :=` the
  `b`-value's Nat magnitude. The iteration premise delivers `S μ'`
  with `μ' = a % b < b = μ+1`, i.e. `μ' ≤ μ` — the rule's ≤-decrease
  shape absorbs the NON-UNIT decrease directly; no rule variant
  needed. The per-iteration segments are the same
  `with_unfolding_all rfl` shape (the exit test `b != 0` is the one
  open-term branch). New pure lemmas needed: `%`-wrap arithmetic on
  uint64 (the `unorm` family extended to `emod`), nothing structural.
- **binary search** (`for lo < hi { mid := (lo+hi)/2; … }`): measure
  `μ := hi - lo`; each branch delivers `μ' ∈ {mid - lo, hi - mid - 1}`,
  both `≤ μ/2 < μ+1` — again within the ≤-decrease shape. The segment
  split gains ONE extra open-term branch point (the probe comparison
  inside the body picks the half), so the iteration premise
  case-splits twice — the rule is untouched; the per-example segment
  count grows with the number of data-dependent branches, as expected.

If a slice-2 shape genuinely fails the ≤-decrease form (none of the
listed set should), the named variant to build is a
well-founded-relation-indexed rule (`completesIn_measure_loop_wf`) —
recorded here so the finding has an address.

## §6 TCB-grounding walk for `fib_ok` — SUPERSEDED by §11

The walk below grounds the PRE-PIVOT `fib_ok` (the seeded
`execStmt`/`loadLoc` driver form). It is left exactly as written, as
the record of the discipline; today's `fib_ok` is the harness theorem,
whose closure is walked in the `proofs/Audit.lean` prose for the
verified-examples blocks, and the model walk for the current form is
the isort harness walk in `docs/2026-08-13_verified-examples-scale-out.md`
§6 (no heap vocabulary at all — the verdict is computed in Go).

Statement closure, every identifier to its ground: `execStmt`,
`loadLoc`, `ExecState`, `Choices`, `ExecOutcome.normal`, `GoValue.int`,
`IntKind.uint64`, `Loc.base` — the interpreter and its value
vocabulary (the trust surface, differentially validated);
`fibSeed`/`fibEnv`/`fibCall` — three literal defs over `fibLowered`;
`fibLowered` — GENERATED from the frontend's lowering of the corpus
source, byte-pinned by `scripts/check-golden` (both links);
`fibSpec` — the six-line recursive reference function, in-module;
`Nat`/`Int`/`∃`/`∀`/`%`/`≤` — Lean core. NO Iris, no WP, no relation,
no tactic-layer name in the statement closure (deletion test:
`Examples/Fib.lean`'s statements survive deleting the entire proof
layer; the proofs of course do not). Axioms: classical trio only,
pinned in `proofs/Audit.lean` (`#guard_msgs` on `fib_ok` and
`fib_wraps_seeded`).

## §7 Draft gallery entry (what a user would see) — SUPERSEDED by §11

The draft below predates the harness ruling (§11) and the shipped
gallery. What a user actually sees is `docs/verified-examples.md`, whose
entries print the harness in full and quote every theorem verbatim; the
statement printed below is the pre-pivot seeded-driver form. Kept as the
design record of the entry's SHAPE, which the gallery did inherit.

---

### fib — iterative Fibonacci over uint64

```go
func fib(n uint64) uint64 {
	var a, b uint64 = 0, 1
	for i := uint64(0); i < n; i++ {
		a, b = b, a+b
	}
	return a
}
```

**Claim.** For every `n ≤ 93` — the largest argument whose Fibonacci
number fits in `uint64` — `fib(n)` completes normally (no panic, no
error, no non-termination: with enough fuel, under every
nondeterminism choice) and returns exactly the `n`-th Fibonacci number.
For every `n` in the full `uint64` domain, `fib(n)` completes normally
and returns `fib(n) mod 2^64` — Go's wrapping arithmetic, stated
rather than hidden. Every quantifier is discharged symbolically.

**The theorems** (`proofs/GoLeanProofs/Examples/Fib.lean`):

```lean
def fibSpec : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSpec n + fibSpec (n + 1)

theorem fib_ok (n : Nat) (hn : n ≤ 93) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel fibEnv fibSeed ch (fibCall n) = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int (fibSpec n) .uint64)

theorem fib_total (n : Nat) (hn : n < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel fibEnv fibSeed ch (fibCall n) = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩)
            = .ok (.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64)
```

**Axioms:** `[propext, Quot.sound]` (no `sorry`, no native evaluation, no
extra axioms; corrected 2026-08-14 — the draft said the classical trio,
but the shipped `fib_total` pin in `proofs/Audit.lean` drops
`Classical.choice`, since its derivation goes through no Iris and no
frame layer).

**Ground:** the program in the theorem is the toolchain's pinned
lowering of the Go source above (staleness-guarded); the same source is
differentially tested against `go run`, including the n = 94 wrap.

---

## §9 The memory-quantified form (slice 2a) — SUPERSEDED by §11

The "headlines UNIFY to the memory-quantified form" ruling recorded here
was itself superseded on 2026-08-13 by the harness ruling (§11): the
memory-quantified forms are KEPT, but as the proof-side supporting layer
(`fib_framed`, `reverse_framed`, `minmax_framed`, …), while the headlines
observe a harness run's returned values from an empty heap. Read this
section as the design of that supporting layer.

Form ruling (user, 2026-08-13): headlines UNIFY to the
memory-quantified form — input data + arbitrary disjoint frame, frame
preservation VISIBLE in the statement. Slice 2a designs the frame
structure on one memory-input exemplar (slice reverse) plus the fib
retrofit, and stops for the ruling; 2b scales. Everything below is
grounded in the shipped machinery (`fib_framed` is PROVEN in this
form; the reverse headline is stated against the same derivation
path).

### §9a How the input-in-memory is quantified

∀ over the ABSTRACT data + ∀ over placement, with an abstraction
function tying them to the heap. For slices the crux definition
(proposed corpus vocabulary; built with its first consumer in 2b):

```lean
/-- The heap representation of a Go `[]uint64` holding `xs`: one
backing cell at `base` with the array of wrapped values. The slice
HANDLE the program receives is `sliceVal xs base` — base pointer,
offset 0, length and capacity `xs.length`. -/
def sliceCells (xs : List Int) (base : Nat) : Heap :=
  [(.base ⟨base⟩,
    ⟨some (.array xs.length (.int .uint64)),
     .array ⟨xs.map (fun v => .int v .uint64)⟩⟩)]

def sliceVal (xs : List Int) (base : Nat) : GoValue :=
  .slice ⟨some (.base ⟨base⟩), 0, xs.length, xs.length⟩
```

Options considered: (i) quantify the heap directly and EXTRACT the
list (an inverse function) — rejected: the ∀ reads backwards ("for
every heap that happens to encode a list") and the extraction
function is a worse TCB citizen than the constructor; (ii) **(chosen)
quantify `xs : List Int` (with the honesty bound `∀ v ∈ xs, v` in
uint64 range — or carry `List (Fin (2^64))`-free phrasing via the
bound) and `base : Nat`, and SEED the representation** — the
abstraction function appears once, is 5 lines of first-order
constructor application, and becomes shared corpus vocabulary exactly
like `fibSpec`. Offset/capacity generality (sub-slices) deliberately
starts pinned at `offset = 0, cap = len`; widening is a recorded 2b+
option, not a v1 requirement.

### §9b How the frame is stated

The MECHANISM is the existing `InitialSplit`/`GoSpec` frame closure
(the triple already quantifies every admissible split and returns
`F.sub` at the terminal state). The HEADLINE choices for rendering it:

- (i) **(chosen) pointwise `Heap.lookup` clauses, inline** — the form
  `fib_framed` ships:
  - the framed seed is literally `input-cells :: fr` (list append —
    the decomposition is visible as data, not as a predicate);
  - admissibility is two hypotheses: `Heap.lookup fr <input-locs> =
    none` (disjointness, one clause per input cell) and `MachineWf
    seed config` (well-formedness — a DECIDABLE interpreter-vocabulary
    predicate: allocator bound above every mentioned address, no
    dangling locs);
  - preservation is `∀ a c, Heap.lookup fr (.base ⟨a⟩) = some c →
    Heap.lookup σf.heap (.base ⟨a⟩) = some c`.
  Deletion-test status: CLEAN — `Heap.lookup`, `MachineWf`, `Heap`,
  `HeapCell` are interpreter vocabulary; no `Heaplet`, no `HProp`, no
  `InitialSplit` in the statement closure (they appear only in the
  PROOF). This is the hard constraint met.
- (ii) explicit heap-decomposition equations on the FINAL state
  (`σf.heap = output-cells ∪ fr ∪ fresh`) — rejected: false as stated
  (the heap is an ordered list; allocation interleaves), and fixing it
  needs multiset/permutation vocabulary that fails the readability
  bar.
- (iii) a named `MemorySpec input output frame` predicate (≤5
  first-order lines bundling (i)'s clauses) — genuinely attractive for
  UNIFORMITY once 2b scales (one definition read once, like
  `fibSpec`); costs one definitional hop on the deletion-test walk.
  Recommendation: adopt at 2b IF the ruling prefers the compact
  surface; (i) and (iii) are the same claim, so nothing re-proves.

### §9c What preservation says, and allocation honesty

Preservation = **pointwise lookup preservation** (same address, same
cell — `HeapCell` equality covers both declared type and value, so
this IS "byte-identical" at the model's granularity). NOT claimed:
domain equality of the final heap. The program ALLOCATES (parameter
and result cells at frame entry; `new`/`make`/`append` in general
programs), so the final heap strictly extends input+frame; the honest
statement claims (1) the output cells' contents, (2) every frame
cell's preservation, and says nothing about fresh cells. Available
strengthening (recorded option, not v1): freshness — every address
outside input ∪ frame that is allocated satisfies `na ≤ a` (from
`StateWf`); adds a clause of real content but doubtful gallery value.

**The completion-half gap, priced honestly**: `fib_framed` (and the
reverse headline) are RUN-CONDITIONED over framed seeds. The full
memory-quantified TOTAL form — `∀ frame: completes ∧ value ∧ frame
preserved` — needs termination from EVERY admissible framed seed, and
the fuel-measure segments do not transfer verbatim: allocation
addresses depend on `nextAddr`, which the frame moves, so the
canonical run's `rfl` computations (concrete addresses) become
symbolic-address computations. Two attack routes, both real work,
neither in 2a: (α) hypothesis-parametric segments (the simp route with
address-inequality side conditions — measured ~2.5 min/segment when
tried naively; needs engineering to be affordable); (β) an executable
frame/weakening theorem (run from `H` simulates run from `H ++ F` up
to an address renaming — the general tool, subsumes (α), sizable).
Until one lands, the honest unified headline is: TOTAL at the
canonical placement (`fib_total`) + framed run-conditioned
(`fib_framed`); equivalently "it completes; and however you frame it,
any completion delivers the value and touches nothing else". RULED
(user, 2026-08-13): route (β) — the executable frame theorem (command
locality up to fresh-address renaming); design of record
`docs/2026-08-13_executable-frame-theorem.md`, which also cross-records
the NPDRF/P-S4NP-2 heap-iso convergence.

### §9d The English rendering convention

*"For any list `xs` (of uint64 values), wherever it lives in memory,
with anything else present: `reverse` completes normally, the slice
then holds `xs` reversed, and no other memory is touched."* — the
three clauses map 1:1 to (input ∀ + placement ∀ + frame ∀), the
completion+value conjunction, and the pointwise preservation clause.
For argument-input examples the middle clause degenerates: fib reads
*"…with anything else in memory: fib(n) completes normally, returns
fib(n) mod 2^64, and touches nothing but its result cell."*

### §9e The reverse exemplar — PROPOSED headline (2b proves it)

Canonical Go (`Corpus/coverage/exec/examples/reverse/main.go`, 5/5
differential rows green incl. odd/even lengths, singleton, empty, and
an int64-boundary value):

```go
func reverse(s []uint64) {
	for i, j := 0, len(s)-1; i < j; i, j = i+1, j-1 {
		s[i], s[j] = s[j], s[i]
	}
}
```

```lean
theorem reverse_ok (xs : List Int) (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64)
    (base : Nat) (fr : Heap) (na : Nat)
    (hb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hwf : MachineWf
      { functions := reverseLowered.funcs,
        heap := sliceCells xs base ++ fr, nextAddr := na }
      (.exec (reverseCall xs base) [] .stop)) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel [] (reverseSeed xs base fr na) ch
            (reverseCall xs base)
          = .ok (.normal σf, ch')
        ∧ Heap.lookup σf.heap (.base ⟨base⟩)
            = some ⟨some (.array xs.length (.int .uint64)),
                .array ⟨xs.reverse.map (fun v => .int v .uint64)⟩⟩
        ∧ ∀ (a : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨a⟩) = some c →
            Heap.lookup σf.heap (.base ⟨a⟩) = some c
```

(`reverseCall xs base` = the driver `reverse(s)` with the slice handle
`sliceVal xs base` as the literal argument — the same
argument-as-quantifier convention as fib, lifted to a memory-backed
value. Modulo the §9c completion split: the ∃N completion clause holds
at the canonical placement; the framed instances are run-conditioned
until (α)/(β).)

Measure-rule fit: `μ := j - i` decreases by 2 per iteration — within
the ≤-decrease shape, no variant needed. The 2b build list for the
value half, discovered against the machinery: slice-index WP laws do
NOT exist yet — needed are the index-read law (`s[i]` evaluation:
handle load, backing-cell read, bounds check), the index-target store
law (`s[i] = v`: `resolveChain`/`indexTargetLoc` through the backing
cell, bounds check at store), `len(s)` evaluation, and the multi-assign
walk at INDEX targets (the spine is general; the target-shape plans
gain index steps). Plus pure `List.set`/`reverse` surgery lemmas for
the two-pointer invariant. Termination additionally reuses the §5c
segment technique with the backing-cell content symbolic (a list — the
loads/stores hit one concrete address, so the `rfl` route carries).

**STATUS 2026-08-13: PROVEN** (`Examples/Reverse.lean`, `reverse_ok` —
∀-frame ∀-placement TOTAL; the frame theorem closed the completion
split, consumed at the input-RELOCATING `ShiftSpec` renaming, so the
`base` quantifier transfers from the canonical placement with nothing
re-run). Build-list outcomes, recorded: (i) the three slice laws exist
and are witnessed (`Laws/Slice.lean` + `SliceMem.lean`); the
multi-assign-at-index-targets item needed NO new law — the tgtOpK
spine laws are shape-generic, and `wp_swap_witness` exercises the
index-shape instances. (ii) The reverse proof itself took the DIRECT
machine-step segment route for BOTH halves (one strong induction on
`(len-1) - 2m` pins the exact loop-head state, array contents
included, so value + completion come from the same segments); the WP
laws stand as witnessed general machinery, deliberately not consumed
by reverse. (iii) Statement delta vs the block above:
`hlen : xs.length < 2^63` ADDED — with completion in the statement the
draft is FALSE past Go's `int` domain (the driver's `len` literal
wraps negative; slice-bounds panic). The §5c `rfl`-segment prediction
held with one refinement: bounds checks and the backing-array
element lookup are data-dependent branch points INSIDE an iteration,
so each iteration is a chain of `rfl` sub-segments glued across four
single branchy steps (two `indexGet` applies, two chain stores),
discharged by the `SliceMem` executable facts.

### §9f The fib retrofit — old vs new, verbatim

OLD (slice 1, canonical seed only — statement unchanged, still
shipped):

```lean
theorem fib_total (n : Nat) (hn : n < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel fibEnv fibSeed ch (fibCall n) = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩)
            = .ok (.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64)
```

NEW (slice 2a, SHIPPED and proven — the memory-quantified companion):

```lean
theorem fib_framed (n : Nat) (hn : n < 2 ^ 64) (fr : Heap) (na : Nat)
    (hfr : Heap.lookup fr (.base ⟨0⟩) = none)
    (hwf : MachineWf
      { functions := fibLowered.funcs,
        heap := (.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩) :: fr,
        nextAddr := na }
      (.exec (fibCall n) fibEnv .stop)) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel fibEnv (fibSeedFr fr na) ch (fibCall n)
        = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩)
          = .ok (.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64)
        ∧ ∀ (a : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨a⟩) = some c →
            Heap.lookup σf.heap (.base ⟨a⟩) = some c
```

English: *for every n, with ANYTHING else in memory: any normal
completion returns fib(n) mod 2^64 and touches nothing but its result
cell.* The completion clause stays with `fib_total` per §9c; unifying
them into one framed-total statement is exactly what the (α)/(β)
ruling decides.

## §10 The map form (scale-out slice 2c, 2026-08-13 — designed BEFORE
proving, per the arc instruction)

The word-count example (`Corpus/coverage/exec/examples/wordcount/`,
subject `maxCount`: build `counts : map[uint64]uint64` from a `[]uint64`
of word-ids, then `for _, c := range counts` take the max count) is the
corpus's first map-heap example. Its two design questions, settled here:

### §10a The map-in-memory vocabulary (the `sliceCells` analog)

A Go map value is a HANDLE (`GoValue.map ⟨some dataLoc⟩`) to a data
cell holding `GoValue.mapData entries` — an insertion-ordered
`Array (GoValue × GoValue)`. The proposed vocabulary, on the
`map[uint64]uint64` fragment (mirroring `sliceCells`'s `[]uint64`
scoping):

```lean
/-- The heap representation of a `map[uint64]uint64` holding the
association list `kvs` (insertion order = list order): one data cell at
`base`. The handle the program carries is `mapVal base`. -/
def mapCells (kvs : List (Int × Int)) (base : Nat) : Heap :=
  [(.base ⟨base⟩,
    ⟨none, .mapData ⟨kvs.map (fun kv => (.int kv.1 .uint64, .int kv.2 .uint64))⟩⟩)]
def mapVal (base : Nat) : GoValue := .map ⟨some (.base ⟨base⟩)⟩
```

TWO abstraction levels, deliberately separated: the heap layer speaks
`List (Int × Int)` WITH its insertion order (the machine's mapData is
ordered — a determinized representation the reasoning must see through,
not deny); the SPEC layer must be order-independent (below). Duplicate
keys are excluded by a `kvs.Nodup`-on-keys side condition where the
vocabulary is consumed (mapAssign maintains it).

### §10b The order-independence discipline (the teaching point)

`for … range m` consumes ONE `Choices` pick per iteration
(`stepFn`'s `mapIterK` arm: `choices.consume remaining.size`, erase the
picked index, allocate fresh key/value cells, run the body). The ∀-ch
quantifier every headline already carries therefore does REAL work on a
map example — the claim holds at EVERY iteration order, which forces
the spec function to be an order-independent fold. For word-count:
`maxMultiplicity ws := the max over v ∈ ws of count v ws` (0 for the
empty list) — commutative-idempotent max, provably invariant under the
pick. A spec that read "the first key with maximal count" would be
UNPROVABLE (too strong: different orders yield different firsts) — and
that unprovability is the design working, not failing: the envelope
rejects order-dependent claims. Proof shape for the range half:
induction on `remaining.size`, ∀ remaining (as a list/array), ∀ acc
with `acc = max over consumed`, ∀ ch — the pick is destructured through
`Choices.consume` (`idx < size` from its `% bound` contract), the body
re-establishes the invariant at `remaining.eraseIdx idx`, and max-fold
lemmas (`max over (erase idx) ∪ {picked} = max over all`) close the
step. No enumeration of orders anywhere — the ban binds.

### §10c What the range loop costs the segment technique (priced,
recorded as the slice's known obstruction)

`bindIterVars` ALLOCATES two fresh cells per iteration, so `nextAddr`
grows by 2m across the loop and every in-loop address is symbolic in
the iteration count — `with_unfolding_all rfl` segments (which need
address-concrete heap lookups) do NOT carry the range body the way they
carry fib/gcd/reverse bodies. The (a)-route from §9c applies at loop
granularity: the body's ~10 steps become HAND-GLUED conditioned steps
(stepFn unfoldings + `Heap.lookup`/`storeLoc` facts at symbolic
addresses, closed by `beq_self` simp — not rfl). Priced at roughly the
§9c α-route cost per iteration segment. The counting half
(`counts[w]++`) additionally needs executable facts for
`mapAssignValue`/`mapEntryIndex?` on the `map[uint64]uint64` fragment
(the `storeTarget_slice_u64` analogs) with an assoc-list update spec.

### §10d Scope ruling for slice 2c (recorded honestly)

The corpus program, oracle rows (6, incl. all-same / two-pairs /
empty), and pinned lowering LANDED with the scale-out infra commit;
the vocabulary and proof are staged AFTER the four slice/argument
examples integrate, and if the session ends first, the word-count
headline is recorded as NAMED FOUNDATION DEBT (consumer: the gallery's
map row; the §10a-c design is the executable plan) rather than forced
through — the charter's fights-the-form rule applied to schedule
rather than shape.

## §11 THE HARNESS RULING (user, 2026-08-13 — FINAL headline form;
supersedes §2/§9 as the USER-FACING form; §9 demotes to
proof-side/reserve)

Ruled by the user 2026-08-13 (explicit agreement on the full form;
relayed through the operator — quoted fragments below are the user's
words as relayed; the harness sketch is reconstructed to the agreed
schema and marked so).

**The form.** Every example ships ONE fixed Go harness function with
three phases:

```go
// reconstructed to the agreed schema (fib_harness is the user's own
// sketch shape): setup — call under test — test.
func fib_harness(n uint64) uint64 {
	// setup_fib_state: builds all memory the test needs from the
	// parameters (pre-allocation context; empty for fib)
	r := fib(n) // the call under test
	// test_fib_state: memory ANALYSIS in Go — readbacks and checks
	// fold into the returned values (identity for fib)
	return r
}
```

The Lean statement observes ONLY termination + returned values,
through the machine's native function entry:

```
∀ x y … (well-typed, pre) → ∃ N, ∀ fuel ≥ N, ∀ ch : Choices,
  runFunctionWithContextM fuel Γ fns harness #[x, y, …] ch
    = .ok ⟨#[v, …]⟩  ∧  post(v, …, x, y, …)
```

(`runProgramM` for whole-program/globals harnesses.) Postconditions
are over RETURNED VALUES only — either returned data = a spec
function of the inputs, or a Go-computed verdict value; per-example
choice, preferring returned data where arity permits.

**The three key properties (rulings, not preferences):**
1. **No AST splicing / program families** — quantification is over
   instantiated `GoValue` ARGUMENTS at the call boundary, the
   machine's native mechanism; the entry builds the empty-heap state
   itself.
2. **No Lean-side heap readback in headlines** — no `loadLoc`, no
   cell/seed/env vocabulary in any user-facing statement:
   `test_*_state` does the memory analysis IN GO, inside the verified
   footprint. In the user's words: at the top level *"we do not have
   any memory reasoning at all."*
3. **No frame clauses anywhere user-facing** — the implicit framing
   property (the harness touches only what it allocates) is INHERENT
   in the empty-heap entry (the user's implicit-framing remark, as
   relayed).

**The CBMC parallel** (user's, as relayed): the harness style is the
bounded-model-checking harness discipline — a closed test program
quantified over its inputs — with our ∃N-∀fuel-∀ch totalization on
top.

**Concurrency extension** (user, as relayed): a fork harness under the
same ∀ch quantifier; *"the reasoning necessary may be deeply complex
(that's Iris) but our top level spec is very boring."* The boring top
level is the point: Iris stays proof-side machinery under an
observable-return headline.

**Variable-size inputs (∀ slice contents — DESIGNED, NOT BUILT; this
arc uses scalar-parameterized setup loops instead).** The designed
mechanism is a CHOICE-CONSUMING INPUT PICK (the CBMC `nondet_*`
pattern): a setup-phase primitive that consumes `Choices` picks to
materialize input data, putting the input under the headline's ∀ch.
DIFFERENTIAL OBLIGATION recorded with it: the pick needs a go-run
counterpart (args/stdin-driven instantiation) so the oracle can
witness picked inputs — an enveloped site with a lower-bound story,
like every Choices site. Not built this arc (ruling (d)); until then,
setup loops parameterized by scalars (length, seed) give input
FAMILIES, honestly weaker than ∀xs, recorded per example.

**The known horizon (user addendum, 2026-08-13, near-verbatim):**
*"this will eventually get tougher when we need ghost variables, which
is the pain of this exact style. No free lunch, basically. But I think
this is a good abstraction FOR NOW as we build."* The boundary, drawn
precisely: ghosts that are computable observation-only HISTORY are
harness-materializable (setup snapshots / shadow copies — real Go,
part of the verified footprint); the genuine wall is ghosts that must
live INSIDE the code under test — prophecy variables, linearization
witnesses, mid-run safety claims not observable at the return
boundary — i.e. exactly fine-grained concurrency claims. Escape hatch
when reached: proof-side Iris ghost state remains untrusted method;
the FORM is revisited only when a CLAIM itself is not
return-observable. Scope line: good abstraction for now, revisit at
that horizon.

**Method-investment disposition (user, 2026-08-13, agreed — recorded
near-verbatim):** *"the half-built separation logic theory over the
interpreter may be redundant if we expect Iris to do all our heavy
lifting"* — resolved: the interpreter-level SL theory is FROZEN at
what is built; no further frame/WP-composition buildout. What stays,
and why: the **allocator-independence quotient** (a machine FACT — it
discharges the doctrine's re-envelope obligation and is the coverage
argument for synthesized pre-states) and the **fuel-measure kit +
direct segment/entry-glue method** (sole owner of the TOTALITY half of
headlines: iris-lean at our pin has no `twp`, Iris WP is
partial-by-construction). Iris is the designated heavy-lifter for
concurrency. If sequential examples ever outgrow direct reasoning, the
move is porting `twp` — not growing the bespoke layer.

**Status of the §9 memory-quantified form:** PROOF-SIDE / RESERVE.
The committed memory-quantified theorems (fib_framed/fib_total_framed,
reverse_ok, gcd_ok, minmax_ok, search_ok, isort_ok pre-restatement)
and the `sliceCells`/frame vocabulary remain as the supporting layer
(the canonical-run segments and inductions carry every harness
headline; the frame theorem remains the ∀-placement engine
proof-side). User-facing restatement over `runFunctionWithContextM`
follows per example; old cell-readback headline shells are deleted
AFTER their restatements land (ruling (a)).

## §8 Parked / out of scope (recorded)

- Machine/frontend changes (must-park): the `$forFirst` desugar tax
  (§4) goes to a frontend arc; no Choices sites touched; no
  interpreter edits.
- Designation: `fib_ok`/`fib_wraps_seeded` are designation CANDIDATES
  (statement-TCB-clean, first-order); recorded for merge-window
  curation, not designated here.
- The `VerifiedExample` bundling structure and any gallery renderer —
  slice 3.
- Recursion/nested-loop termination + tactic packaging — the residue
  of the §4 debt after slice 1.5 paid the loop case (§5c).

## §12 THE ACTIVE-ABSTRACTION LOOP (user ruling 2026-08-13 — standing
convention for shared proof-kit growth)

The consolidation discipline for lifting repeated proof patterns into
shared kit modules (first exercised by the 2026-08-13 consolidation
slice, `docs/2026-08-13_consolidation-slice.md`):

(a) **Consumer-driven only.** Every lift retrofits **≥2 existing
    consumers in the same commit**, with a fixture witness (the
    retrofitted consumers themselves, plus a discharge instance where
    the lemma's premises deserve one). Never speculative API: if a
    second consumer does not exist yet, the pattern stays a private
    copy and a promotion-ledger row (form note §8 of the scale-out
    record).

(b) **Automation lives strictly in the untrusted-method zone.**
    Tactics, macros, and proof-side lemmas NEVER become headline
    statement vocabulary. Headline statements stay byte-identical
    under any kit retrofit (deletion tests + Audit designations stay
    green); the §11 statement closure is FROZEN vocabulary and the kit
    sits strictly beneath it.

(c) **Success is MEASURED.** Every lift reports line-count and
    elaboration-time deltas per retrofitted file, before vs after, in
    the slice record. A lift that saves nothing measurable is
    reverted, not kept for elegance.

(d) **Grind is the signal — both ways.** A missing abstraction
    announces itself as repeated grind (the brick-wp lesson); but if a
    lift itself enters a probe loop (>5 iterations without net
    progress in the artifact), STOP that item, record precisely where
    it resisted, and move on. An honest "kit insufficient because X"
    is a valid deliverable.
