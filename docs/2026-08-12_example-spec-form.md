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

## §2 THE PROPOSED HEADLINE (decision object)

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
run-conditioned readout half remains available as `fib_wraps`.

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
- **(b) Full-domain wrapped claim** (BUILT, as `fib_wraps`):
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

- Naming: `fib_ok` (the total claim), `fib_wraps` (the boundary
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

## §6 TCB-grounding walk for `fib_ok` (per-export discipline)

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
`fib_wraps`).

## §7 Draft gallery entry (what a user would see)

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

**Axioms:** `[propext, Classical.choice, Quot.sound]` (Lean's classical
trio; no `sorry`, no native evaluation, no extra axioms).

**Ground:** the program in the theorem is the toolchain's pinned
lowering of the Go source above (staleness-guarded); the same source is
differentially tested against `go run`, including the n = 94 wrap.

---

## §8 Parked / out of scope (recorded)

- Machine/frontend changes (must-park): the `$forFirst` desugar tax
  (§4) goes to a frontend arc; no Choices sites touched; no
  interpreter edits.
- Designation: `fib_ok`/`fib_wraps` are designation CANDIDATES
  (statement-TCB-clean, first-order); recorded for merge-window
  curation, not designated here.
- The `VerifiedExample` bundling structure and any gallery renderer —
  slice 3.
- Recursion/nested-loop termination + tactic packaging — the residue
  of the §4 debt after slice 1.5 paid the loop case (§5c).
