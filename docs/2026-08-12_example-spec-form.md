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

Beside it, the full-domain companion (also shipped):

```lean
theorem fib_wraps (n : Nat) (hn : n < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel fibEnv fibSeed ch (fibCall n) = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩)
        = .ok (.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64)
```

*for every value of the Go argument type, every normal completion
returns `fibSpec n % 2^64`* — machine-integer honesty (FD-E3): what
Go's wrapping arithmetic actually computes past n = 93, run-conditioned
because full-domain termination is the recorded debt (§4).

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

### L5 — the termination cost (bounded-domain total claims)

The headline's completion half is kernel-enumerated: `allStreamsOk` at
fuel 6000 over all 94 seeds, one `decide +kernel`, measured **≈2:15
kernel time** (single n=93 run ≈3.5 s; whole module ≈223 s; the
desugared loop costs ~60 machine steps per iteration). This lands in
every proofs build via the in-build Audit gate. Options:

- (a) **Pay it** (BUILT): honest, simple; the cost is one module,
  parallelizable in the build graph.
- (b) **Trim the headline domain** (e.g. n ≤ 32): cheaper, but the
  bound stops meaning anything — 93 is the overflow boundary; 32 is a
  budget. Rejected unless build cost becomes a real problem.
- (c) **Symbolic termination machinery** (loop variants / a
  termination measure over the interpreter): the real fix, and the
  same machinery would upgrade `fib_wraps` to full-domain total. This
  is an arc of its own (§4).

**Recommendation: (a) now, (c) as the recorded debt's consumer.** If
2:15/build is judged too heavy at the checkpoint, (b)-with-a-recorded-
reason beats deleting the total claim.

## §4 Foundation debt recorded (charter FD-E3 fallback clause)

**Symbolic (∀-input) termination does not exist.** `Terminates` is
dischargeable only by per-seed kernel evaluation of the ∀-streams
checker (`allStreamsOk`), so: (1) the total claim's domain must be
kernel-enumerable — `fib_ok` is 94 checker runs, ≈2:15 of kernel time
per proofs build (L5); (2) the full-uint64-domain claim (`fib_wraps`)
is run-conditioned, NOT total — the "completes" half at 2^64 inputs is
out of reach. What closing it needs: a loop-variant/termination-measure
rule over the interpreter (or a WP-total carrier), i.e. new general
machinery — a future arc, not an example-lane patch (machine changes
are must-park here). Consumers: every loop example in slice 2 inherits
the same shape; the sequential-width arc's re-proof capstone inherits
the same bound. This entry is the debt record; the arc charter's honest
position ("concrete-domain fallbacks RECORDED as foundation debt") is
met by `fib_ok`'s enumerated bound.

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
For every `n` in the full `uint64` domain, any normal completion
returns `fib(n) mod 2^64` — Go's wrapping arithmetic, stated rather
than hidden.

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

theorem fib_wraps (n : Nat) (hn : n < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel fibEnv fibSeed ch (fibCall n) = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩)
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
- Symbolic termination — future arc (§4 debt).
