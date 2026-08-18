# Verified examples — the gallery (2026-08-15/16; +matmul 2026-08-18)

Twenty-five Go programs, and for each one a GoLean theorem you can read.

This file is the **object of agreement**: it exists so that a reader who is
not a Lean expert can check, by eye, that the top-level statement really
establishes the property they want — *no errors, and returns the correct
value* — for a Go program they can also read. Nothing here is summarised
from a proof: every Go snippet, every theorem, and every axiom line below is
quoted **verbatim** from the file it comes from, and `scripts/render-gallery`
re-checks those quotes byte-for-byte (see *Staleness*, at the end).

Arc record: `docs/2026-08-15_gallery-campaign.md` — the campaign charter
seventeen of the eighteen newest entries were built under (its per-unit log
is `docs/gallery-campaign-log/`, its retrospective
`docs/2026-08-16_gallery-campaign-trip-report.md`; the eighteenth,
`matmul`, is the campaign's honest gap landed by the WP arc —
`docs/2026-08-16_wp-arc-charter.md` §Slice 4, its record
`docs/wp-arc-log/s4.md` unit S4.11);
`docs/2026-08-14_examples-phase2-arc-charter.md` — the phase-2 arc, which
swapped three of the headlines and designated all eight; the founding arc is
`docs/2026-08-12_verified-examples-arc-charter.md`. The statement form and
the rulings behind it: `docs/2026-08-12_example-spec-form.md` §11.

## How to read an entry

Every example ships one fixed Go **harness** function with three phases —
*setup* (build whatever memory the test needs, from scalar parameters), *the
call under test*, and *test* (analyse the result, in Go, folding the analysis
into returned values). The Lean statement observes only two things about
running that harness: that it finishes, and what it returns.

So each entry prints the subject program **and the harness in full, never
elided**. That is a rule, not a courtesy: where the harness's test phase
computes the verdict, *the claim is only as strong as the Go check you can
read beside it*. If the test phase checked the wrong thing, the theorem would
still be true and would still mean nothing. Reading the harness is part of
reading the claim.

Every headline has the same shape:

    ∃ N, ∀ fuel ≥ N, ∀ ch : Choices,
      runFunctionWithContextM fuel … harness #[args…] … ch
        = .ok { values := #[…] }

read as: *given enough gas, however the machine's nondeterministic choices
fall, the run finishes normally and returns exactly these values.* The single
`= .ok …` equation is what carries "no errors": the interpreter reports
exactly one outcome per run, and `.ok` is the one that is not a panic, not a
deadlock, not a stuck/unsupported state, not an internal error, and not fuel
exhaustion.

## What is being trusted

- **The interpreter is the model of Go, and it is the trust surface.**
  `runFunctionWithContextM` and the step function beneath it *are* the
  semantics these theorems talk about. If the interpreter is wrong about Go,
  every theorem here inherits that error. The standing check is the
  differential corpus: the same Go sources are run by real `go run` and by the
  machine, and every example's rows are green (per-entry, below).
- **The frontend is trust surface too.** The Go source is turned into the
  GoCore program the theorems talk about by `tools/nativefrontend` +
  `NativeToIR`, and *nothing here verifies that translation*. If the frontend
  lowers a Go construct wrongly, the theorem is a true statement about the
  wrong program. What checks it is the same differential corpus as the
  interpreter, and it checks the two **jointly**: frontend and interpreter
  together reproduce `go run`'s observable behaviour on every corpus row. That
  is validation, not proof, and it is the honest status of every claim below.
- **The program in each theorem is not retyped by hand.** It is the
  frontend's lowering of the corpus `main.go`, pinned by `scripts/check-golden`
  on both links — a fresh frontend emit + decode must reproduce the checked-in
  baseline, and the checked-in Lean term must print the same. Each proof module
  additionally pins the harness function *inside* that lowering by `rfl`.
  For the four unswapped examples that is `fibHarness_pin` and its siblings,
  registered in `proofs/Audit.lean`. For the three examples whose headline was
  swapped in phase-2 slice 1, the pin that carries the CURRENT headline lives
  in the example's audit shard beside the new harness —
  `reverseHarnessV_pin` (`proofs/Audit/Reverse.lean:61`), `minmaxHarnessR_pin`
  (`proofs/Audit/MinMax.lean:62`), `wordcountHarnessR_pin`
  (`proofs/Audit/WordCount.lean:110`) — while the `…Harness_pin` entries in
  `proofs/Audit.lean` still pin the harnesses the demoted `_v1` theorems talk
  about. Both sets are live; each theorem is pinned against its own harness.
  So "the theorem is about this Go file" is a **staleness-checked** chain: it
  catches a lowering that drifts from the source or a hand-edited Lean term,
  and it says nothing about whether the lowering is faithful. The translation
  step itself is validated by the differential corpus, not verified.
- **No proof machinery leaks into the statements.** They mention interpreter
  vocabulary, the pinned program, and specification functions (`fibSpec`,
  `findSpec`, …) that live with the other statement vocabulary in one
  definition-only module, `proofs/GoLeanProofs/Examples/Targets.lean` —
  readable on its own, and importing nothing but the interpreter and the
  pinned lowerings. No separation logic, no weakest-precondition machinery,
  no Iris appears in any statement — those are proof devices, and deleting
  the entire proof layer leaves these statements elaborating unchanged. That
  deletion test was checked by review and independently re-derived in the
  2026-08-14 pre-merge audit; as of 2026-08-14 the first eight headlines
  quoted below are **designated in the mechanized gate**
  (`proofs/Audit.lean`), so
  every build now walks each statement's transitive definition closure and
  fails if it reaches Iris or the Prop-level transition relation — the
  deletion test stopped being a thing we check by reading. Designation also
  puts them in front of the independent Comparator judge, which re-checks
  the proofs by kernel replay against these statements alone.
  **The eighteen newest entries — `histogram`, `powmod`, `dotprod`,
  `kadane`, `dedup`, `palin`, `strrev`, `twosum`, `selsort`, `bubble`,
  `rle`, `fibmemo`, `sieve`, `stein`, `wordfreq`, `stack`, `queue` and
  `matmul` —
  are NOT designated.**
  (The eight designated headlines span seven example sections, because
  `fib` carries two of them.) Seventeen were added by the gallery
  campaign (2026-08-15/16); `matmul` — the campaign's one honest gap —
  was landed by the WP arc (2026-08-18) as slice 4's chartered
  acceptance. Designation is a separate, user-signed act:
  all eighteen are deliberately absent from
  `Examples/Targets.lean`, from `scripts/ci`'s trusted-closure allowlist
  and from the Comparator judge's set. Their
  deletion tests were therefore RUN by hand rather than by the gate, all
  eighteen of them, recorded per unit in `docs/gallery-campaign-log/g1.md`
  (and, for `matmul`, in `docs/wp-arc-log/s4.md` unit S4.11)
  — `lean_minimal_hypotheses` on `histogram_ok` (all four explicit binders
  load-bearing), on `powmod_ok` (all five), on `dotprod_ok` (all three),
  on `kadane_ok` (all five), on `dedup_ok` (all three), on `fibmemo_ok`
  (both), on `sieve_ok` (both), on `stein_ok` (all three), on
  `wordfreq_ok` (all four) and on `stack_ok`
  (all four explicit binder groups); scratch re-elaboration per binder on
  lane B's six — `palin_ok`, `strrev_ok`, `twosum_ok`, `selsort_ok`,
  `bubble_ok`, `rle_ok` — each binder breaking at least one goal when
  dropped, no decorative hypothesis anywhere; for `queue_ok` a
  **machine probe** instead: each named hypothesis dropped in turn and the
  postcondition re-evaluated against the real run (`n = 9` panics,
  `k = 2^64` produces a witnessed counterexample, `seed = 2^64` still
  matches — so two of the three are frontiers of the claim and the third
  is a frontier of the proof only); and for `matmul_ok` the same
  machine-probe pattern (its one hypothesis `hseed` comes back a
  frontier of the proof only: at `seed = 2^64`, `2^64 + 5` and
  `2^65 + 7` the machine still matches the wrapped family). That is
  exactly the weaker standing that undesignated means. Their axioms are
  pinned in-build like everyone else's, one shard each
  (`proofs/Audit/Histogram.lean`, `proofs/Audit/PowMod.lean`,
  `proofs/Audit/DotProduct.lean`, `proofs/Audit/Kadane.lean`,
  `proofs/Audit/DedupAdjacent.lean`, `proofs/Audit/ArrayPalindrome.lean`,
  `proofs/Audit/StringReverse.lean`, `proofs/Audit/TwoSum.lean`,
  `proofs/Audit/SelectionSort.lean`, `proofs/Audit/BubbleSort.lean`,
  `proofs/Audit/RunLength.lean`, `proofs/Audit/FibMemo.lean`,
  `proofs/Audit/Sieve.lean`, `proofs/Audit/Stein.lean`,
  `proofs/Audit/WordFreq.lean`, `proofs/Audit/SliceStack.lean`,
  `proofs/Audit/SliceQueue.lean`, `proofs/Audit/MatMul.lean`).
- **Where the audits are.** Two adversarial pre-merge audits stand behind
  this file, and entries below cite both by date. The **2026-08-15** one —
  the phase-2 arc's, which swapped three headlines and designated all eight
  — has its own record with every finding and disposition:
  `docs/2026-08-15_phase2-premerge-audit.md`. The **2026-08-14** one, at the
  foundation merge, predates that practice; it is recorded in the arc's
  commits and in `docs/2026-08-12_verified-examples-arc-charter.md`
  §"Arc-end audit marker". Neither audit is a proof of anything — both are
  review, and where a claim below rests on one rather than on a gate or an
  oracle, the entry says so.
- **The heap is empty at entry.** Each theorem starts the harness from an
  empty state with its arguments at the call boundary, so the harness
  allocates everything it touches. There is nothing to frame, and no
  heap-level clause appears in any statement — the memory analysis happens in
  Go, inside the verified footprint.

## What "∀ choices" means

`Choices` is the stream of nondeterministic decisions the machine consumes at
points where Go does not promise an outcome. `∀ ch : Choices` says the claim
holds at **every** such stream. For nineteen of the twenty-five examples this
quantifier is cheap (their runs consume no choices). For the other six it
does real work, in two different ways — and `wordfreq` in both at once.

**Map iteration order** (word-count, histogram, wordfreq's max loop): `for …
range` over a Go map consumes one choice per iteration, because Go
deliberately does not fix map iteration order — so the theorem covers every
order, and the specification is *forced* to be order-independent. A spec
saying "the count of the first key" would be unprovable there. That
unprovability is the model working.

**`append` capacity** (stack, queue, run-length encoding, wordfreq's fields
slice): a spilling `append` consumes one choice, because Go promises only "a
new, sufficiently large underlying array" and real `gc` picks the size by an
amortized growth rule *and* by element-size-dependent size-class rounding —
so the machine admits an envelope of capacities rather than pinning one. The
theorem holds at every member. Here the *specification* is not forced to
change (capacity is not observable through the harness), but the *proof* is:
it has to carry the backing array's address and capacity as existentials,
because a proof pinned to one stream's layout would be a false claim about
`∀ ch`. Worth noticing when reading those entries: the returned values and
the step count are choice-invariant, while the heap layout — and even how
many choices the run consumes — are not. `queue` inherits this through
`enqueue`, and its dequeue half is choice-free, because re-slicing `q[1:]`
only advances a header offset.

## What fuel is, and what the bound is

The interpreter is fuel-indexed (that is what makes it a total function), so
termination is stated as `∃ N, ∀ fuel ≥ N`. **The statement claims only that
some bound exists**; each proof supplies an explicit one, quoted per entry
("fuel bound"). None of these bounds is enumerated over inputs — every
quantifier here is discharged symbolically.

## What these claims are NOT

- **Usability evidence, not machine-hardening evidence.** The charter's
  two-questions separation: this corpus shows the reasoning layer can carry
  natural specs through real programs on the current, deliberately over-tight
  machine. Whether the machine is permissive enough for everything Go might do
  is the separate width arc's question, whose exit includes re-proving this
  corpus over the widened machine.
- **Not ∀-input over data, where an entry says so.** The harness takes scalar
  parameters and its setup phase builds the data, so several entries quantify
  over an input *family* (`n`, `seed`) rather than over all slices. That is
  said plainly in each such entry. Where a genuinely ∀-data companion is
  proven, it is named in the entry's status line as supporting material.
- **Domain conditions are part of the claim.** Where a bound appears
  (`n ≤ 93`, `len < 2^63`, `len < 2^62`), the entry says which of four kinds
  it is: the mathematics, Go's own type domain *as the model represents it*,
  the program's own arithmetic — including where the bound exists because the
  program has a real, famous bug — or **machine idealization**. That fourth
  kind is the one to watch: the machine's heap is unbounded and allocation
  always succeeds, so a `2^63` length bound is where Go's `int` domain ends
  *in the model*, not where a real Go program stops working. Real Go is
  memory-bounded — `make([]uint64, n)` can fail long before `2^63` — so the
  practical domain of every allocating entry below is strictly smaller than
  the stated one. The theorems state the model's domain; that is honest only
  if said out loud (register entry: `docs/2026-08-11_essence-of-go-doctrine.md`).

---

## fib — iterative Fibonacci over uint64

**The Go** (`Corpus/coverage/exec/examples/fib/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/fib/main.go -->
```go
func fib(n uint64) uint64 {
	var a, b uint64 = 0, 1
	for i := uint64(0); i < n; i++ {
		a, b = b, a+b
	}
	return a
}
```

<!-- verbatim: Corpus/coverage/exec/examples/fib/main.go -->
```go
// fib_harness: the harness ruling's three-phase shape (2026-08-13).
// setup_fib_state: nothing — fib takes no memory input.
// test_fib_state: identity — the result IS the observable.
func fib_harness(n uint64) uint64 {
	r := fib(n)
	return r
}
```

**The claim.** For every `n ≤ 93` — the largest argument whose Fibonacci
number fits in a `uint64` — running `fib_harness(n)` finishes normally (no
panic, no error, no stuck state, no running out of fuel past one bound), at
every nondeterminism choice, and returns exactly the `n`-th Fibonacci number.
The bound `93` is arithmetic, not a limitation of the proof: it is where the
answer stops fitting. A companion theorem covers the **whole** `uint64`
argument domain and returns `fibSpec n mod 2^64` — what Go's wrapping
arithmetic actually computes past the boundary, stated rather than hidden.

**The specification function** (`proofs/GoLeanProofs/Examples/Targets.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Targets.lean -->
```lean
def fibSpec : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSpec n + fibSpec (n + 1)
```

**The theorems** (`proofs/GoLeanProofs/Examples/Fib.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Fib.lean -->
```lean
theorem fib_ok (n : Nat) (hn : n ≤ 93) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel fibLowered.typeDefs.toList
          fibLowered.funcs fibHarnessFunc #[.int (n : Int) .uint64]
          fibLowered.methods ch
        = .ok { values := #[.int (fibSpec n) .uint64] } := by
```

<!-- verbatim: proofs/GoLeanProofs/Examples/Fib.lean -->
```lean
theorem fib_total (n : Nat) (hn : n < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel fibLowered.typeDefs.toList
          fibLowered.funcs fibHarnessFunc #[.int (n : Int) .uint64]
          fibLowered.methods ch
        = .ok { values := #[.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit.lean`, checked at every build):

<!-- verbatim: proofs/Audit.lean -->
```lean
/-- info: 'GoLean.Examples.Fib.fib_ok' depends on axioms: [propext, Quot.sound] -/
```

<!-- verbatim: proofs/Audit.lean -->
```lean
/-- info: 'GoLean.Examples.Fib.fib_total' depends on axioms: [propext, Quot.sound] -/
```

Lean's `propext` and `Quot.sound` only — this pair does not even use
`Classical.choice`. No `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and affine: the proof supplies `N = 129 + 56·n`
interpreter steps.

**Status.** The harness headline is the user-facing claim; a run-conditioned
twin (`fib_readout`: *any* successful run returns that value) and
memory-quantified companions (`fib_framed`, `fib_total_framed` — the same
value claim with arbitrary other memory present and untouched) sit beneath it
as supporting material.

**Ground.** Differentially green against `go run` on 8 corpus rows —
`n = 0, 1, 2, 10, 93` and `94` (past the overflow boundary, oracle-confirming
the wrap), plus the harness itself at `10` and `94`.

---

## gcd — Euclid's algorithm over uint64

**The Go** (`Corpus/coverage/exec/examples/gcd/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/gcd/main.go -->
```go
func gcd(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}
```

<!-- verbatim: Corpus/coverage/exec/examples/gcd/main.go -->
```go
// gcd_harness: three-phase shape; setup and test are identities
// (argument-input subject, returned data is the observable).
func gcd_harness(a, b uint64) uint64 {
	r := gcd(a, b)
	return r
}
```

**The claim.** For every `a` and `b` in the full `uint64 × uint64` domain —
no bound and no wrapping clause, because `a % b` and the gcd cannot overflow —
`gcd_harness(a, b)` finishes normally, at every nondeterminism choice, and
returns exactly `Nat.gcd a b`: Lean's own textbook gcd, including
`gcd(0, 0) = 0`. This is the one arithmetic example where fib's
bounded/wrapped pair collapses into a single exact claim; there is no
overflow to state.

**The theorem** (`proofs/GoLeanProofs/Examples/Gcd.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Gcd.lean -->
```lean
theorem gcd_ok (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel gcdLowered.typeDefs.toList
          gcdLowered.funcs gcdHarnessFunc
          #[.int (a : Int) .uint64, .int (b : Int) .uint64]
          gcdLowered.methods ch
        = .ok { values := #[.int ((Nat.gcd a b : Nat) : Int) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/Gcd.lean`, the example's shard of
`proofs/Audit.lean`):

<!-- verbatim: proofs/Audit/Gcd.lean -->
```lean
/-- info: 'GoLean.Examples.Gcd.gcd_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and affine in the second argument: `N = 91 + 45·b`.

**Status.** `gcd_readout` is the run-conditioned twin; `gcd_framed` /
`gcd_framed_readout` are the memory-quantified companions (same value, with
arbitrary other memory present and preserved), kept as supporting material.

**Ground.** Differentially green on 9 corpus rows, including `gcd(0,0)`,
one-sided zeros, coprime pairs, a long chain, and a near-`2^63` pair, plus
the harness at `(12,18)` and `(7,0)`.

---

## reverse — in-place slice reversal (two-pointer)

**The Go** (`Corpus/coverage/exec/examples/reverse/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/reverse/main.go -->
```go
func reverse(s []uint64) {
	for i, j := 0, len(s)-1; i < j; i, j = i+1, j-1 {
		s[i], s[j] = s[j], s[i]
	}
}
```

<!-- verbatim: Corpus/coverage/exec/examples/reverse/main.go -->
```go
// reverse_harness_v: the COPY-RELATIONAL harness (examples phase-2
// slice 1, 2026-08-14; scoping study §4.3). Setup builds the family
// AND saves a pre-copy `t`; the test phase checks `s` against the
// SAVED COPY — the check is the reversal RELATION itself, not the
// setup algebra, so the Go reads as an ordinary unit test. The saved
// copy is a HISTORY GHOST materialized as real Go (ghost ladder rung
// 0): no annotations anywhere.
func reverse_harness_v(n, seed uint64) uint64 {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i
	}
	t := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		t[i] = s[i]
	}
	reverse(s)
	ok := uint64(1)
	for i := uint64(0); i < n; i++ {
		if s[i] != t[n-1-i] {
			ok = 0
		}
	}
	return ok
}
```

**The claim.** For every length `n < 2^63` and every `seed < 2^64`,
`reverse_harness_v(n, seed)` finishes normally, at every nondeterminism
choice, and **the check returned `1`**. What `1` means is in the Go above:
setup builds `s[i] = (seed + i) mod 2^64` and copies it into `t`, `reverse`
runs on `s`, and the test phase checks element-wise — in Go, inside the
verified footprint — that `s[i]` equals `t[n-1-i]`. The claim is exactly
*"that check returned 1, for every `(n, seed)` in the domain"*, and no more.

What the copy buys, and what it does not: the check now compares two reads
of the machine's own memory rather than re-deriving the setup formula, so
the Go says "reversal" and not "the family's algebra". It does NOT widen the
input quantifier — see Input honesty below.

The bound `n < 2^63` is where Go's `int` domain ends **in the model**:
`make([]uint64, n)` takes a Go `int`, so past `2^63` the length no longer fits
Go's `int` and `make` panics. Note what the bound is not — it is not the
practical domain of the Go program. The machine models allocation as always
succeeding (entry from an empty heap, an unbounded heap, no allocation
failure), while real Go is memory-bounded and `make([]uint64, n)` fails far
below `2^63`. So the theorem's domain is the model's domain, wider than the
one a real process has; the machine idealization, not the theorem, is what
buys the extra width. The harness also allocates a second `n`-element slice
that exists only so the check can be stated over observed data.

Input honesty: the quantifiers are the scalars `(n, seed)` — an input
*family*, not all slices. The copy-relational check does not change that; it
makes the harness the ANNOTATION-READY form, because at ghost rung 1
annotating the one setup assignment would make the input ∀-data with the same
test phase, which the verdict harness below (`reverse_ok_v1`, whose check
re-derives `seed+(n-1-i)`) could never do. The wrapping is deliberate and the
theorem covers every seed below `2^64`, including the ones where `seed + i`
wraps; since extension E1 the differential rows DO reach that region
(see **Ground**).

**The family** (`proofs/GoLeanProofs/Examples/Reverse/Core.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Reverse/Core.lean -->
```lean
def revFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i) % 2 ^ 64 : Nat) : Int))
```

**The theorem** (`proofs/GoLeanProofs/Examples/Reverse/HarnessV.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Reverse/HarnessV.lean -->
```lean
theorem reverse_ok (n seed : Nat) (hn : n < 2 ^ 63) (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel reverseLowered.typeDefs.toList
          reverseLowered.funcs reverseHarnessVFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          reverseLowered.methods ch
        = .ok { values := #[.int 1 .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/Reverse.lean`):

<!-- verbatim: proofs/Audit/Reverse.lean -->
```lean
/-- info: 'GoLean.Examples.Reverse.reverse_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and affine: `N = 205·n + 335`. The measured step
counts are bounded above by that same expression — but it is a *bound on the
measurements*, not a law, because the true counts are **not affine**: their
first differences alternate 167/242, since a two-pointer swap happens every
other iteration. The bound is tight only at `n = 0`, running 1 to 41 steps
above the measurements at `n = 1…8`. There is no single affine measured law
to quote here, so none is quoted.

**Status.** `reverse_readout` is the run-conditioned twin. Two supporting
theorems sit beneath, both kept and both still proved:

* `reverse_ok_v1` (with `reverse_readout_v1`) — the previous headline over
  `reverse_harness`, whose test phase re-derives `seed+(n-1-i)` instead of
  reading a saved copy. Same claim shape, different Go; its corpus rows stay.
* `reverse_framed` — the stronger INPUT claim: for any list of `uint64`
  values **of length below `2^63`**, at any placement, beside any frame that
  does not already occupy that placement, and under the module's stated
  well-formedness and frame-disjointness side conditions (`MachineWf` on the
  seed state, `hb`/`hxs` — see the module), `reverse` finishes and that
  memory then holds the list reversed with every frame cell preserved. It is
  genuinely ∀-data — no harness family subsumes it — and it is kept as
  supporting material because the user-facing form observes only returned
  values.

**Ground.** Differentially green on 14 corpus rows: four/three/one/empty
element drivers, an `int64`-boundary value and a `2^64-1` driver value
(`four-u64max`); the verdict harness at `(5,100)`, `(0,7)`, a near-`2^63`
seed (`harness-wrapping`) and seed `2^64-1` (`harness-wrap-max`); and the
copy-relational harness at `harness-v-five`, `harness-v-empty`,
`harness-v-wrapping` and `harness-v-wrap-max`. **The `uint64` wrap region is
now oracle-witnessed**: at seed `2^64-1` the family `s[i] = seed + i` is
`[2^64-1, 0, 1, 2]`, and the two `*-wrap-max` rows compare real `go run`
against the machine there, like every other row. Before extension E1
(2026-08-15, `docs/gallery-campaign-log/g2.md`) the differential driver
parsed its arguments as signed `int64`, so a near-`2^63` seed was the largest
a row could express and the wrap region rested on hand `go run` probes from
the 2026-08-14 audit; the driver now parses the full 64-bit domain and those
probes are permanent rows. Note the two `*-wrapping` ids are MISNAMED and
known to be: at seed `9223372036854775805` with `n = 4` the family tops out
at exactly `2^63`, so nothing wraps. Renaming them to `*-near-max` is
chartered under E1 and is currently BLOCKED by the baseline re-pin guard,
which cannot tell a renamed id from a regressed one (`g2.md`, E1's build
record).

---

## minmax — minimum and maximum of a slice

**The Go** (`Corpus/coverage/exec/examples/minmax/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/minmax/main.go -->
```go
func minMax(s []uint64) (uint64, uint64) {
	lo, hi := s[0], s[0]
	for i := 1; i < len(s); i++ {
		if s[i] < lo {
			lo = s[i]
		}
		if s[i] > hi {
			hi = s[i]
		}
	}
	return lo, hi
}
```

<!-- verbatim: Corpus/coverage/exec/examples/minmax/main.go -->
```go
// minmax_harness_r: the S3 RELATIONAL harness (examples phase-2 slice
// 1, 2026-08-14; scoping study §4.4). Returns the PRE-STATE (as a
// fixed-cap array, the pass-by-value fragment's unbounded-data
// workaround) alongside the subject's `(lo, hi)`, so the Lean
// postcondition relates the returned data DIRECTLY —
// `lo = minSpec pre`, `hi = maxSpec pre` — with no family function
// re-describing the setup. Real Go, ghost ladder rung 0.
func minmax_harness_r(n, seed uint64) ([minmaxCapN]uint64, uint64, uint64) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i
	}
	var pre [minmaxCapN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	lo, hi := minMax(s)
	return pre, lo, hi
}
```

**The claim.** For every `n` with `1 ≤ n ≤ 8` and every `seed < 2^64`,
`minmax_harness_r(n, seed)` finishes normally, at every nondeterminism
choice, and returns three values: a list `pre` of length `n` (as the
fixed-cap array the Go returns) together with the pair
`(minSpec pre, maxSpec pre)`. **The postcondition is a relation over the
RETURNED data** — min and max of the very array the program handed back. No
family function appears in the claim.

Three honesty clauses, none of them small print:

* **The cap `n ≤ 8` is a toy bound, and it is the price of this style.** Go's
  pass-by-value fragment cannot return unbounded data, so the harness returns
  `[minmaxCapN]uint64` with `minmaxCapN = 8` — visible in the Go — and the
  second loop and the zero padding exist *only* so the pre-state can cross
  the observation boundary. The theorem carries `n ≤ 8` as a hypothesis
  rather than hiding it.
* **`∃ pre` is still family-determined.** The witness the proof supplies is
  `s[i] = (seed + i) mod 2^64`; the statement merely does not *say* so. What
  the swap buys is on the postcondition side, not the input side: the old
  headline (kept as `minmax_ok_v1`) asserts `minSpec (mmFamily n seed)`,
  naming the setup family inside the claim, and this one asserts
  `minSpec pre` about observed output. Turning the input into genuine
  ∀-data needs the ghost rung-1 annotation, which is designed and not built.
* **`1 ≤ n` is Go's own boundary**, not proof convenience: `minMax` reads
  `s[0]`, so the empty slice panics, and the corpus pins that panic against
  `go run`.

As elsewhere, the machine idealizes allocation (entry from an empty heap, an
unbounded heap, allocation always succeeds), so the theorem's domain is the
model's. Because the family wraps at `2^64`, the answer is not simply the
first and last element once `seed + n` crosses the boundary.

**The specification functions** (`proofs/GoLeanProofs/Examples/Targets.lean`;
their `[]` cases are unreachable here, since `n ≥ 1`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Targets.lean -->
```lean
def minSpec : List Int → Int
  | [] => 0
  | [v] => v
  | v :: w :: rest => min v (minSpec (w :: rest))
```

<!-- verbatim: proofs/GoLeanProofs/Examples/Targets.lean -->
```lean
def maxSpec : List Int → Int
  | [] => 0
  | [v] => v
  | v :: w :: rest => max v (maxSpec (w :: rest))
```

**The returned-array adapter** — the whole of the S3 statement vocabulary
(`proofs/GoLeanProofs/Examples/Targets.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Targets.lean -->
```lean
def goArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .uint64)⟩
```

**The theorem** (`proofs/GoLeanProofs/Examples/MinMax/HarnessR.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/MinMax/HarnessR.lean -->
```lean
theorem minmax_ok (n seed : Nat) (h1 : 1 ≤ n) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel minMaxLowered.typeDefs.toList
            minMaxLowered.funcs mmHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            minMaxLowered.methods ch
          = .ok { values := #[goArr8 pre,
                              .int (minSpec pre) .uint64,
                              .int (maxSpec pre) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/MinMax.lean`):

<!-- verbatim: proofs/Audit/MinMax.lean -->
```lean
/-- info: 'GoLean.Examples.MinMax.minmax_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and affine: `N = 202·n + 218`. This is the
branch-UNIFORM worst case — either `if` inside `minMax` may fire, at 16 steps
each. The *measured* law at a non-wrapping seed is `186·n + 234`, and that is
also a true bound, because `s[i] < lo` and `s[i] > hi` cannot both hold in one
iteration; proving the tighter number would mean carrying `lo ≤ hi` through
the loop induction, which buys nothing when the statement is `∃N`. The bound
quoted here is the one the theorem actually ships.

**Status.** `minmax_readout` is the run-conditioned twin. Beneath sit
`minmax_ok_v1` / `minmax_readout_v1` — the previous headline over
`minmax_harness`, which returns only the pair and states
`minSpec (mmFamily n seed)`, naming the family in the claim; kept unweakened
with its corpus rows. Below those, `minmax_framed` /
`minmax_framed_readout` are the memory-quantified companions — for any
**non-empty** list of `uint64` values of length below `2^63`, at any
placement other than the two result cells, and under the module's stated
well-formedness and frame-disjointness side conditions (`MachineWf`, the
three `Heap.lookup fr … = none` clauses — see the module), with the
additional claim that the input slice comes back unchanged (the program is
read-only on its input) and every frame cell is preserved. Supporting
material.

**Ground.** Differentially green on 16 corpus rows: the four/three/one/empty
drivers, an `int64`-boundary value and a `2^64-1` driver value
(`four-u64max`), the empty-slice panic through both the driver and the
harness, the pair harness at `(5,40)`, `(1,7)` and seed `2^64-1`
(`harness-wrap-max`), and the relational harness at `harness-r-five`,
`harness-r-one`, `harness-r-eight`, `harness-r-wrap-max` (seed `2^64-1`)
and `harness-r-empty-panics`.

What the rows reach, corrected: the theorem covers every `seed < 2^64`,
including the seeds where `seed + i` wraps and the answer stops being "the
first and last element" — and **since extension E1 (2026-08-15,
`docs/gallery-campaign-log/g2.md`) corpus rows reach that region**. At seed
`2^64-1` with `n = 5` the family is `[2^64-1, 0, 1, 2, 3]`, so `lo = 0` and
`hi = 2^64-1`: the wrap is what makes the answer, and `harness-wrap-max` /
`harness-r-wrap-max` check it against real `go run`. Until E1 the
differential driver parsed `int64` arguments, the largest expressible seed
was near `2^63`, and this entry's wrap behaviour rested on a 2026-08-15
audit check **on the machine only, with no `go run` oracle in the loop** —
that gap is closed, and the oracle agrees.

---

## binsearch — first-occurrence binary search over a sorted []uint64

**The Go** (`Corpus/coverage/exec/examples/binsearch/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/binsearch/main.go -->
```go
func search(s []uint64, target uint64) int {
	lo, hi := 0, len(s)
	for lo < hi {
		mid := (lo + hi) / 2
		if s[mid] < target {
			lo = mid + 1
		} else {
			hi = mid
		}
	}
	if lo < len(s) && s[lo] == target {
		return lo
	}
	return -1
}
```

<!-- verbatim: Corpus/coverage/exec/examples/binsearch/main.go -->
```go
// search_harness: three-phase harness — setup builds the sorted
// family s[i] = seed + 2*i (precondition: no wrap, so it IS sorted
// with gaps); the target is a raw parameter, covering found and
// not-found; returned index is the observable.
func search_harness(n, seed, t uint64) int {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + 2*i
	}
	return search(s, t)
}
```

**The claim.** For every `n < 2^62`, every `seed` with `seed + 2n < 2^64`,
and every target `t` in the `uint64` range, `search_harness(n, seed, t)`
finishes normally, at every nondeterminism choice, and returns exactly the
index of the **first** occurrence of `t` in the family
`s[i] = seed + 2·i`, or `-1` when `t` does not occur. The family is spaced by
two, so in-range misses are covered as well as hits; the `seed + 2n < 2^64`
condition is what makes the setup family genuinely sorted (no wrap).

**The `2^62` bound is the program's own bug, stated honestly.**
`mid := (lo + hi) / 2` computes `lo + hi` in Go's `int`: at lengths above
`2^62` that sum can reach `2^63` and wrap negative — the classic "nearly all
binary searches are broken" overflow (Bloch, 2006). We did not repair the
program and we did not hide the boundary; it appears as a domain condition of
the theorem. (The first genuinely unsafe length is `2^62 + 1`; the stated
bound is the clean power of two one step inside.)

Input honesty: the quantifiers are the scalars `(n, seed, t)` — an input
family, not all sorted slices.

**The specification function and the family**
(`proofs/GoLeanProofs/Examples/Targets.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Targets.lean -->
```lean
def findSpec (xs : List Int) (t : Int) : Int :=
  match xs with
  | [] => -1
  | v :: rest =>
      if v = t then 0
      else if findSpec rest t < 0 then -1 else findSpec rest t + 1
```

<!-- verbatim: proofs/GoLeanProofs/Examples/Targets.lean -->
```lean
def bsFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => ((seed + 2 * i : Nat) : Int))
```

**The theorem** (`proofs/GoLeanProofs/Examples/BinSearch.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/BinSearch.lean -->
```lean
theorem search_ok (n seed : Nat) (t : Int)
    (hn : n < 2 ^ 62) (hnowrap : seed + 2 * n < 2 ^ 64)
    (ht : 0 ≤ t ∧ t < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel searchLowered.typeDefs.toList
          searchLowered.funcs searchHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
            .int t .uint64]
          searchLowered.methods ch
        = .ok { values := #[.int (findSpec (bsFamily n seed) t) .int] } := by
```

**Axioms** (pinned in `proofs/Audit/BinSearch.lean`, the example's shard of
`proofs/Audit.lean`):

<!-- verbatim: proofs/Audit/BinSearch.lean -->
```lean
/-- info: 'GoLean.Examples.BinSearch.search_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and affine: `N = 220 + 132·n`.

**Status.** This is the one entry with **no run-conditioned twin at the
harness form** — `search_framed_readout` exists for the memory-quantified
companion only. `search_framed` is that companion (∀ sorted list, at any
placement, other memory preserved, input array unchanged); both are
supporting material. Also shown on the way: the post-loop `&&` really is
lazy — when `lo = len(s)`, the out-of-bounds read `s[lo]` never happens. That
is shown by the proof's step-walk (the segment completes without a panic, and
the machine panics on out-of-range reads); the carrier lemmas are
proof-internal.

**Ground.** Differentially green on 14 corpus rows: first/middle/last hits,
misses below, in the gap and above, the duplicates lower-bound row (first
occurrence, not any occurrence), one-element and empty slices, an
`int64`-boundary value, plus the harness at `(6,10,14)`, `(6,10,15)` and
`(0,10,3)`.

---

## isort — insertion sort (nested loops, short-circuit `&&`)

**The Go** (`Corpus/coverage/exec/examples/isort/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/isort/main.go -->
```go
func insertionSort(s []uint64) {
	for i := 1; i < len(s); i++ {
		for j := i; j > 0 && s[j-1] > s[j]; j-- {
			s[j-1], s[j] = s[j], s[j-1]
		}
	}
}
```

<!-- verbatim: Corpus/coverage/exec/examples/isort/main.go -->
```go
// isort_harness: three-phase harness — setup builds the wrapped
// multiplicative family s[i] = seed * (i+1); test verifies IN GO
// (inside the verified footprint) that the result is sorted AND a
// permutation of the rebuilt input family (count-based), folding
// into a verdict.
func isort_harness(n, seed uint64) uint64 {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed * (i + 1)
	}
	insertionSort(s)
	ok := uint64(1)
	for i := uint64(1); i < n; i++ {
		if s[i-1] > s[i] {
			ok = 0
		}
	}
	t := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		t[i] = seed * (i + 1)
	}
	for i := uint64(0); i < n; i++ {
		cs := uint64(0)
		ct := uint64(0)
		for j := uint64(0); j < n; j++ {
			if s[j] == t[i] {
				cs++
			}
			if t[j] == t[i] {
				ct++
			}
		}
		if cs != ct {
			ok = 0
		}
	}
	return ok
}
```

**The claim.** For every `n < 2^63` and every `seed < 2^64`,
`isort_harness(n, seed)` finishes normally, at every nondeterminism choice,
and returns `1`. **What `1` means is the Go test phase above**: setup builds
`s[i] = (seed·(i+1)) mod 2^64` — wrapping, so the family has duplicates and
non-monotone orders, which are the interesting sort inputs — `insertionSort`
runs, and then, in Go, the test phase checks that the result is pairwise
sorted **and** that every element of a freshly rebuilt copy of the input
occurs exactly as many times in the sorted slice as it does in that copy —
which, the two having the same length, is a permutation check. The claim is
that this verdict is `1` for every `(n, seed)` in the domain; it is exactly
as strong as the check printed above, and no stronger.

`n < 2^63` is Go's `int` domain for lengths, as in reverse — the model's
domain: this harness allocates two slices, and the machine's allocation never
fails, so the practical Go domain is much smaller. Input honesty: the
quantifiers are the scalars `(n, seed)`.

**The family** (`proofs/GoLeanProofs/Examples/InsertionSort/Family.lean`, the
family shard of the split `InsertionSort` module):

<!-- verbatim: proofs/GoLeanProofs/Examples/InsertionSort/Family.lean -->
```lean
def isFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed * (i + 1)) % 2 ^ 64 : Nat) : Int))
```

**The theorem** (`proofs/GoLeanProofs/Examples/InsertionSort.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/InsertionSort.lean -->
```lean
theorem isort_ok (n seed : Nat) (hn : n < 2 ^ 63) (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel isortLowered.typeDefs.toList
          isortLowered.funcs isortHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          isortLowered.methods ch
        = .ok { values := #[.int 1 .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/InsertionSort.lean`, the example's shard
of `proofs/Audit.lean`):

<!-- verbatim: proofs/Audit/InsertionSort.lean -->
```lean
/-- info: 'GoLean.Examples.InsertionSort.isort_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/InsertionSort.lean -->
```lean
/-- info: 'GoLean.Examples.InsertionSort.isort_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and **quadratic**, honestly so — the harness's
count-based permutation check is O(n²):
`N = (92·n+160)·n + (110·n+220)·n + 285·n + 505`.

**Status.** `isort_readout` is the run-conditioned twin. The mathematical
sortedness claim lives beneath, in the memory-quantified companion
`isort_framed`: for any list of `uint64` values **of length below `2^63`**,
at any placement, beside any disjoint frame, and under the module's stated
well-formedness and frame-disjointness side conditions (`MachineWf`,
`hb`/`hxs` — see the module), the slice afterwards holds `sortSpec xs` —
proven sorted (`sortSpec_sorted`), of the same length (`sortSpec_length`) and
a permutation (`sortSpec_count`: every value keeps its multiplicity) — with
every frame cell preserved. That companion, not the harness verdict, is where
"insertion sort sorts" is stated in mathematics. Also proved on the way: at
`j = 0` the machine provably never reads `s[j-1]` — Go's short-circuit `&&`
is load-bearing here, and that is shown by the proof's step-walk (the segment
completes without a panic, and the machine panics on out-of-range reads); the
carrier lemmas are proof-internal.

**Ground.** Differentially green on 13 corpus rows
(shuffled/sorted/reversed/duplicates/`int64`-boundary/`2^64-1`
(`four-u64max`)/three/one/empty) plus the harness at `(5,37)`, `(6,0)`
(all-equal family), `(0,5)` and seed `2^64-1` (`harness-wrap-max`, extension
E1). At that seed the multiplicative family `s[i] = seed * (i+1)` wraps at
every index — it is `[2^64-1, 2^64-2, …, 2^64-5]`, i.e. descending — so the
row exercises the sort's worst case and the wrapping setup arithmetic
against real `go run`.

---

## wordcount — maximum multiplicity via a Go map

**The Go** (`Corpus/coverage/exec/examples/wordcount/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/wordcount/main.go -->
```go
func maxCount(words []uint64) uint64 {
	counts := make(map[uint64]uint64)
	for i := 0; i < len(words); i++ {
		counts[words[i]]++
	}
	best := uint64(0)
	for _, c := range counts {
		if c > best {
			best = c
		}
	}
	return best
}
```

<!-- verbatim: Corpus/coverage/exec/examples/wordcount/main.go -->
```go
// wordcount_harness_r: the S3 RELATIONAL harness (examples phase-2
// slice 1, 2026-08-14; scoping study §4.7, re-landed by slice 1.5
// after the `wc_empty_run` cost blocker was retired). Returns the
// WORDS (as a fixed-cap array, the pass-by-value fragment's
// unbounded-data workaround) alongside the subject's answer, so the
// Lean postcondition relates the returned data DIRECTLY —
// `best = maxMultiplicity words` — with no family function
// re-describing the setup. Real Go, ghost ladder rung 0.
func wordcount_harness_r(n, seed uint64) ([wordcountCapN]uint64, uint64) {
	w := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		w[i] = seed + i%3
	}
	var words [wordcountCapN]uint64
	for i := uint64(0); i < n; i++ {
		words[i] = w[i]
	}
	best := maxCount(w)
	return words, best
}
```

**The claim.** For every `n ≤ 8` and every `seed < 2^64`,
`wordcount_harness_r(n, seed)` finishes normally, at every nondeterminism
choice, and returns two values: a list `words` of length `n` (as the
fixed-cap array the Go returns) together with `maxMultiplicity words`.
**The postcondition is a relation over the RETURNED data** — the greatest
number of times any word id occurs in the very array the program handed
back. Neither the setup family nor its solved closed form appears in the
claim.

**This is still the entry where `∀ ch : Choices` earns its keep — and after
the swap that quantifier is load-bearing for READING the claim, not just for
proving it.** The subject iterates over a Go **map**, and Go deliberately
does not fix map iteration order; the machine therefore consumes one
nondeterministic choice per iteration, and the theorem holds at every one of
them — i.e. at every iteration order Go could exhibit. That is only possible
because **`maxMultiplicity` is order-invariant**: it is a max-fold over
multiplicities, and multiplicities do not depend on the order the entries
were visited. So "the returned count is the greatest multiplicity among the
returned words" means exactly what it sounds like. Had the specification
named an order-dependent witness — "the count of the first key visited" —
the statement would be *unprovable*, since different streams give different
answers, and the envelope would be rejecting the claim by construction. This
is the one place where the S3 "relation over returned data" framing could
mislead a reader if the order-invariance were left implicit, so it is said
here explicitly.

Three honesty clauses, none of them small print:

* **The cap `n ≤ 8` is a toy bound, and it is the price of this style.** Go's
  pass-by-value fragment cannot return unbounded data, so the harness returns
  `[wordcountCapN]uint64` with `wordcountCapN = 8` — visible in the Go — and
  the copy loop and the zero padding exist *only* so the counted words can
  cross the observation boundary. The theorem carries `n ≤ 8` as a hypothesis
  rather than hiding it. Note the contrast with minmax: there is no `1 ≤ n`
  here, because `maxCount` of an empty slice returns `0` rather than
  panicking, and the corpus pins that case.
* **`∃ words` is still family-determined.** The witness the proof supplies is
  `w[i] = (seed + i%3) mod 2^64`; the statement merely does not *say* so.
  What the swap buys is on the postcondition side: the old headline (kept as
  `wordcount_ok_v1`) asserts the *solved value* `⌈n/3⌉`, which names the
  family and its combinatorics inside the claim, while this one asserts
  `maxMultiplicity words` about observed output — and the closed form
  `wcFamily_maxMult` is not used in the proof at all. Turning the input into
  genuine ∀-data needs the ghost rung-1 annotation, which is designed and not
  built.
* **Machine idealization**, as elsewhere: entry from an empty heap, an
  unbounded heap, allocation always succeeds — and this harness also grows a
  map. The theorem's domain is the model's, not the practical one.

**The specification functions**
(`proofs/GoLeanProofs/Examples/Targets.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Targets.lean -->
```lean
def multiplicity (v : Int) (ws : List Int) : Nat :=
  (ws.filter (· = v)).length
```

<!-- verbatim: proofs/GoLeanProofs/Examples/Targets.lean -->
```lean
def maxMultiplicity (ws : List Int) : Nat :=
  ws.foldl (fun acc v => max acc (multiplicity v ws)) 0
```

Read the second one alongside the order-invariance paragraph above: `max` is
commutative and idempotent and `multiplicity v ws` does not depend on
position, which is precisely why the fold is a legitimate specification for a
loop whose visit order the machine chooses.

**The returned-array adapter** — the whole of the S3 statement vocabulary
(`proofs/GoLeanProofs/Examples/Targets.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Targets.lean -->
```lean
def goArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .uint64)⟩
```

**The theorem** (`proofs/GoLeanProofs/Examples/WordCount/HarnessR.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/WordCount/HarnessR.lean -->
```lean
theorem wordcount_ok (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ words : List Int, words.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel wordCountLowered.typeDefs.toList
            wordCountLowered.funcs wcHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            wordCountLowered.methods ch
          = .ok { values := #[goArr8 words,
                              .int (maxMultiplicity words : Nat) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/WordCount.lean`):

<!-- verbatim: proofs/Audit/WordCount.lean -->
```lean
/-- info: 'GoLean.Examples.WordCount.wordcount_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/WordCount.lean -->
```lean
/-- info: 'GoLean.Examples.WordCount.wordcount_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and affine: `N = 218·n + 302`. This is the
branch-UNIFORM worst case: the range loop is charged 24 steps per iteration
(the cost when `c > best` fires and `best` is rewritten; the else branch
costs 12), and the map snapshot is bounded by the word count rather than by
the three distinct values this particular family produces. **The measured
step counts are a different number, and the difference is worth stating
plainly.** They are bounded above by `206·n + 314`, which is tight at
`1 ≤ n ≤ 3` — and *not* at `n = 0`, the point the earlier "tight at `n ≤ 3`"
wording swept in, where the 2026-08-15 audit's measurement puts the bound 12
steps high — but that is an
affine *upper bound on the measurements*, not a law, because the true counts
are **not affine**: the first differences run 218, 206, 206, then 194, since
the family `w[i] = seed + i%3` stops adding new entries to the map after the
third word and every later word is cheaper.
There is no single measured law to quote here, so none is quoted; the bound
the theorem ships is `218·n + 302` and the measurement envelope is
`206·n + 314`, and neither is presented as the other.

**Status.** `wordcount_readout` is the run-conditioned twin. Beneath the
headline sit `wordcount_ok_v1` / `wordcount_readout_v1` — the previous
headline over `wordcount_harness`, which returns only the scalar and states
the solved `⌈n/3⌉`; kept unweakened with its corpus rows, since it and the
S3 form make genuinely different claims rather than one superseding the
other. Below those, `maxCount_total_canonical` is the stronger *input*
claim: for **any** list of word ids (not just the three-residue family), at
every choice stream, the subject finishes and delivers the maximum
multiplicity — the ∀-data claim no scalar-parameterized harness subsumes.
`wordcount_empty_ok` covers the zero-argument degenerate harness. Supporting
material.

**Ground.** Differentially green on 14 corpus rows: the distinct /
all-same / mode-of-three / two-pairs / one / empty drivers plus a
`2^64-1`-keyed driver (`four-u64max`), the scalar harness at `(7,50)`,
`(0,9)` and seed `2^64-1` (`harness-wrap-max`), and the relational harness
at `harness-r-seven`, `harness-r-eight`, `harness-r-empty` and seed `2^64-1`
(`harness-r-wrap-max`). The `(n+2)/3` closed form behind `wordcount_ok_v1`
was additionally cross-checked against `go run` at seeds `0`, `50`, `2^63−1`,
`2^64−3`, `2^64−2`, `2^64−1` before any of it was written in Lean; since
extension E1 (2026-08-15) the `2^64−1` end of that sweep is a permanent
oracle row rather than a hand probe — the family `seed + i%3` is
`[2^64-1, 0, 1, …]` there, so the wrap decides the map keys themselves.

---

---

## histogram — a queried count and a distinct-key count via a Go map

**The Go** (`Corpus/coverage/exec/examples/histogram/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/histogram/main.go -->
```go
func histogram(vals []uint64, q uint64) (uint64, uint64) {
	counts := make(map[uint64]uint64)
	for i := 0; i < len(vals); i++ {
		counts[vals[i]]++
	}
	hits := counts[q]
	distinct := uint64(0)
	for range counts {
		distinct++
	}
	return hits, distinct
}
```

<!-- verbatim: Corpus/coverage/exec/examples/histogram/main.go -->
```go
// histogram_harness_r: the S3 RELATIONAL harness (gallery campaign G1,
// 2026-08-15). Setup builds the value family v[i] = seed + i%3
// (controllable multiplicities); the harness returns the VALUES it
// counted (as a fixed-cap array, the pass-by-value fragment's
// unbounded-data workaround) alongside both summaries, so the Lean
// postcondition relates the returned data DIRECTLY — no family function
// re-describing the setup. Real Go, ghost ladder rung 0.
func histogram_harness_r(n, seed, q uint64) ([histogramCapN]uint64, uint64, uint64) {
	v := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		v[i] = seed + i%3
	}
	var vals [histogramCapN]uint64
	for i := uint64(0); i < n; i++ {
		vals[i] = v[i]
	}
	hits, distinct := histogram(v, q)
	return vals, hits, distinct
}
```

**The claim.** For every `n ≤ 8`, every `seed < 2^64` and every queried key
`q < 2^64`, `histogram_harness_r(n, seed, q)` finishes normally, at every
nondeterminism choice, and returns three values: a list `vals` of length `n`
(as the fixed-cap array the Go returns), the number of times `q` occurs in
that very list, and the number of distinct values that very list holds.
**The postcondition is a relation over the RETURNED data** — neither the
setup family nor any closed form appears in it.

**This is the second entry where `∀ ch : Choices` earns its keep, and here
the order-invariance is load-bearing for the *third* value.** `for range
counts` iterates a Go map, whose order Go deliberately does not fix; the
machine consumes one nondeterministic choice per iteration and the theorem
holds at every one of them. That is possible because `distinctCount` is a
function of the returned values alone — it cannot see the order the machine
chose. So "the third value is how many distinct values the returned array
holds" means exactly what it sounds like. A spec naming an order-dependent
witness — "the count of the first key visited" — would be *unprovable*, and
that unprovability would be the envelope rejecting the claim by
construction.

There is a second thing worth noticing about the machine here, because it is
what makes this example cheap: `for range counts { … }` binds **neither** a
key nor a value, so the machine's per-iteration bookkeeping allocates
nothing at all. Its only effect is "one fewer entry in the snapshot". The
number of iterations is therefore the number of entries, at every stream —
which is the whole proof of the third value.

Four honesty clauses, none of them small print:

* **The queried count is the map READ, zero value included.** Go's
  `counts[q]` on a key that was never counted yields `0`, not an error, and
  `occurrences q vals` is `0` in exactly that case. This is a real Go
  semantics point rather than a convenience: the corpus rows `miss`,
  `one-miss` and `harness-r-miss` pin it against `go run` before any of it
  was written in Lean.
* **The cap `n ≤ 8` is a toy bound, and it is the price of this style.**
  Go's pass-by-value fragment cannot return unbounded data, so the harness
  returns `[histogramCapN]uint64` with `histogramCapN = 8` — visible in the
  Go — and the copy loop and the zero padding exist *only* so the counted
  values can cross the observation boundary. The theorem carries `n ≤ 8` as
  a hypothesis rather than hiding it.
* **`∃ vals` is still family-determined.** The witness the proof supplies is
  `v[i] = (seed + i%3) mod 2^64`; the statement merely does not *say* so.
  What the S3 form buys is on the postcondition side — both answers are
  asserted about observed output. Turning the input into genuine ∀-data
  needs the ghost rung-1 annotation, which is designed and not built.
* **Machine idealization**, as elsewhere: entry from an empty heap, an
  unbounded heap, allocation always succeeds — and this harness also grows a
  map. The theorem's domain is the model's, not the practical one. The three
  arithmetic domains are separated as usual: `n ≤ 8` is *the program's own*
  (the array cap), `seed < 2^64` and `q < 2^64` are *Go's* uint64 domain at
  the call boundary, and the counting itself is mathematics.

**The specification functions**
(`proofs/GoLeanProofs/Examples/Histogram/Pure.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Histogram/Pure.lean -->
```lean
def occurrences (v : Int) (l : List Int) : Nat :=
  (l.filter (· = v)).length
```

<!-- verbatim: proofs/GoLeanProofs/Examples/Histogram/Pure.lean -->
```lean
def distinctCount : List Int → Nat
  | [] => 0
  | v :: rest => (if v ∈ rest then 0 else 1) + distinctCount rest
```

Read the second one alongside the order-invariance paragraph above: it
counts each value once, at its last occurrence, and it is a function of the
list — nothing about visit order can be recovered from it, which is
precisely why it is a legitimate specification for a loop whose visit order
the machine chooses. The bridge to the machine's map is a theorem of its
own, `countsList_length : (countsList l).length = distinctCount l`.

**The returned-array adapter** — the rest of the statement vocabulary
(`proofs/GoLeanProofs/Examples/Histogram/Machine.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Histogram/Machine.lean -->
```lean
def histArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .uint64)⟩
```

**The theorem** (`proofs/GoLeanProofs/Examples/Histogram.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Histogram.lean -->
```lean
theorem histogram_ok (n seed q : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64)
    (hq : q < 2 ^ 64) :
    ∃ vals : List Int, vals.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel histogramLowered.typeDefs.toList
            histogramLowered.funcs histHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (q : Int) .uint64]
            histogramLowered.methods ch
          = .ok { values := #[histArr8 vals,
                              .int (occurrences (q : Int) vals : Nat) .uint64,
                              .int (distinctCount vals : Nat) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/Histogram.lean`):

<!-- verbatim: proofs/Audit/Histogram.lean -->
```lean
/-- info: 'GoLean.Examples.Histogram.histogram_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/Histogram.lean -->
```lean
/-- info: 'GoLean.Examples.Histogram.histogram_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and affine: `N = 210·n + 344`. This is the
branch-UNIFORM worst case — 57 steps per setup iteration, 53 per copy
iteration, 84 per counting iteration, 16 per range iteration, with the range
loop charged `n` iterations rather than the `distinctCount vals ≤ n` it
actually runs. **The measured step count is a different number, and the
difference is worth stating plainly.** It is *exactly*
`194·n + 16·distinctCount vals + 344`, verified by direct machine
measurement at `n = 0…8` and found independent of both the choice stream and
`q`. That measurement is **not affine in `n`**, because the family
`v[i] = seed + i%3` stops adding entries to the map after the third value,
so the shipped bound and the measurement coincide only while every value is
new (`n ≤ 3`). The bound the theorem ships is `210·n + 344`; the measurement
is the formula above; neither is presented as the other.

**Status.** NOT DESIGNATED — see the note in *How to read an entry*: this
example post-dates the 2026-08-14 designation, and designation is arc-end
work under user sign-off, so its statement is not walked by the mechanized
statement-TCB gate and not replayed by the Comparator judge. What it does
have, in-build: the `rfl` lowering pins (`histogram_pin`,
`histogramHarnessR_pin`), the golden-lowering guard on both links, and the
axiom pins above. `histogram_readout` is the run-conditioned twin. There is
no ∀-data companion claim here yet (the analogue of wordcount's
`maxCount_total_canonical`) — the subject-level claim over arbitrary value
lists is not proved, and this entry does not imply it.

**Ground.** Differentially green on 13 corpus rows: the all-distinct /
all-same / mode-of-three / query-miss / one / one-miss / empty drivers, and
the relational harness at `harness-r-seven`, `harness-r-eight`,
`harness-r-one`, `harness-r-empty`, `harness-r-miss` (a query that is
absent) and `harness-r-wrap` (`seed = q = 2^63 − 1`, the largest value the
differential driver can pass — the `--arg` int64 ceiling is a *driver*
limit, not a machine one, and it is why no row reaches the true uint64 wrap
region).

## powmod — exponentiation by squaring, modulo `m`

**The Go** (`Corpus/coverage/exec/examples/powmod/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/powmod/main.go -->
```go
func powMod(base, exp, mod uint64) uint64 {
	if mod == 0 {
		return 0
	}
	if mod == 1 {
		return 0
	}
	result := uint64(1)
	base = base % mod
	for exp > 0 {
		if exp%2 == 1 {
			result = result * base % mod
		}
		base = base * base % mod
		exp = exp / 2
	}
	return result
}
```

<!-- verbatim: Corpus/coverage/exec/examples/powmod/main.go -->
```go
// powmod_harness: three-phase shape; setup and test are identities
// (argument-input subject, returned scalar is the observable).
func powmod_harness(base, exp, mod uint64) uint64 {
	r := powMod(base, exp, mod)
	return r
}
```

The harness is the S2 SCALAR shape — the same one `gcd` uses, and for the
same reason: with a scalar in and a scalar out an S3 relational harness
would degenerate, because the pre-state *is* the argument list.

**The specification** (`proofs/GoLeanProofs/Examples/PowMod.lean`) — the
whole postcondition, and it is mathematics rather than a restatement of the
loop:

<!-- verbatim: proofs/GoLeanProofs/Examples/PowMod.lean -->
```lean
def powModAnswer (base exp mod : Nat) : Nat :=
  if mod = 0 then 0 else base ^ exp % mod
```

`base ^ exp` is natural-number exponentiation — unbounded, no modulus, no
squaring — so the theorem below is the *correctness of exponentiation by
squaring*, not "the program computes what the program computes". The
loop-shaped function the proof actually inducts over (`powLoop`) is
proof-side only; it is bridged to this specification by `powLoop_eq` and it
does not appear in the statement.

Two cases are worth reading carefully. `mod = 1` gets **no case of its
own**: Go's second guard returns `0`, and `base ^ exp % 1 = 0`, so the
guard and the mathematics agree and the general branch covers it. `mod = 0`
*is* a case, and it is the program's own documented definition rather than a
mathematical fact — Go's `% 0` panics, and this program chose to return `0`
instead. `powModAnswer` says exactly that, in the open.

**The theorem** (`proofs/GoLeanProofs/Examples/PowMod.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/PowMod.lean -->
```lean
theorem powmod_ok (base exp mod : Nat) (hb : base < 2 ^ 64) (he : exp < 2 ^ 64)
    (hm : mod < 2 ^ 64) (hnw : (mod - 1) * (mod - 1) < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel powmodLowered.typeDefs.toList
          powmodLowered.funcs powmodHarnessFunc
          #[.int (base : Int) .uint64, .int (exp : Int) .uint64,
            .int (mod : Int) .uint64]
          powmodLowered.methods ch
        = .ok { values := #[.int ((powModAnswer base exp mod : Nat) : Int) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/PowMod.lean`):

<!-- verbatim: proofs/Audit/PowMod.lean -->
```lean
/-- info: 'GoLean.Examples.PowMod.powmod_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/PowMod.lean -->
```lean
/-- info: 'GoLean.Examples.PowMod.powmod_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Domain bounds, attributed.** `base < 2^64` and `exp < 2^64` are **Go's
domain** — the uint64 arguments, nothing more. `(mod − 1)² < 2^64` is **the
program's own arithmetic**: it is the no-wrap condition quoted from the Go
source's own comment (equivalently `mod ≤ 2^32`), and it is exactly the
region in which the uint64 multiplies `result * base` and `base * base` do
not wrap. Outside it the program still runs and still returns something —
the corpus row `wrap` pins what — but that something is not
`base ^ exp mod m`, and **this theorem deliberately does not claim it**.
Of the 13 corpus rows exactly **one**, `wrap` (`mod = 2^63 − 1`), lies
outside the theorem's domain; the other twelve are inside it, including
`harness-extreme`, whose `base = 2^63 − 1` and `exp = 2^63 − 2` are
extreme but whose `mod = 999999937` is comfortably below the threshold. `mod < 2^64` is Go's
domain again; it is *logically implied* by the no-wrap condition (below the
threshold `mod` cannot exceed `2^32 + 1`), and it is kept as an explicit
binder so the statement reads uniformly — all three arguments in the uint64
domain, plus the no-wrap condition. The deletion test below confirms the
proof does consume it.

**Fuel bound.** `N = 6027` — a **constant over the whole domain**, which is
the interesting part. The exponent halves every pass, so `exp < 2^64` needs
at most 64 iterations no matter how large it is; the induction is on the
exponent's *bit budget*, not on the exponent, and the bound comes out as
`139 + 92·64`. It is a BOUND, and the measurement is a different number:
the measured step count is exactly `139 + 72·bits(exp) + 20·popcount(exp)`
(probe-verified against the machine — 139 at `exp = 0`, 231 at `exp = 1`,
487 at `exp = 13`), because an odd pass costs 92 steps and an even pass 72.
The two coincide only at `exp = 2^64 − 1`, where every pass is odd. The
guard paths measure 59 (`mod = 0`) and 68 (`mod = 1`). Neither number is
presented as the other.

**∀ choices is vacuous here, and stated anyway.** The subject consumes no
nondeterminism choice; the quantifier records that fact rather than hiding a
`Choices` argument.

**Status.** NOT DESIGNATED — see the note in *How to read an entry*. Added
by the gallery campaign (2026-08-15); designation is arc-end work under user
sign-off, so this statement is not walked by the mechanized statement-TCB
gate and not replayed by the Comparator judge. What it does have, in-build:
the `rfl` lowering pins (`powMod_pin` on the subject, `powmodHarnessFunc_pin`
on the harness), the golden-lowering guard on both links, and the axiom pins
above. Its deletion test was RUN by hand rather than by the gate —
`lean_minimal_hypotheses` on `powmod_ok`, **all five explicit binders
load-bearing**. `powmod_readout` is the run-conditioned twin. There is no
subject-level claim about `powMod` itself apart from the harness run, and
this entry does not imply one.

**Ground.** Differentially green on 13 corpus rows: `exp-zero`, `exp-one`,
`small`, `base-reduce`, `zero-zero`, `large-exp` (`exp = 2^63 − 1`, the
largest the differential driver can pass — the `--arg` int64 ceiling is a
*driver* limit, not a machine one), `mod-one`, `mod-zero`, `wrap` (the one
row inside the wrap region the theorem excludes), the fixed driver
`two-ten` and `two-large`, and the harness at `harness-typical` and
`harness-extreme`. Twelve of the thirteen are inside the theorem's
domain — the differential and the proof overlap on all but `wrap`.

## dotprod — an accumulate loop that genuinely wraps

**The Go** (`Corpus/coverage/exec/examples/dotprod/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/dotprod/main.go -->
```go
func dotProduct(a, b []uint64) uint64 {
	n := len(a)
	if len(b) < n {
		n = len(b)
	}
	acc := uint64(0)
	for i := 0; i < n; i++ {
		acc += a[i] * b[i]
	}
	return acc
}
```

<!-- verbatim: Corpus/coverage/exec/examples/dotprod/main.go -->
```go
// dotprod_harness_r: S3 RELATIONAL harness. Setup builds the families
// a[i] = seed + i and b[i] = i + 1; two copy loops lift them into the
// fixed-cap arrays av and bv (the pass-by-value fragment's
// unbounded-data workaround, zero-padded past n); the observable is
// (av, bv, dot) so the Lean postcondition can relate the returned data
// directly. Real Go, ghost ladder rung 0; harness bound n <= 8.
func dotprod_harness_r(n, seed uint64) ([dotCapN]uint64, [dotCapN]uint64, uint64) {
	a := make([]uint64, n)
	b := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		a[i] = seed + i
		b[i] = i + 1
	}
	var av [dotCapN]uint64
	for i := uint64(0); i < n; i++ {
		av[i] = a[i]
	}
	var bv [dotCapN]uint64
	for i := uint64(0); i < n; i++ {
		bv[i] = b[i]
	}
	dot := dotProduct(a, b)
	return av, bv, dot
}
```

**The specification** (`proofs/GoLeanProofs/Examples/DotProduct.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/DotProduct.lean -->
```lean
def dotSpec (a b : List Int) : Int :=
  (List.zipWith (· * ·) a b).sum % (2 ^ 64 : Int)
```

**This is the entry where the arithmetic wraps, and the claim says so.**
`a[i] * b[i]` and the running accumulator are `uint64`; at large seeds they
genuinely reduce mod 2⁶⁴, and eight corpus rows exercise that deliberately.
The theorem does **not** add a hypothesis excluding the wrap region — that
would throw away exactly the interesting rows. Instead the specification is
the wrapped one: `(Σ aᵢ·bᵢ) mod 2⁶⁴`, **one** modular reduction of the true
integer sum. That single reduction equals the machine's per-step wrapping
because `mod` distributes over the sum — and that equality is *proved*
(`dpAcc_eq`), not assumed. Compare `powmod` just above, which made the
opposite choice and excluded its wrap region; both are honest, and each
entry says which it did.

**The theorem** (`proofs/GoLeanProofs/Examples/DotProduct.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/DotProduct.lean -->
```lean
theorem dotprod_ok (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ av bv : List Int, av.length = n ∧ bv.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel dotprodLowered.typeDefs.toList
            dotprodLowered.funcs dotprodHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            dotprodLowered.methods ch
          = .ok { values := #[dpArr8 av, dpArr8 bv,
                              .int (dotSpec av bv) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/DotProduct.lean`):

<!-- verbatim: proofs/Audit/DotProduct.lean -->
```lean
/-- info: 'GoLean.Examples.DotProduct.dotprod_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/DotProduct.lean -->
```lean
/-- info: 'GoLean.Examples.DotProduct.dotprod_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Domain bounds, attributed.** `seed < 2^64` is **Go's domain**, the whole of
it. `n ≤ 8` is **the program's own arithmetic** — `dotCapN = 8` is visible in
the corpus Go, and the fixed-cap arrays plus zero padding exist only so the
multiplied values can cross Go's pass-by-value observation boundary. The
summation and the modular reduction are **mathematics**. Machine
idealization as elsewhere: empty heap at entry, unbounded heap, allocation
always succeeds.

**Two disclosures the statement does not make on its face.** First, `∃ av bv`
is **family-determined**: the witnesses are `av = [seed, seed+1, …]` (wrapped)
and `bv = [1, …, n]`, and the statement merely avoids naming them — making
the input genuine ∀-data needs the ghost rung-1 annotation, which is designed
and not built. Second, the subject's **min-length guard is not exercised** by
this harness: both slices have length `n`, so `len(b) < n` is false on every
run the theorem covers. The mismatched-length corpus row `uneven` pins that
branch differentially; the theorem claims the harness's runs and nothing
more.

**Fuel bound.** `N = 237·n + 398`, and for this harness the bound is
**exact**: every loop iteration is branch-free, so the composed step count is
an equality rather than a worst case, and the probe-measured counts coincide
with it at `n = 0…8` (398, 635, 872, 1109, 1346, 1583, 1820, 2057, 2294).
Per-loop: 70 steps per setup iteration (two stores), 53 per copy iteration in
each of the two copy loops, 61 per accumulate iteration. Bound and
measurement agree *here*; the entry says so rather than letting the reader
assume it, because in `powmod` and `histogram` they do not.

**Status.** NOT DESIGNATED — see the note in *How to read an entry*. Added by
the gallery campaign (2026-08-15). In-build it has the `rfl` lowering pins
(`dotProduct_pin` on the subject, `dotprodHarnessRFunc_pin` on the harness),
the golden-lowering guard on both links, and the axiom pins above. Its
deletion test was RUN by hand — `lean_minimal_hypotheses` on `dotprod_ok`,
**all three explicit binders load-bearing**. `dotprod_readout` is the
run-conditioned twin.

**Ground.** Differentially green on 18 corpus rows: `four-typical`,
`four-zero-vec`, `four-same`, `four-wrap`, `four-wrap-u64max`, `one`,
`one-wrap`, `one-wrap-u64max`, `empty`, `uneven` (the min-length guard), and
the relational harness at `harness-r-empty`, `harness-r-one`,
`harness-r-mid`, `harness-r-cap`, `harness-r-wrap-max`, `harness-r-wrap-62`,
`harness-r-wrap-u64max` and `harness-r-wrap-63`. The eight wrap rows are the
wrap region — inside the theorem's domain, not excluded from it. Four of them
(`four-wrap-u64max`, `one-wrap-u64max`, `harness-r-wrap-u64max`,
`harness-r-wrap-63`) arrived with extension E1, which lifted the differential
driver's argument domain past the int64 ceiling and so let the corpus reach
the top half of `uint64` directly.

## kadane — maximum subarray sum, the gallery's first signed example

**The Go** (`Corpus/coverage/exec/examples/kadane/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/kadane/main.go -->
```go
func kadane(s []int64) int64 {
	if len(s) == 0 {
		return 0
	}
	best := s[0]
	cur := s[0]
	for i := 1; i < len(s); i++ {
		if cur < 0 {
			cur = s[i]
		} else {
			cur = cur + s[i]
		}
		if cur > best {
			best = cur
		}
	}
	return best
}
```

<!-- verbatim: Corpus/coverage/exec/examples/kadane/main.go -->
```go
// kadane_harness_r: S3 RELATIONAL harness. Setup builds the
// alternating-sign family s[i] = seed + i with every odd index
// negated, copies it into the fixed-cap pre-state array, runs the
// subject, and returns (pre, best) so a postcondition can relate the
// returned data directly. Real Go, ghost ladder rung 0; bound n <= 8.
func kadane_harness_r(n, seed int64) ([kadaneCapN]int64, int64) {
	s := make([]int64, n)
	for i := int64(0); i < n; i++ {
		s[i] = seed + i
		if i%2 == 1 {
			s[i] = -s[i]
		}
	}
	var pre [kadaneCapN]int64
	for i := int64(0); i < n; i++ {
		pre[i] = s[i]
	}
	best := kadane(s)
	return pre, best
}
```

**The specification** (`proofs/GoLeanProofs/Examples/Kadane.lean`) — an
explicit enumeration of every non-empty contiguous segment, and the greatest
of their sums:

<!-- verbatim: proofs/GoLeanProofs/Examples/Kadane.lean -->
```lean
def nePrefixes : List Int → List (List Int)
  | [] => []
  | x :: t => [x] :: (nePrefixes t).map (x :: ·)

/-- All non-empty contiguous segments of `xs`: the non-empty prefixes
starting at position 0, then the segments of the tail. -/
def segments : List Int → List (List Int)
  | [] => []
  | x :: t => nePrefixes (x :: t) ++ segments t

/-- **The maximum subarray sum**: the greatest sum over all non-empty
contiguous segments, `0` for the empty list. -/
def maxSubarraySum (xs : List Int) : Int :=
  (((segments xs).map List.sum).max?).getD 0
```

This is the point of the entry. Kadane's algorithm is a *clever* linear
scan; the specification above is the *obvious* quadratic definition —
enumerate the segments, sum each, take the max. They are not the same
program, and the theorem is that the clever one computes the obvious one's
answer. The scan-shaped functions the induction actually carries
(`kadCur`, `kadBest`) are proof-side and are bridged to `maxSubarraySum`;
they do not appear in the statement. The all-negative case is the classic
trap — the answer is the largest single element, never `0` — and it falls
out of the definition rather than needing a clause, because `segments` are
non-empty by construction; the corpus row `four-negative` pins it on the
oracle side.

**The theorem** (`proofs/GoLeanProofs/Examples/Kadane.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Kadane.lean -->
```lean
theorem kadane_ok (n : Nat) (seed : Int) (hcap : n ≤ 8)
    (hs1 : -(2 ^ 59) ≤ seed) (hs2 : seed ≤ 2 ^ 59) :
    ∃ vals : List Int, vals.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel kadaneLowered.typeDefs.toList
            kadaneLowered.funcs kadaneHarnessRFunc
            #[.int (n : Int) .int64, .int seed .int64]
            kadaneLowered.methods ch
          = .ok { values := #[kadArr8 vals,
                              .int (maxSubarraySum vals) .int64] } := by
```

**Axioms** (pinned in `proofs/Audit/Kadane.lean`):

<!-- verbatim: proofs/Audit/Kadane.lean -->
```lean
/-- info: 'GoLean.Examples.Kadane.kadane_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/Kadane.lean -->
```lean
/-- info: 'GoLean.Examples.Kadane.kadane_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Domain bounds, attributed — and this entry's bound is the narrowest in the
gallery, so read it carefully.** `n ≤ 8` is **the program's own arithmetic**
(`kadaneCapN = 8`, visible in the corpus Go). The segment enumeration and the
maximum are **mathematics**. But `−2^59 ≤ seed ≤ 2^59` is **not Go's int64
domain** — it is a no-wrap window, and it is narrower than the corpus. The
family values are `±(seed+i)` and the running sums can reach a small multiple
of `|seed|`, so the window is exactly what keeps every int64 `normalize` an
identity. **Of the six relational-harness corpus rows, four are inside the
theorem's domain and two are outside it**: `harness-r-maxseed`
(`seed = 2^63 − 1`) and `harness-r-minseed` (`seed = −2^63`) are pinned
differentially and are *not* claimed here. That is a real gap between what
the oracle checks and what the theorem says, and it is stated rather than
elided.

**Fuel bound.** `N = 227·n + 220`, a branch-UNIFORM worst case: 86 steps per
setup iteration on the negated (odd) index and 66 on the even one, 53 per
copy iteration, at most 88 per scan iteration, and the exits. **The measured
step count is a different number and is not affine**, because the setup and
scan branches depend on the data: measured at seed 5 for `n = 0…8` it is
213, 427, 642, 845, 1060, 1263, 1478, 1681, 1896 (cross-checked at seeds −7
and −100). The bound the theorem ships is `227·n + 220`; the measurements are
those numbers; neither is presented as the other.

**∀ choices is vacuous here, and stated anyway.** The subject consumes no
nondeterminism choice.

**Status.** NOT DESIGNATED — see the note in *How to read an entry*. Added by
the gallery campaign (2026-08-15). In-build: the `rfl` lowering pins
(`kadane_pin` on the subject, `kadaneHarnessRFunc_pin` on the harness), the
golden-lowering guard on both links, and the axiom pins above. Its deletion
test was RUN by hand — `lean_minimal_hypotheses` on `kadane_ok`, **all five
explicit binders load-bearing**. `kadane_readout` is the run-conditioned
twin. The theorem covers the harness's runs only, including the `n = 0` path
through the Go's empty-slice guard; the standalone drivers (`kadaneFour`,
`kadaneThree`, `kadaneOne`, `kadaneEmpty`) are pinned differentially and are
not claimed.

**Ground.** Differentially green on 14 corpus rows: `four-mixed`,
`four-positive`, `four-negative` (the all-negative trap), `four-same`,
`four-extremes`, `three`, `one`, `empty`, and the relational harness at
`harness-r-empty`, `harness-r-one`, `harness-r-mid`, `harness-r-eight`,
`harness-r-maxseed` and `harness-r-minseed` — the last two outside the
theorem's seed window, as above.

## dedup — adjacent-only compaction, in place

**The Go** (`Corpus/coverage/exec/examples/dedup/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/dedup/main.go -->
```go
func dedupAdjacent(s []uint64) []uint64 {
	k := 0
	for i := 0; i < len(s); i++ {
		if k == 0 || s[i] != s[k-1] {
			s[k] = s[i]
			k++
		}
	}
	return s[:k]
}
```

<!-- verbatim: Corpus/coverage/exec/examples/dedup/main.go -->
```go
// dedup_harness_r: the S3 RELATIONAL harness. Setup builds the family
// s[i] = seed + i/2 (integer division, so adjacent pairs repeat), the
// pre array snapshots it, the subject compacts in place, the post
// array holds the surviving prefix zero-padded, and k is its length.
func dedup_harness_r(n, seed uint64) ([dedupCapN]uint64, [dedupCapN]uint64, uint64) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i/2
	}
	var pre [dedupCapN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	r := dedupAdjacent(s)
	var post [dedupCapN]uint64
	for i := 0; i < len(r); i++ {
		post[i] = r[i]
	}
	return pre, post, uint64(len(r))
}
```

**The specification** (`proofs/GoLeanProofs/Examples/DedupAdjacent.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/DedupAdjacent.lean -->
```lean
def dedupAdjTail (prev : Int) : List Int → List Int
  | [] => []
  | x :: xs => if x = prev then dedupAdjTail x xs
               else x :: dedupAdjTail x xs

/-- **The specification**: adjacent-only deduplication. The first
element is always kept; every later element is kept iff it differs
from the last kept one. -/
def dedupAdj : List Int → List Int
  | [] => []
  | x :: xs => x :: dedupAdjTail x xs
```

**"Adjacent" is the whole content of this entry, and it is the thing readers
get wrong.** `dedupAdjacent` is not "remove duplicates" — it collapses only
*runs* of equal neighbours. The input `1, 2, 1, 2` survives entirely
intact: no element equals its predecessor, so nothing is dropped, even
though only two distinct values appear. The specification above says exactly
that ("kept iff first, or differs from the last KEPT one") and the corpus row
`four-alternating` pins it against the real Go. A specification that said
"the distinct values" would be a different, false claim.

**The theorem** (`proofs/GoLeanProofs/Examples/DedupAdjacent.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/DedupAdjacent.lean -->
```lean
theorem dedup_ok (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ vals : List Int, vals.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel dedupLowered.typeDefs.toList
            dedupLowered.funcs dedupHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            dedupLowered.methods ch
          = .ok { values := #[ddArr8 vals, ddArr8 (dedupAdj vals),
              .int ((dedupAdj vals).length : Nat) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/DedupAdjacent.lean`):

<!-- verbatim: proofs/Audit/DedupAdjacent.lean -->
```lean
/-- info: 'GoLean.Examples.DedupAdjacent.dedup_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/DedupAdjacent.lean -->
```lean
/-- info: 'GoLean.Examples.DedupAdjacent.dedup_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**What the machine had to be shown, and why it is interesting.** The
compaction is *in place*: it writes `s[k]` while reading `s[i]` and `s[k-1]`,
with `k ≤ i` throughout, so the slice is simultaneously the input being read
and the output being built. The invariant that carries it is that after
processing the first `i` elements with `k` kept, the slice is
`dedupAdj (first i elements)` followed by the still-untouched original tail —
the stale region between `k` and `i` is never read again, because the guard
reads only `s[k-1]`. A second machine fact fell out of the proof and is worth
recording: the guard `k == 0 || s[i] != s[k-1]` is genuinely **lazy** in the
machine — on the `k == 0` branch the `s[k-1]` read never happens, so the
out-of-range index the reader worries about is never evaluated. The raw
segments show that directly.

**Domain bounds, attributed.** `n ≤ 8` is **the program's own arithmetic**
(`dedupCapN = 8`, visible in the corpus Go). `seed < 2^64` is **Go's
domain**, all of it — the setup family is `seed + i/2` and wraps freely; no
hypothesis excludes it. The deduplication itself is **mathematics**. Machine
idealization as elsewhere.

**`∃ vals` is family-determined.** The witness is the setup family
`seed + i/2` (integer division, so adjacent pairs repeat and the example has
something to collapse); the statement merely avoids naming it. Genuine
∀-data needs the ghost rung-1 annotation, which is designed and not built.

**Fuel bound.** `N = 263·n + 361` — a branch-UNIFORM bound that charges every
element the widest branch (the 98-step "keep, with `k ≠ 0`" path) plus a
55-step post-copy slot. **The measurement is a different, input-dependent
number**: `361` at `n = 0`, and `177·n + 86·K + 343` for `n ≥ 1`, where `K`
is the number of survivors (the family gives `K = ⌈n/2⌉`). Probe-verified at
`n = 0, 1, 2, 3, 5, 8`: 361, 606, 783, 1046, 1486, 2103 — and 2103 again at
the wrap-boundary seed `2^64 − 2`. The bound the theorem ships is
`263·n + 361`; the measurement is the formula above; neither is presented as
the other.

**∀ choices is vacuous here, and stated anyway.**

**Status.** NOT DESIGNATED — see the note in *How to read an entry*. Added by
the gallery campaign (2026-08-15). In-build: the `rfl` lowering pins
(`dedupAdjacent_pin` on the subject, `dedupHarnessRFunc_pin` on the harness),
the golden-lowering guard on both links, and the axiom pins above. Its
deletion test was RUN by hand — `lean_minimal_hypotheses` on `dedup_ok`,
**all three explicit binders load-bearing**. `dedup_readout` is the
run-conditioned twin.

**Ground.** Differentially green on 13 corpus rows: `four-all-same`,
`four-distinct`, `four-alternating` (the adjacent-only guard),
`four-pairs`, `four-extremes`, `four-first`, `one`, `empty`, and the
relational harness at `harness-r-empty`, `harness-r-one`, `harness-r-mid`,
`harness-r-cap` and `harness-r-big`. All five harness rows are inside the
theorem's domain.

## palin — array palindrome check (two-index inward walk, early return)

**The Go** (`Corpus/coverage/exec/examples/palin/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/palin/main.go -->
```go
func isPalindrome(s []uint64) uint64 {
	i := 0
	j := len(s) - 1
	for i < j {
		if s[i] != s[j] {
			return 0
		}
		i++
		j--
	}
	return 1
}
```

<!-- verbatim: Corpus/coverage/exec/examples/palin/main.go -->
```go
// palin_harness_r: the S3 RELATIONAL harness. Setup builds the
// alternating family s[i] = seed + i%2 (go-run verified: verdict 1 for
// n <= 1 and odd n, verdict 0 for even n >= 2); the copy loop lifts the
// pre-state into a fixed-cap array and the subject's verdict rides
// alongside. Real Go, ghost ladder rung 0.
func palin_harness_r(n, seed uint64) ([palinCapN]uint64, uint64) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i%2
	}
	var pre [palinCapN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	v := isPalindrome(s)
	return pre, v
}
```

**The claim.** For every `n ≤ 8` and every `seed < 2^64`,
`palin_harness_r(n, seed)` finishes normally, at every nondeterminism
choice, and returns two values: a list `pre` of length `n` (as the fixed-cap
array the Go returns) and a verdict which is `1` exactly when *that very
list* reads the same forwards and backwards. **The postcondition is a
relation over the RETURNED data** — the setup family does not appear in it.

**The whole mathematical content of the claim is one line.** The
specification is `palinSpec xs = if xs.reverse = xs then 1 else 0`: list
reversal, written the way a mathematician would write it. It contains no
indices, no halves, no loop. The Go program does something quite different —
it walks two indices inward and stops in the middle, inspecting only the
pairs `(t, len−1−t)` for `t < len/2`. That the two agree is a *theorem*
(`palin_iff_half`), not a definition, and it is where all the index
arithmetic in this example lives. This is the separation the gallery is for:
you read the claim without reading the algorithm.

**The shape that is new here: an early return.** Every other subject in this
gallery leaves its loop one way. `isPalindrome` leaves two ways that are not
symmetric — the loop's exit test when the walk meets in the middle, and a
`return 0` from *inside* the body at the first mismatched pair. So the
machine-level loop lemma cannot stop at "the loop head after `μ`
iterations"; it runs all the way to the driver terminal, and its content is
that **both exits deliver the same observable**. The loop's own `i` and `j`
are existentially quantified there, because the two exits stop at different
indices and nothing the harness returns depends on which.

Four honesty clauses, none of them small print:

* **The cap `n ≤ 8` is a toy bound, and it is the price of this style.**
  Go's pass-by-value fragment cannot return unbounded data, so the harness
  returns `[palinCapN]uint64` with `palinCapN = 8` — visible in the Go — and
  the copy loop and the zero padding exist *only* so the checked array can
  cross the observation boundary. The theorem carries `n ≤ 8` as a
  hypothesis rather than hiding it.
* **`∃ pre` is still family-determined.** The witness the proof supplies is
  `s[i] = (seed + i%2) mod 2^64`; the statement merely does not *say* so.
  What the S3 form buys is on the postcondition side — the verdict is
  asserted about observed output. Turning the input into genuine ∀-data
  needs the ghost rung-1 annotation, which is designed and not built. The
  family is not a degenerate choice: it produces **both** verdicts (`1` for
  `n ≤ 1` and odd `n`, `0` for even `n ≥ 2`), so the corpus rows exercise
  both branches of the subject against `go run`.
* **`n = 0` is in the domain and is not a hole.** The Go sets `j = -1`, the
  loop never runs, the verdict is `1`, and the empty list is indeed a
  palindrome. The row `harness-r-empty` pins that against `go run`.
* **Machine idealization**, as elsewhere: entry from an empty heap, an
  unbounded heap, allocation always succeeds. The three arithmetic domains
  are separated as usual: `n ≤ 8` is *the program's own* (the array cap),
  `seed < 2^64` is *Go's* uint64 domain at the call boundary, and list
  reversal is mathematics.

**The specification function**
(`proofs/GoLeanProofs/Examples/ArrayPalindrome/Pure.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/ArrayPalindrome/Pure.lean -->
```lean
def palinSpec (xs : List Int) : Int :=
  if xs.reverse = xs then 1 else 0
```

**The returned-array adapter** — the rest of the statement vocabulary
(`proofs/GoLeanProofs/Examples/ArrayPalindrome/Machine.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/ArrayPalindrome/Machine.lean -->
```lean
def palArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .uint64)⟩
```

**The theorem** (`proofs/GoLeanProofs/Examples/ArrayPalindrome.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/ArrayPalindrome.lean -->
```lean
theorem palin_ok (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel palinLowered.typeDefs.toList
            palinLowered.funcs palinHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            palinLowered.methods ch
          = .ok { values := #[palArr8 pre,
                              .int (palinSpec pre) .uint64] } := by
```

**The first-order readout**, for a reader who would rather not unfold
`palinSpec` at all (`proofs/GoLeanProofs/Examples/ArrayPalindrome.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/ArrayPalindrome.lean -->
```lean
theorem palin_verdict_iff (n seed : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        ∃ v : Int,
          runFunctionWithContextM fuel palinLowered.typeDefs.toList
              palinLowered.funcs palinHarnessRFunc
              #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
              palinLowered.methods ch
            = .ok { values := #[palArr8 pre, .int v .uint64] }
          ∧ (v = 1 ↔ pre.reverse = pre) := by
```

**Axioms** (pinned in `proofs/Audit/ArrayPalindrome.lean`):

<!-- verbatim: proofs/Audit/ArrayPalindrome.lean -->
```lean
/-- info: 'GoLean.Examples.ArrayPalindrome.palin_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/ArrayPalindrome.lean -->
```lean
/-- info: 'GoLean.Examples.ArrayPalindrome.palin_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and affine: `N = 144·n + 298`. This is the
branch-UNIFORM worst case — 57 steps per setup iteration, 53 per copy
iteration, 68 per full subject iteration (of which there are at most `n/2`,
charged here as `34·n`), plus the fixed `298` covering entry, the three loop
exits, the one frame entry, the subject's prologue and the epilogue. **The
measured step counts are different numbers, and the difference is worth
stating plainly**: `277` at `n = 0`, `387` at `n = 1`, then `518`/`738`/`1178`
at `n = 2`/`4`/`8` (the walk bails at the first pair) against `675`/`963` at
`n = 3`/`5` (the walk completes). That measurement is **not affine in `n`**
and could not be, because how far the walk gets depends on the data. The
bound the theorem ships is `144·n + 298`; the measurements are the numbers
above; neither is presented as the other.

**Status.** NOT DESIGNATED — see the note in *How to read an entry*: this
example post-dates the 2026-08-14 designation, and designation is arc-end
work under user sign-off, so its statement is not walked by the mechanized
statement-TCB gate and not replayed by the Comparator judge. What it does
have, in-build: the `rfl` lowering pins (`palin_pin`,
`palinHarnessRFunc_pin`), the golden-lowering guard on both links, and the
axiom pins above. `palin_readout` is the run-conditioned twin, and
`palin_verdict_iff` is the first-order readout quoted above. There is no
∀-data companion claim here: the subject-level statement about arbitrary
`[]uint64` inputs is not proved, and this entry does not imply it.

**Ground.** Differentially green on 14 corpus rows: the four-element drivers
(`four-palin`, `four-nonpalin`, `four-allsame`, `four-big`), the
three-element pair (`three-palin`, `three-nonpalin`), the singleton (`one`)
and the empty slice (`empty`), plus the relational harness at
`harness-r-empty`, `harness-r-one`, `harness-r-four`, `harness-r-five`,
`harness-r-eight` and `harness-r-big` (`seed = 2^63 − 1`, the largest value
the differential driver can pass — the `--arg` int64 ceiling is a *driver*
limit, not a machine one).

## strrev — string reversal by byte concatenation, with a palindrome verdict

**The Go** (`Corpus/coverage/exec/examples/strrev/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/strrev/main.go -->
```go
// reverseString: the subject — walk the bytes from the end and build
// the reversal by concatenation.
func reverseString(s string) string {
	out := ""
	for i := len(s) - 1; i >= 0; i-- {
		out += string(rune(s[i]))
	}
	return out
}
```

<!-- verbatim: Corpus/coverage/exec/examples/strrev/main.go -->
```go
// isStringPalindrome: companion subject — two-index byte walk; returns
// 1 if s reads the same forwards and backwards, else 0.
func isStringPalindrome(s string) uint64 {
	i := 0
	j := len(s) - 1
	for i < j {
		if s[i] != s[j] {
			return 0
		}
		i++
		j--
	}
	return 1
}
```

<!-- verbatim: Corpus/coverage/exec/examples/strrev/main.go -->
```go
// buildStr: the differential driver passes only integer arguments, so
// every corpus subject builds its string internally from (n, seed).
func buildStr(n, seed uint64) string {
	out := ""
	for i := uint64(0); i < n; i++ {
		out += string(rune(97 + (seed+i)%26))
	}
	return out
}
```

<!-- verbatim: Corpus/coverage/exec/examples/strrev/main.go -->
```go
// strrev_harness_r: the S3 RELATIONAL harness — setup builds the
// string from (n, seed), the subject reverses it, and the verdict
// reports whether the ORIGINAL is a palindrome. The returned
// (pre, post, isPalin) triple is the observable; strings cross the
// observation boundary by contents (tag "string"), so both pre and
// post are genuinely observed.
func strrev_harness_r(n, seed uint64) (string, string, uint64) {
	pre := buildStr(n, seed)
	post := reverseString(pre)
	isPalin := isStringPalindrome(pre)
	return pre, post, isPalin
}
```

**The claim.** For every `n < 2^63` and every `seed < 2^64`,
`strrev_harness_r(n, seed)` finishes normally, at every nondeterminism
choice, and returns three values: a byte string `pre` of length `n`, the
string holding exactly `pre`'s bytes in reverse order, and a verdict that
is `1` exactly when `pre` reads the same both ways. **The postcondition is
a relation over the RETURNED data** — `post` is `pre.reverse` and the
verdict is `palinSpec pre`; neither the setup family nor any index
arithmetic appears in it.

**This is the gallery's first entry with NO fixed-cap toy bound on the
returned data.** Every previous relational entry returns its data through
a fixed-size array (`[8]uint64` and the copy-loop-plus-zero-padding
workaround), because Go's pass-by-value fragment cannot return unbounded
aggregates. Strings can: they cross the observation boundary by CONTENTS
(`{"tag":"string","bytes":[...]}`), so all three returned values are
genuinely observed at every length and there is no `n ≤ 8` anywhere in
the statement. The bounds that DO appear are attributed below — both are
Go's own domains, not caps of ours.

Honesty clauses, none of them small print:

* **The reversal claim is byte-level, and the ASCII invariant is what
  makes it the Go's.** `reverseString` rebuilds through
  `string(rune(s[i]))`, and the machine models that round-trip
  FAITHFULLY: it is the full UTF-8 encoder, so a byte `≥ 128` would come
  back as a two-byte encoding and the Go would NOT compute the byte
  reversal of such a string. The theorem is about the harness, whose
  built strings are all-ASCII (`a`–`z`), and the proof carries
  `∀ b ∈ pre, b.toNat < 128` (`strFamily_ascii`) through the reverse
  loop explicitly. No claim is made about `reverseString` on non-ASCII
  strings — and that restraint is the machine being right about Go, not
  a proof shortcut.
* **`∃ pre` is still family-determined.** The witness is
  `strFamily n seed` — byte `i` is `97 + ((seed+i) mod 2^64) mod 26`,
  which is the program's OWN uint64 arithmetic including the wrap (for
  `seed + i ≥ 2^64` the inner wrap changes the letter, and the family
  says so rather than pretending `%` distributes). The statement merely
  avoids SAYING so; genuine ∀-input data needs the ghost rung-1
  annotation, which is designed and not built.
* **Domain bounds, attributed.** `seed < 2^64` is Go's uint64 domain at
  the call boundary. `n < 2^63` is Go's `int` domain: both subjects run
  `int` loop indices over the string (`i := len(s) - 1`, `j := len(s) -
  1`), so a length past `2^63 − 1` could not even be indexed — the bound
  is the language's, not the mathematics'. There is no bound from the
  proof method itself.
* **`n = 0` is included**: `reverseString` sets `i = -1` and
  `isStringPalindrome` sets `j = -1`, no loop body runs, and the empty
  string is its own reversal and a palindrome. The corpus rows
  `harness-empty`/`palin-empty` pin that against `go run`.
* **Machine idealization**, as elsewhere: entry from an empty heap, an
  unbounded heap, allocation always succeeds — and string VALUES of
  unbounded length, which is exactly Go-the-language (the spec caps
  `int` indexing, not string size; a real machine would exhaust memory
  first). The theorem's domain is the model's, not the practical one.

**The specification vocabulary**
(`proofs/GoLeanProofs/Examples/StringReverse/Pure.lean` and
`.../Machine.lean`). The whole mathematical content is `List.reverse`
plus:

<!-- verbatim: proofs/GoLeanProofs/Examples/StringReverse/Pure.lean -->
```lean
def palinSpec (xs : List UInt8) : Int :=
  if xs.reverse = xs then 1 else 0
```

<!-- verbatim: proofs/GoLeanProofs/Examples/StringReverse/Machine.lean -->
```lean
def gs (l : List UInt8) : GoString := ⟨⟨l⟩⟩
```

(`gs` is the two-constructor bridge from a byte list to the machine's
string value — the returned strings are `.string (gs pre)` etc.; a Go
string in the machine IS its byte array. The Go decides the verdict by
a half scan with an early return; `palin_iff_half` — the ArrayPalindrome
bridge re-derived one type over — is proof method, not statement.)

**The theorem** (`proofs/GoLeanProofs/Examples/StringReverse.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/StringReverse.lean -->
```lean
theorem strrev_ok (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∃ pre : List UInt8, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel strrevLowered.typeDefs.toList
            strrevLowered.funcs strrevHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            strrevLowered.methods ch
          = .ok { values := #[.string (gs pre),
                              .string (gs pre.reverse),
                              .int (palinSpec pre) .uint64] } := by
```

The first-order readout corollary (statement-TCB doctrine) is
`strrev_verdict_iff`: over the returned byte lists, `v = 1 ↔ post =
pre` — the verdict is `1` exactly when the returned reversal equals the
returned original, with no `palinSpec` in sight. (Its `∃ post` is
family-determined the same way `∃ pre` is; the headline pins
`post = pre.reverse`.)

**Axioms** (pinned in `proofs/Audit/StringReverse.lean`):

<!-- verbatim: proofs/Audit/StringReverse.lean -->
```lean
/-- info: 'GoLean.Examples.StringReverse.strrev_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/StringReverse.lean -->
```lean
/-- info: 'GoLean.Examples.StringReverse.strrev_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project
axioms.

**Fuel bound.** Explicit and affine: `N = 156·n + 372`. This is the
branch-UNIFORM worst case — 65 steps per build iteration, 57 per
reverse iteration, 68 per full palindrome iteration with the palindrome
loop charged its `n/2` maximum (as `34·n`), plus the fixed `372` of
entry, three frame entries, three prologues, three first dispatches,
two inter-frame exits and the worst palindrome tail. **The measured
step counts are different numbers, recorded separately and not
presented as the bound**: `351` at `n = 0`, `473` at `n = 1`, and
`122·n + 372` for the measured `n = 2/3/4/8` (`616/738/860/1348`) —
the alternating-letter family mismatches at its first pair, so the
palindrome loop's `68·(n/2)` worst case is never exercised past one
partial iteration by this family, and the measurement is
family-dependent where the bound is not.

**Status.** NOT DESIGNATED — this example post-dates the 2026-08-14
designation set; designation is arc-end work under user sign-off, so
its statement is not walked by the mechanized statement-TCB gate and
not replayed by the Comparator judge. What it does have, in-build: FOUR
`rfl` lowering pins (`buildStr_pin`, `reverseString_pin`,
`isStringPalindrome_pin`, `strrevHarnessRFunc_pin` — every function the
run steps through), the golden-lowering guard on both links, the axiom
pins above, and a hand-run deletion test (both hypotheses load-bearing:
dropping `hn` breaks three normalization goals, dropping `hseed` two).
`strrev_readout` is the run-conditioned twin. One toolchain finding is
recorded in the module: `derive_entry_eq` fails closed on string result
defaults, so this example's entry equation is hand-written in exactly
the macro's emitted shape.

**Ground.** Differentially green on 12 corpus rows: the literal drivers
(`rev-lit`, `palin-lit` — the positive multi-character palindrome runs
over a literal, because the build family's adjacent letters always
differ), the subject drivers (`build-mid`, `rev-built`, `palin-one`,
`palin-no`, `palin-empty` with an extreme seed), and the relational
harness at `harness-empty`, `harness-one`, `harness-mid`,
`harness-cap`, `harness-extreme` (`seed = 2^63 − 1`, the largest value
the differential driver can pass — the `--arg` int64 ceiling is a
driver limit, not a machine one).

## twosum — first pair summing to a target (nested loops, early return)

**The Go** (`Corpus/coverage/exec/examples/twosum/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/twosum/main.go -->
```go
// twoSum: the O(n^2) double loop. Returns the FIRST index pair (i, j)
// in scan order with i < j and s[i]+s[j] == target (wrapping uint64
// addition). When no pair exists it returns
// (uint64(len(s)), uint64(len(s))) — an out-of-range sentinel.
func twoSum(s []uint64, target uint64) (uint64, uint64) {
	n := uint64(len(s))
	for i := uint64(0); i < n; i++ {
		for j := i + 1; j < n; j++ {
			if s[i]+s[j] == target {
				return i, j
			}
		}
	}
	return n, n
}
```

<!-- verbatim: Corpus/coverage/exec/examples/twosum/main.go -->
```go
// twosum_harness_r: the S3 RELATIONAL harness. Setup builds the family
// s[i] = seed + i (wrapping uint64 addition); a copy loop lifts the
// pre-state into a fixed-cap array (the pass-by-value fragment's
// unbounded-data workaround); then the subject runs. Returning
// (vals, i, j) lets the postcondition relate the returned data
// directly: either i < j < n with vals[i]+vals[j] = target and (i, j)
// first in scan order, or i = j = n (the not-found sentinel).
// Real Go, ghost ladder rung 0.
func twosum_harness_r(n, seed, target uint64) ([twosumCapN]uint64, uint64, uint64) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i
	}
	var vals [twosumCapN]uint64
	for i := uint64(0); i < n; i++ {
		vals[i] = s[i]
	}
	i, j := twoSum(s, target)
	return vals, i, j
}
```

**The claim.** For every `n ≤ 8`, every `seed < 2^64` and every
`target < 2^64`, `twosum_harness_r(n, seed, target)` finishes normally, at
every nondeterminism choice, and returns three values: a list `vals` of
length `n` (as the fixed-cap array the Go returns) together with the index
pair `twoSumSpec vals target` — the FIRST pair `(i, j)` in scan order
(outer index ascending, inner ascending, always `i < j`) whose wrapping
sum `(vals[i] + vals[j]) % 2^64` equals the target, or the sentinel
`(n, n)` when no pair does. **The postcondition is a relation over the
RETURNED data** — the pair is a function of the very array the program
handed back. No family function appears in the claim.

The honesty clauses, none of them small print:

* **`twoSumSpec` is a first-search recursion**, shaped like the scan it
  specifies — by itself it would be a program-shaped spec. The genuinely
  first-order content is shipped alongside: `twosum_first_pair` restates
  the theorem as the explicit disjunction — *either* `i < j < n`, the
  wrapped sum hits, and no scan-earlier pair hits; *or* `i = j = n` and no
  pair hits at all — with no reference to `twoSumSpec`, using only
  `List.getD`, `%` and `<`.
* **The wrapped sum is the program's own arithmetic.** The `% 2^64` in the
  claim is Go's uint64 addition on this fragment (spelled with `Int.emod`),
  not a proof convenience; the domain bounds `seed, target < 2^64` are Go's
  uint64 domain; `n ≤ 8` is the program's own array cap (below); the
  first-pair ordering content is mathematics.
* **The cap `n ≤ 8` is a toy bound, and it is the price of this style.**
  Go's pass-by-value fragment cannot return unbounded data, so the harness
  returns `[twosumCapN]uint64` with `twosumCapN = 8` — visible in the Go —
  and the copy loop and the zero padding exist *only* so the searched array
  can cross the observation boundary. The theorem carries `n ≤ 8` as a
  hypothesis rather than hiding it.
* **`∃ vals` is still family-determined.** The witness the proof supplies
  is `s[i] = (seed + i) mod 2^64`; the statement merely does not *say* so.
  Turning the input into genuine ∀-data needs the ghost rung-1 annotation,
  which is designed and not built.
* **`n = 0` and `n = 1` are included** and are not degenerate holes: no
  pair exists, both loops fall through, and the sentinel comes back —
  pinned against `go run` by the `harness-r-empty` / `harness-r-one` rows.

As elsewhere, the machine idealizes allocation (entry from an empty heap,
an unbounded heap, allocation always succeeds) — and this example leans on
that idealization harder than its siblings: each outer iteration of
`twoSum` declares a fresh inner `j` and loop flag, so the machine allocates
two new cells per outer round, all of which succeed by fiat.

**The specification function** (`proofs/GoLeanProofs/Examples/TwoSum/Pure.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/TwoSum/Pure.lean -->
```lean
def findFrom (xs : List Int) (tgt : Int) (i j : Nat) : Option Nat :=
  if _h : j < xs.length then
    if (xs.getD i 0 + xs.getD j 0) % 2 ^ 64 = tgt then some j
    else findFrom xs tgt i (j + 1)
  else none
termination_by xs.length - j
```

<!-- verbatim: proofs/GoLeanProofs/Examples/TwoSum/Pure.lean -->
```lean
def findPair (xs : List Int) (tgt : Int) (i : Nat) : Option (Nat × Nat) :=
  if _h : i < xs.length then
    match findFrom xs tgt i (i + 1) with
    | some j => some (i, j)
    | none => findPair xs tgt (i + 1)
  else none
termination_by xs.length - i
```

<!-- verbatim: proofs/GoLeanProofs/Examples/TwoSum/Pure.lean -->
```lean
def twoSumSpec (xs : List Int) (tgt : Int) : Int × Int :=
  match findPair xs tgt 0 with
  | some (i, j) => ((i : Int), (j : Int))
  | none => ((xs.length : Int), (xs.length : Int))
```

**The returned-array adapter** — the S3 statement vocabulary
(`proofs/GoLeanProofs/Examples/TwoSum/Machine.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/TwoSum/Machine.lean -->
```lean
def tsArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .uint64)⟩
```

**The theorem** (`proofs/GoLeanProofs/Examples/TwoSum.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/TwoSum.lean -->
```lean
theorem twosum_ok (n seed target : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) (htgt : target < 2 ^ 64) :
    ∃ vals : List Int, vals.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel twosumLowered.typeDefs.toList
            twosumLowered.funcs twosumHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (target : Int) .uint64]
            twosumLowered.methods ch
          = .ok { values := #[tsArr8 vals,
              .int (twoSumSpec vals (target : Int)).1 .uint64,
              .int (twoSumSpec vals (target : Int)).2 .uint64] } := by
```

**The first-order corollary** (same file; the statement-TCB readout —
what the pair MEANS, with `twoSumSpec` never mentioned):

<!-- verbatim: proofs/GoLeanProofs/Examples/TwoSum.lean -->
```lean
theorem twosum_first_pair (n seed target : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) (htgt : target < 2 ^ 64) :
    ∃ vals : List Int, vals.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        ∃ i j : Int,
          runFunctionWithContextM fuel twosumLowered.typeDefs.toList
              twosumLowered.funcs twosumHarnessRFunc
              #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
                .int (target : Int) .uint64]
              twosumLowered.methods ch
            = .ok { values := #[tsArr8 vals, .int i .uint64,
                .int j .uint64] }
          ∧ ((∃ a b : Nat, i = (a : Int) ∧ j = (b : Int)
                ∧ a < b ∧ b < n
                ∧ (vals.getD a 0 + vals.getD b 0) % 2 ^ 64
                    = (target : Int)
                ∧ ∀ a' b' : Nat, a' < b' → b' < n →
                    (a' < a ∨ (a' = a ∧ b' < b)) →
                    ¬ (vals.getD a' 0 + vals.getD b' 0) % 2 ^ 64
                        = (target : Int))
            ∨ (i = (n : Int) ∧ j = (n : Int)
                ∧ ∀ a b : Nat, a < b → b < n →
                    ¬ (vals.getD a 0 + vals.getD b 0) % 2 ^ 64
                        = (target : Int))) := by
```

**Axioms** (pinned in `proofs/Audit/TwoSum.lean`):

<!-- verbatim: proofs/Audit/TwoSum.lean -->
```lean
/-- info: 'GoLean.Examples.TwoSum.twosum_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and QUADRATIC — the honest shape of a nested
loop: `N = 57·n² + 212·n + 303`. It is branch-uniform: each of the at most
`n` outer rows is charged its worst case (`57·n + 106`, covering the fresh
inner-counter allocation, up to `n−1` inner iterations at 57 steps each,
and either exit), on top of the setup/copy loops at 53 steps per iteration
and the fixed entry/call/epilogue overheads. The *measured* counts are
smaller and data-dependent, because the early return skips everything
after the first hit — the exact no-pair law is
`303 + 206·n + 57·n·(n−1)/2` (measured: 303/509/772/1469/3547 at
`n = 0/1/2/4/8`), while a hit at `(0,1)` costs 607 at `n = 2` and 1243 at
`n = 8`. The bound quoted here is the one the theorem actually ships;
the measurements are recorded, not shipped.

**Status.** NOT DESIGNATED — see the note in *How to read an entry*: this
example post-dates the 2026-08-14 designation, and designation is arc-end
work under user sign-off, so its statement is not walked by the mechanized
statement-TCB gate and not replayed by the Comparator judge. It is absent
from `Examples/Targets.lean`, the `scripts/ci` Targets allowlist,
`Audit.lean`'s designated-name list and the Comparator Challenge's
trusted closure. `twosum_readout` is the run-conditioned twin;
`twosum_first_pair` is the first-order corollary quoted above.
Deletion test run 2026-08-15 by re-elaborating the
headline with each explicit binder removed: `hcap`, `hseed` and `htgt`
each break the proof (two sites each). No decorative hypothesis.

**Ground.** Differentially green on 14 corpus rows: the four-element
driver at a middle/first/last/absent/duplicate/degenerate-duplicate hit,
an `int64`-boundary extreme, the one-element and empty drivers, and the
relational harness at `n = 0` and `n = 1` (both below the two-element
minimum, so both return the sentinel), `n = 5` — seed 10, target 27,
which hits at `(3, 4)`, the FINAL adjacent pair, `13 + 14` — `n = 8` —
seed 1, target 9, which hits at `(0, 7)`, the WIDEST pair, `1 + 8` — and
the wrap-region seed `9223372036854775807` with target `0`, which hits
at `(0, 2)`: `s[0] + s[2] = (2^63 − 1) + (2^63 + 1) = 2^64 ≡ 0`.
[All three descriptors corrected 2026-08-16, fix round #3, each
recomputed from the row's own `cases.tsv` args through the Go oracle.
They read "`n = 5` (interior hit)" — it is the last two of five;
"`n = 8` (adjacent hit at the head)" — it is the first and last of
eight, the least adjacent pair there is; and the wrap row was described
as returning the no-pair sentinel, which is the opposite of what it
does.]

What no row reaches, said plainly: the theorem covers every
`seed, target < 2^64`, including the region where `seed + i` and the pair
sums wrap past `2^64` — but the differential driver parses `int64`
arguments, so no corpus row exercises a seed or target above `2^63 − 1`
(the `harness-r-wrap` row sits exactly at that boundary, where the pair
sums `≈ 2^64` DO wrap — and wrapping is not merely tolerated there but
load-bearing: that row's hit at `(0, 2)` exists ONLY because
`(2^63 − 1) + (2^63 + 1)` wraps to `0`, so the row is a positive test of
the wrapped-addition semantics rather than a boundary that degrades to
the sentinel).
The full uint64 wrap region was checked on the machine only, with no
`go run` oracle in the loop — extending the driver past `int64` is the
recorded E1 extension (dotprod is its designated consumer).

## selsort — selection sort, the sorted output returned and related to the input

**The Go** (`Corpus/coverage/exec/examples/selsort/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/selsort/main.go -->
```go
func selectionSort(s []uint64) {
	for i := 0; i < len(s); i++ {
		m := i
		for j := i + 1; j < len(s); j++ {
			if s[j] < s[m] {
				m = j
			}
		}
		s[i], s[m] = s[m], s[i]
	}
}
```

<!-- verbatim: Corpus/coverage/exec/examples/selsort/main.go -->
```go
// selsortCapN: the fixed observation cap of the S3 relational harness.
// Both returned arrays are `[selsortCapN]uint64`, so the harness's own
// bound is `n <= 8` — plainly visible in the source.
const selsortCapN = 8
```

<!-- verbatim: Corpus/coverage/exec/examples/selsort/main.go -->
```go
// selsort_harness_r: the S3 RELATIONAL harness. Setup builds a
// genuinely-unsorted family by iterating a wrapping LCG from `seed`;
// a copy loop lifts it into `pre` (the fixed-cap array is the
// pass-by-value fragment's unbounded-data workaround), the subject
// sorts in place, and a second copy loop lifts the result into
// `post`, so a postcondition can relate the returned data directly.
// Real Go, ghost ladder rung 0.
func selsort_harness_r(n, seed uint64) ([selsortCapN]uint64, [selsortCapN]uint64) {
	s := make([]uint64, n)
	x := seed
	for i := uint64(0); i < n; i++ {
		x = x*6364136223846793005 + 1442695040888963407
		s[i] = x
	}
	var pre [selsortCapN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	selectionSort(s)
	var post [selsortCapN]uint64
	for i := uint64(0); i < n; i++ {
		post[i] = s[i]
	}
	return pre, post
}
```

**The claim.** For every `n ≤ 8` and every `seed < 2^64`,
`selsort_harness_r(n, seed)` finishes normally, at every nondeterminism
choice, and returns two values: a list `pre` of length `n` and the list
`post = sortSpec pre` — THE sorted permutation of `pre` — both as the
fixed-cap `[8]uint64` arrays the Go returns. **The postcondition is a
relation between the two RETURNED arrays**: the sorted output is itself
observed and equated to the mathematical sort of the observed input. This is
the strongest honest form this harness style has achieved for a sort — the
gallery's other sort, `isort`, checks sortedness and the permutation
property IN GO and returns the verdict `1`; here the data itself crosses the
boundary and the theorem relates it. The first-order companion
`selsort_sorted_count` states the same claim with no `sortSpec` at all:
the second array is `Sorted` and every value occurs in it exactly as often
as in the first (`SortShared.sorted_perm_unique` makes the two forms
interderivable — a sorted list is determined by its counts).

Four honesty clauses, none of them small print:

* **`sortSpec` is one shared definition.** It is the insertion fold from
  the isort entry (`Examples.InsertionSort.Pure`), imported deliberately via
  `SortShared` so that "the sorted permutation" means ONE thing across the
  gallery; `sortSpec_sorted`/`sortSpec_count` are its defining theorems, and
  the first-order corollary avoids the name entirely.
* **The cap `n ≤ 8` is a toy bound, and it is the price of this style.**
  Go's pass-by-value fragment cannot return unbounded data, so the harness
  returns `[selsortCapN]uint64` with `selsortCapN = 8` — visible in the
  Go — and the copy loops and the zero padding exist *only* so the data can
  cross the observation boundary. The theorem carries `n ≤ 8` as a
  hypothesis rather than hiding it.
* **`∃ pre` is still family-determined.** The witness the proof supplies is
  the wrapping LCG `x = x·6364136223846793005 + 1442695040888963407
  (mod 2^64)` iterated from `seed` — genuinely unsorted inputs,
  probe-verified in the guardrails wave — and the statement merely does not
  *say* so. What the S3 form buys is on the postcondition side: the
  sorted-permutation relation is asserted about observed output against
  observed input. Turning the input into genuine ∀-data needs the ghost
  rung-1 annotation, which is designed and not built.
* **Machine idealization**, as elsewhere: entry from an empty heap, an
  unbounded heap, allocation always succeeds. The arithmetic domains are
  separated as usual: `n ≤ 8` is *the program's own* (the array cap,
  declared in its source), `seed < 2^64` is *Go's* uint64 domain at the
  call boundary, the LCG wrap-around is *the program's own arithmetic*
  (uint64 multiply-add, wrapping by Go's rules), and sortedness/counting
  are mathematics.

**The theorem** (`proofs/GoLeanProofs/Examples/SelectionSort.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/SelectionSort.lean -->
```lean
theorem selsort_ok (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ pre post : List Int, pre.length = n ∧ post = sortSpec pre ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel selsortLowered.typeDefs.toList
            selsortLowered.funcs selsortHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            selsortLowered.methods ch
          = .ok { values := #[selArr8 pre, selArr8 post] } := by
```

**The first-order readout** (same file; the statement-TCB corollary — no
`sortSpec`, nothing to unfold):

<!-- verbatim: proofs/GoLeanProofs/Examples/SelectionSort.lean -->
```lean
theorem selsort_sorted_count (n seed : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ pre post : List Int, pre.length = n ∧
      Sorted post ∧ (∀ v : Int, post.count v = pre.count v) ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel selsortLowered.typeDefs.toList
            selsortLowered.funcs selsortHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            selsortLowered.methods ch
          = .ok { values := #[selArr8 pre, selArr8 post] } := by
```

**The returned-array adapter** — the rest of the statement vocabulary
(`proofs/GoLeanProofs/Examples/SelectionSort/Machine.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/SelectionSort/Machine.lean -->
```lean
def selArr8 (xs : List Int) : GoValue :=
  .array ⟨(selPad8 xs).map (fun v => .int v .uint64)⟩
```

**Axioms** (pinned in `proofs/Audit/SelectionSort.lean`):

<!-- verbatim: proofs/Audit/SelectionSort.lean -->
```lean
/-- info: 'GoLean.Examples.SelectionSort.selsort_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/SelectionSort.lean -->
```lean
/-- info: 'GoLean.Examples.SelectionSort.selsort_sorted_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and QUADRATIC, as selection sort is:
`N = (67·n + 145)·n + 174·n + 318`. This is the branch-UNIFORM worst case:
every inner iteration is charged at its `m`-update ceiling (67 steps) and
every pass at a full-suffix scan. **The measured step counts are different
numbers, and the difference is worth stating plainly.** At seed 7 the
machine takes `318` steps at `n = 0` (exactly the bound's constant term),
then `637 / 1011 / 1452 / 1960 / 2535 / 3165 / 3838 / 4566` at `n = 1…8`;
at `n = 8` across seeds `0 / 1 / 123456789 / 2^64−1` it takes
`4506 / 4530 / 4554 / 4542` against the bound's `7158`. The measurement
depends on the data — how often the running minimum updates — and the bound
does not; neither is presented as the other.

**A machine shape worth noticing** (it is what this proof pays for that the
gallery's other sort already paid at a shallower prefix): the subject
allocates a FRESH `m`/`j`/`$forFirst` cell triple on every outer pass — the
pass-local declarations re-enter their blocks, `nextAddr` grows by 3 per
pass, and the dead cells stay in the heap. The proof runs each pass once at
a tight canonical placement and moves it to the true garbage-laden placement
with the executable frame theorem, retiring the triple into the frame
between passes. The garbage is semantically inert; the frame theorem is
precisely the tool that says so.

**Status.** NOT DESIGNATED — see the note in *How to read an entry*: this
example post-dates the 2026-08-14 designation, and designation is arc-end
work under user sign-off, so its statement is not walked by the mechanized
statement-TCB gate and not replayed by the Comparator judge. What it does
have, in-build: the `rfl` lowering pins (`selectionSort_pin`,
`selsortHarnessRFunc_pin`), the golden-lowering guard on both links, and the
axiom pins above. `selsort_readout` is the run-conditioned twin. The
deletion test was run by hand (both binders load-bearing; two broken goals
each). There is no ∀-data companion claim — the subject-level claim over
arbitrary slice contents is not proved, and this entry does not imply it.

**Ground.** Differentially green on 14 corpus rows: the fixed-size drivers
`four-shuffled` / `four-sorted` / `four-same` / `four-reversed` /
`four-duplicates` / `four-extremes` (values at the int64 driver maximum),
`three`, `one`, `empty`, and the relational harness at `harness-r-empty`
(`n = 0`), `harness-r-one`, `harness-r-mid` (`n = 5`), `harness-r-cap`
(`n = 8`) and `harness-r-extreme` (`n = 8`, `seed = 2^63 − 1` — the largest
seed the differential driver can pass; the `--arg` int64 ceiling is a
*driver* limit, not a machine one).

## bubble — early-exit bubble sort, sorted-permutation over returned data

**The Go** (`Corpus/coverage/exec/examples/bubble/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/bubble/main.go -->
```go
func bubbleSort(s []uint64) {
	for end := len(s); end > 1; end-- {
		swapped := false
		for i := 1; i < end; i++ {
			if s[i-1] > s[i] {
				s[i-1], s[i] = s[i], s[i-1]
				swapped = true
			}
		}
		if !swapped {
			return
		}
	}
}
```

<!-- verbatim: Corpus/coverage/exec/examples/bubble/main.go -->
```go
// bubble_harness_r: the S3 RELATIONAL harness. Setup builds a
// genuinely-unsorted family by iterating a wrapping LCG from `seed`;
// a copy loop lifts it into `pre` (the fixed-cap array is the
// pass-by-value fragment's unbounded-data workaround), the subject
// sorts in place, and a second copy loop lifts the result into
// `post`, so a postcondition can relate the returned data directly.
// Real Go, ghost ladder rung 0.
func bubble_harness_r(n, seed uint64) ([bubbleCapN]uint64, [bubbleCapN]uint64) {
	s := make([]uint64, n)
	x := seed
	for i := uint64(0); i < n; i++ {
		x = x*2862933555777941757 + 3037000493
		s[i] = x
	}
	var pre [bubbleCapN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	bubbleSort(s)
	var post [bubbleCapN]uint64
	for i := uint64(0); i < n; i++ {
		post[i] = s[i]
	}
	return pre, post
}
```

**The claim.** For every `n ≤ 8` and every `seed` in the full uint64 domain,
`bubble_harness_r(n, seed)` finishes normally, at every nondeterminism
choice, and returns TWO `[8]uint64` arrays: a length-`n` list `pre` (the
input, zero-padded to the cap), and **`sortSpec pre` — THE sorted
permutation of `pre`** — as the second. The postcondition is stated over
the RETURNED data only. `sortSpec` is the gallery's one definition of "the
sorted permutation" (an insertion fold, shared with the `isort` entry), and
the first-order corollary `bubble_sorted_perm` restates the same claim
without it: the second array is **sorted** (`GoLean.SliceMem.Sorted`) and
has **exactly the first array's element counts** (`List.count`, every
`v : Int`). This is the strongest honest form the S3 harness style has
achieved in the gallery: the other sort entry (`isort`) returns a
Go-computed verdict `1`, while `bubble` returns the data itself and the
theorem relates the two arrays.

**The theorem** (`proofs/GoLeanProofs/Examples/BubbleSort.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/BubbleSort.lean -->
```lean
theorem bubble_ok (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel bubbleLowered.typeDefs.toList
            bubbleLowered.funcs bubbleHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            bubbleLowered.methods ch
          = .ok { values := #[bArr8V pre, bArr8V (sortSpec pre)] } := by
```

with the first-order readout corollary, same file:

<!-- verbatim: proofs/GoLeanProofs/Examples/BubbleSort.lean -->
```lean
theorem bubble_sorted_perm (n seed : Nat) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        ∃ post : List Int,
          runFunctionWithContextM fuel bubbleLowered.typeDefs.toList
              bubbleLowered.funcs bubbleHarnessRFunc
              #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
              bubbleLowered.methods ch
            = .ok { values := #[bArr8V pre, bArr8V post] }
          ∧ Sorted post ∧ (∀ v : Int, post.count v = pre.count v) := by
```

**Axioms** (pinned in `proofs/Audit/BubbleSort.lean`, the example's shard
of `proofs/Audit.lean`):

<!-- verbatim: proofs/Audit/BubbleSort.lean -->
```lean
/-- info: 'GoLean.Examples.BubbleSort.bubble_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Honesty clauses.**

* **`∃ pre` is family-determined.** The witness is the wrapping LCG family
  `x ← x·2862933555777941757 + 3037000493 (mod 2^64)` seeded at `seed` —
  the statement merely avoids saying so. The corpus rows exercise passes
  with swaps, the swap-free early exit, and the counter exit, so both ways
  out of the subject are on the proven path AND the differential path.
  Making the input genuine ∀-data needs the ghost rung-1 annotation
  (designed, not built).
* **The cap `n ≤ 8` is a TOY bound.** It exists only so the data can cross
  Go's pass-by-value observation boundary as `[bubbleCapN]uint64`
  (`bubbleCapN = 8`, visible in the source); it is not a property of
  bubble sort.
* **Domain bounds attributed**: `seed < 2^64` is Go's own uint64 argument
  domain; the elements' bounds are the program's own arithmetic (LCG
  iterates mod `2^64`); `n ≤ 8` is the harness cap; sortedness and
  count-preservation are mathematics over `List Int`. Machine
  idealization as in every entry: empty-heap entry, unbounded heap,
  allocation always succeeds.
* **`n = 0` and `n = 1` are included** — `end ≤ 1` fails the outer test at
  once and the empty/singleton array is sorted; corpus rows pin both.

**Fuel bound.** Explicit and QUADRATIC (this is bubble sort):
`N = (105·n + 116)·n + 174·n + 318` — a branch-uniform worst case: `105`
per inner comparison charged at the swap arm, at most `n−1` passes, `68`
per setup iteration, `53` per copy iteration (twice), plus fixed
entry/prologue/epilogue segments. Measured runs (seed 7), recorded
separately and NOT the bound: `318` at `n = 0`, `492` at `n = 1`,
`809/1040/1549` at `n = 2/3/4`, `4443` at `n = 8` — data-dependent (how
many swaps fire, where the early exit lands), which is why only the bound
is a law.

**Status.** NOT DESIGNATED — see the note in *How to read an entry*: this
example post-dates the 2026-08-14 designation, and designation is arc-end
work under user sign-off, so its statement is not walked by the mechanized
statement-TCB gate and not replayed by the Comparator judge. What it does
have, in-build: the `rfl` lowering pins (`bubble_pin`,
`bubbleHarnessRFunc_pin`, both axiom-pinned in `proofs/Audit/BubbleSort.lean`),
the golden-lowering guard (`scripts/check-golden` against
`baselines/golden/bubble-lowered.repr`), and the axiom pins above. The
deletion test was RUN by hand — both explicit hypotheses load-bearing
(`hcap` breaks the run lemma's cap-dependent goals, `hseed` the entry
normalization). `bubble_readout` is the run-conditioned twin. The early return
(`if !swapped { return }`, the corpus's unary-`!` probe) means the subject
leaves from two places; the proof runs both exits to the same terminal —
the swap-free exit is discharged by "a swap-free pass certifies a sorted
prefix", the counter exit by the pass invariant alone. The per-pass
re-allocation of `swapped`/`i`/`$forFirst` is carried by the executable
frame theorem (each pass proven once at a tight placement, retired cells
rebased into the frame), the isort precedent at threshold 16.

**Ground.** Differentially green on 14 corpus rows: subject rows through
`sortFour`/`sortThree`/`sortOne`/`sortEmpty` covering shuffled,
already-sorted (early exit on the first pass), all-equal, reverse-sorted
(full pass count), duplicate, and near-`2^63` inputs, plus the harness at
`n = 0/1/5/8` and a near-`2^63` seed.

## rle — run-length encoding via `append`

**The Go** (`Corpus/coverage/exec/examples/rle/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/rle/main.go -->
```go
// rle: run-length encode s into two parallel slices (runValues,
// runCounts), built with append — walk s, extending the current run
// while the value repeats, starting a new run otherwise. INTERNAL
// subject: it returns slices, so it is never a corpus subject directly;
// the scalar drivers and the fixed-cap harness below observe it.
func rle(s []uint64) ([]uint64, []uint64) {
	runVals := []uint64{}
	runCounts := []uint64{}
	for i := 0; i < len(s); i++ {
		k := len(runVals)
		extended := false
		if k > 0 {
			if runVals[k-1] == s[i] {
				runCounts[k-1]++
				extended = true
			}
		}
		if !extended {
			runVals = append(runVals, s[i])
			runCounts = append(runCounts, 1)
		}
	}
	return runVals, runCounts
}
```

<!-- verbatim: Corpus/coverage/exec/examples/rle/main.go -->
```go
// rle_harness_r: the S3 RELATIONAL harness (gallery campaign G1,
// 2026-08-15). Setup builds the family s[i] = seed + i/3, so runs of
// length up to 3 appear; the harness returns the PRE-STATE alongside
// the encoded (runVals, runCounts) — all as fixed-cap arrays, the
// pass-by-value fragment's unbounded-data workaround — plus the run
// count k, so the Lean postcondition relates the returned data
// DIRECTLY, with no family function re-describing the setup. Real Go,
// ghost ladder rung 0.
func rle_harness_r(n, seed uint64) ([rleCapN]uint64, [rleCapN]uint64, [rleCapN]uint64, uint64) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i/3
	}
	var pre [rleCapN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	vals, counts := rle(s)
	var runVals [rleCapN]uint64
	var runCounts [rleCapN]uint64
	for i := 0; i < len(vals); i++ {
		runVals[i] = vals[i]
		runCounts[i] = counts[i]
	}
	return pre, runVals, runCounts, uint64(len(vals))
}
```

**The claim.** For every `n ≤ 3` and every `seed < 2^64`,
`rle_harness_r(n, seed)` finishes normally, at every nondeterminism
choice, and returns four values related as follows: `pre` is the
length-`n` encoded input (zero-padded to the cap), `runVals` and
`runCounts` hold exactly the value and count projections of
`rleSpec pre` — the mathematician's run-length encoding, grouped maximal
runs — zero-padded past the live prefix, and `k = (rleSpec pre).length`.
The first-order corollary `rle_decode` states the DECODE relation with
no `rleSpec` in the statement: the returned `vals`/`counts` lists have
equal length `k`, the returned count is `vals.length`, and expanding
each `(vals[j], counts[j])` pair back into a run reproduces the
returned `pre` exactly.

**What `∀ choices` means HERE, specifically.** `rle` builds its output
slices with `append`. The machine's append-spill draws the fresh
backing array's CAPACITY from the nondeterminism-choice stream — the
envelope `[newLen, max 32 (2·growth)]`, arguing spec §Appending's "a
new, sufficiently large underlying array" (any capacity ≥ the length is
conforming). The theorem quantifies over EVERY stream, so it covers
every capacity in that envelope: both spill capacities are carried
symbolically through the proof (`capV, capC ∈ [1, 32]`, existential,
never pinned), and the theorem shows nothing the harness returns
depends on the draw. This is a genuine nondeterminism-envelope claim,
not a replay of one allocator behavior.

**Scope honesty — the claim's `n ≤ 3` is NOT the harness's own cap.**
The harness's visible bound is `n ≤ 8` (`rleCapN`); the theorem proves
the SINGLE-RUN regime `n ≤ 3`, where the family `seed + i/3` is
constant, exactly one new-run event fires, and both its `append`s spill
from cap 0. For `n ∈ [4, 8]` a second new-run event fires at `i = 3`,
and whether ITS appends spill (allocate) or extend in place depends on
the FIRST spill's choice-drawn capacity — so the machine's allocation
layout downstream is choice-dependent, which the current
literal-address raw-segment proof technology cannot follow. That regime
is a RECORDED HONEST GAP (kit-gap ledger, lane B): the theorem simply
does not speak about `n > 3`, and this entry claims nothing there.
Consequently the encoding exercised by the proof always has exactly one
run (`k = 1`, or `0` at `n = 0`): the extend path, both spills, the
zero-padding, and the count reporting are all covered; a mid-stream
run BOUNDARY (a `false` extend test) is not.

**Domain bounds, attributed.** `n ≤ 3` — the proof's own regime bound
(above; not mathematics, not Go). `seed < 2^64` — Go's `uint64` domain.
The family wraps mod `2^64` by the program's own arithmetic and the
theorem covers wrapping seeds. The fixed cap `8` is a TOY bound existing
only so the data can cross Go's pass-by-value observation boundary as
`[8]uint64`s. Machine idealization as everywhere: entry from an empty
heap, unbounded heap, allocation always succeeds.

**Input honesty:** the quantifiers are the scalars `(n, seed)` — an
input *family*, not all slices. `∃ pre` in the theorem is
family-determined (the witness is `s[i] = seed + i/3`, constant on this
domain); the statement merely avoids saying so. Genuine ∀-data needs
ghost rung 1.

**The spec** (`proofs/GoLeanProofs/Examples/RunLength/Pure.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/RunLength/Pure.lean -->
```lean
def rleSpec : List Int → List (Int × Nat)
  | [] => []
  | x :: xs =>
    match rleSpec xs with
    | [] => [(x, 1)]
    | (y, c) :: rest =>
      if x = y then (x, c + 1) :: rest else (x, 1) :: (y, c) :: rest
```

with the general decode theorem (proved for ALL lists, not just this
domain):

<!-- verbatim: proofs/GoLeanProofs/Examples/RunLength/Pure.lean -->
```lean
theorem rleSpec_decode (l : List Int) :
    (rleSpec l).flatMap (fun p => List.replicate p.2 p.1) = l := by
```

**The theorem** (`proofs/GoLeanProofs/Examples/RunLength.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/RunLength.lean -->
```lean
theorem rle_ok (n seed : Nat) (hcap : n ≤ 3) (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel rleLowered.typeDefs.toList
            rleLowered.funcs rleHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            rleLowered.methods ch
          = .ok { values :=
              #[rleArr8 pre,
                rleArr8 ((rleSpec pre).map Prod.fst),
                rleArr8 ((rleSpec pre).map (fun p => ((p.2 : Nat) : Int))),
                .int (((rleSpec pre).length : Nat) : Int) .uint64] } := by
```

and the first-order decode corollary:

<!-- verbatim: proofs/GoLeanProofs/Examples/RunLength.lean -->
```lean
theorem rle_decode (n seed : Nat) (hcap : n ≤ 3) (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        ∃ (vals counts : List Int),
          runFunctionWithContextM fuel rleLowered.typeDefs.toList
              rleLowered.funcs rleHarnessRFunc
              #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
              rleLowered.methods ch
            = .ok { values :=
                #[rleArr8 pre, rleArr8 vals, rleArr8 counts,
                  .int ((vals.length : Nat) : Int) .uint64] }
          ∧ vals.length = counts.length
          ∧ (List.zip vals counts).flatMap
              (fun p => List.replicate p.2.toNat p.1) = pre := by
```

**Axioms** (pinned in `proofs/Audit/RunLength.lean`):

<!-- verbatim: proofs/Audit/RunLength.lean -->
```lean
/-- info: 'GoLean.Examples.RunLength.rle_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project
axioms.

**Fuel bound.** Explicit and affine: `N = 253·n + 527` — a BOUND, not a
measured law. The measured counts (probe, then re-derived exactly as
segment sums, and choice-independent — spilling and in-place appends
cost the same steps): `419` at `n = 0`, `780` at `n = 1`, `1033` at
`n = 2`, `1286` at `n = 3`. The bound over-charges by up to 108 steps
(`n = 0`); the true counts are affine on `n ∈ [1, 3]` (`253·n + 527`
exactly) with `n = 0` below the line.

**Status.** NOT DESIGNATED — see the note in *How to read an entry*: this
example post-dates the 2026-08-14 designation, and designation is arc-end
work under user sign-off, so its statement is not walked by the mechanized
statement-TCB gate and not replayed by the Comparator judge. It is absent
from `Examples/Targets.lean`, the `scripts/ci` Targets allowlist,
`Audit.lean`'s designated-name list and the Comparator Challenge's
trusted closure. `rle_readout` is the run-conditioned twin; `rle_decode`
the first-order corollary. The deletion test was RUN (both hypotheses
load-bearing: dropping `hcap` breaks the case split, dropping `hseed`
the entry normalization).

**Ground.** Differentially green on 14 corpus rows: five four-element
`rleFourCount` drivers (mixed, distinct, all-same, alternating, and an
`int64`-extreme pair), two `rleFourFirst` drivers, one-element and
empty drivers, and the relational harness at `(0,5)`, `(1,7)`, `(5,40)`,
`(8,10)` and `(8, int64-max)`. Note the harness rows at `n = 5` and
`n = 8` sit in the `n ∈ [4, 8]` regime the theorem does NOT cover — the
differential guards the gap regime's oracle behavior (multiple runs,
mid-stream boundaries) even though it is outside the machine proof; the
`rleFour*` driver rows exercise multi-run encodings end-to-end as well.

## fibmemo — recursive Fibonacci over a live memo table

**The Go** (`Corpus/coverage/exec/examples/fibmemo/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/fibmemo/main.go -->
```go
func fibMemo(n uint64, memo map[uint64]uint64) uint64 {
	if n < 2 {
		return n
	}
	if v, ok := memo[n]; ok {
		return v
	}
	r := fibMemo(n-1, memo) + fibMemo(n-2, memo)
	memo[n] = r
	return r
}
```

<!-- verbatim: Corpus/coverage/exec/examples/fibmemo/main.go -->
```go
// fib: wrapper subject — allocates the memo table and runs the
// memoized recursion.
func fib(n uint64) uint64 {
	memo := make(map[uint64]uint64)
	return fibMemo(n, memo)
}
```

<!-- verbatim: Corpus/coverage/exec/examples/fibmemo/main.go -->
```go
// fibmemo_harness: the harness ruling's three-phase shape, S2 scalar.
// setup: nothing — fib takes no memory input (the memo is internal).
// test: identity — the returned scalar IS the observable.
func fibmemo_harness(n uint64) uint64 {
	return fib(n)
}
```

**The specification** is `fibSpec` — the same definition the designated
`fib` entry states its headlines over, imported rather than redefined, so
the gallery's "Fibonacci" means exactly one thing:

<!-- verbatim: proofs/GoLeanProofs/Examples/Targets.lean -->
```lean
def fibSpec : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSpec n + fibSpec (n + 1)
```

**The theorem** (`proofs/GoLeanProofs/Examples/FibMemo.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/FibMemo.lean -->
```lean
theorem fibmemo_ok (n : Nat) (hn : n < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel fibmemoLowered.typeDefs.toList
          fibmemoLowered.funcs fibmemoHarnessFunc
          #[.int (n : Int) .uint64] fibmemoLowered.methods ch
        = .ok { values := #[.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/FibMemo.lean`):

<!-- verbatim: proofs/Audit/FibMemo.lean -->
```lean
/-- info: 'GoLean.Examples.FibMemo.fibmemo_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/FibMemo.lean -->
```lean
/-- info: 'GoLean.Examples.FibMemo.fibmemo_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Why this entry exists: it is the gallery's first RECURSION.** Every other
entry's machine run stays inside one call frame and loops. `fibMemo` calls
itself twice, so the machine pushes a genuine continuation stack, the heap
interleaves live frames with the dead cells of completed sub-calls, and no
finite description of "the" run shape exists — the shape grows with `n`. The
proof's induction (`fmCall_build` in `Examples/FibMemo/Rec.lean`) is
**continuation-stack-parametric**: each call-span lemma quantifies over the
return continuation, so the recursive instantiation hands it the exact frame
continuation the machine pushed one level up. The heap is carried as a
small-footprint invariant — the memo's data cell, the caller's result cell,
and whole-heap freshness above the allocation cursor — rather than as any
concrete layout.

**The memo is load-bearing, and the bound proves it.** The fuel bound
`N = 170·n + 107` is LINEAR in `n`; an unmemoized double recursion would be
exponential. The induction tracks the memo as exactly the table `{2..k}`
(insertion-ordered, which is what the machine's append-on-insert produces),
and after the first recursive call returns, the second always hits the
table. The comma-ok read `v, ok := memo[n]` is the honest cache test the
corpus comments call out: `fib(0) = 0` is indistinguishable from "absent"
under a zero-value read, so `ok` does real work.

**Domain bounds, attributed.** `n < 2^64` is **Go's domain**, all of it. The
`% 2^64` in the postcondition is **the program's own arithmetic** — uint64
addition wraps, and the claim states the wrapped value on the full domain
(the same stance as the designated `fib_total`); for `n ≤ 93` the mod is the
identity and the returned value IS `fibSpec n`. The Fibonacci function is
**mathematics**. Machine idealization as elsewhere — in particular the
recursion allocates a fresh frame per call and nothing bounds the depth but
`n` itself.

**Fuel bound.** `N = 170·n + 107` is a BOUND. **The measurement is a
different number**: `107` for `n ≤ 1`, `249` at `n = 2`, and `170·n − 119`
for `n ≥ 3` — probe-verified at `n = 3, 4, 5, 10` (391, 561, 731, 1581).
Neither is presented as the other.

**∀ choices is vacuous here, and stated anyway** — the memo map is only
indexed, never ranged over, so this harness consumes no choices. (The
corpus's separate `fibMemoSize` subject does range the memo; it is pinned by
differential rows, not by this theorem.)

**Status.** NOT DESIGNATED — see the note in *How to read an entry*. Added by
the gallery campaign's hard lane (2026-08-15). In-build: the `rfl` lowering
pins (`fibMemoFunc_pin` on the recursive subject, `fibmemoHarnessFunc_pin`
on the harness), the golden-lowering guard on both links, and the axiom pins
above. Its deletion test was RUN by hand — `lean_minimal_hypotheses` on
`fibmemo_ok`, **both explicit binders load-bearing**. `fibmemo_readout` is
the run-conditioned twin.

**Ground.** Differentially green on 10 corpus rows: `zero`, `one`, `two`,
`ten`, `thirty` (the `fib` wrapper), `memosize-zero`, `memosize-one`,
`memosize-ten` (the map-ranging sibling subject), and the harness rows
`harness-one` and `harness-thirty`. All ten are inside the theorem's domain.

## sieve — the sieve of Eratosthenes, bounded

**The Go** (`Corpus/coverage/exec/examples/sieve/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/sieve/main.go -->
```go
func countPrimes(n uint64) uint64 {
	if n < 2 {
		return 0
	}
	composite := make([]bool, n+1)
	for i := uint64(2); i*i <= n; i++ {
		if !composite[i] {
			for j := i * i; j <= n; j += i {
				composite[j] = true
			}
		}
	}
	count := uint64(0)
	for i := uint64(2); i <= n; i++ {
		if !composite[i] {
			count++
		}
	}
	return count
}
```

<!-- verbatim: Corpus/coverage/exec/examples/sieve/main.go -->
```go
// sieve_harness: S2 scalar three-phase shape; setup and test are
// identities (argument-input subject, returned scalar is the
// observable).
func sieve_harness(n uint64) uint64 {
	return countPrimes(n)
}
```

**The specification** (`proofs/GoLeanProofs/Examples/Sieve/Pure.lean`) is
trial-division primality — the obvious definition a reader checks by eye,
not a restatement of the sieve:

<!-- verbatim: proofs/GoLeanProofs/Examples/Sieve/Pure.lean -->
```lean
/-- Trial-division primality: `2 ≤ k` and no divisor `d` with `2 ≤ d < k`. -/
def isPrime (k : Nat) : Bool :=
  decide (2 ≤ k) && (List.range k).all (fun d => decide (d < 2) || decide (k % d ≠ 0))
```

<!-- verbatim: proofs/GoLeanProofs/Examples/Sieve/Pure.lean -->
```lean
/-- The number of primes ≤ `n` — the obvious spec the headline states. -/
def primeCount (n : Nat) : Nat := ((List.range (n + 1)).filter isPrime).length
```

**The theorem** (`proofs/GoLeanProofs/Examples/Sieve.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Sieve.lean -->
```lean
theorem sieve_ok (n : Nat) (hn : n < 2 ^ 62) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel sieveLowered.typeDefs.toList
          sieveLowered.funcs sieveHarnessFunc
          #[.int (n : Int) .uint64] sieveLowered.methods ch
        = .ok { values := #[.int ((primeCount n : Nat) : Int) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/Sieve.lean`):

<!-- verbatim: proofs/Audit/Sieve.lean -->
```lean
/-- info: 'GoLean.Examples.Sieve.sieve_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/Sieve.lean -->
```lean
/-- info: 'GoLean.Examples.Sieve.sieve_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**The theorem says the sieve computes THE PRIMES.** The specification never
mentions marking, multiples, or loops — it enumerates divisors. So the
theorem carries the sieve's own number theory: that marking the multiples
`i·i, i·i+i, …` of each still-unmarked `i` with `i·i ≤ n` marks *exactly*
the composites `≤ n`. The two directions are genuinely different facts: a
marked cell is a multiple `j ≥ i·i` of some `i ≥ 2`, hence composite; and a
composite `k ≤ n` has a least prime factor `p` with `p·p ≤ k` — so the
outer loop reaches `p` (its guard `p·p ≤ n` holds), finds it unmarked
(its own factors are smaller than `p`, and `p` is prime), and marks `k`.
That least-prime-factor argument is `sieveTable_spec`'s core, proved from
scratch (this project carries no Mathlib).

**Why this entry was hard, mechanically.** `make([]bool, n+1)` allocates a
backing array of SYMBOLIC length — no fixed cap, unlike every array entry
before it — and each marking pass allocates fresh loop-scratch cells, so
the heap's shape depends on the run's own data (which `i` were prime). The
machine half rides the footprint style the `fibmemo` unit introduced: a
concrete 10-cell front, an abstract dead region with a freshness invariant,
and per-pass live cells at symbolic addresses.

**Domain bounds, attributed.** `n < 2^62` is **the program's own
arithmetic**: the outer guard computes `i*i`, and although `i` stays small
(`i ≤ √n + 1`), for `n` near `2^64` that multiply can WRAP and the guard —
and with it the program — computes something else. Below `2^62` every
machine integer in the run is comfortably under the threshold, and the
theorem deliberately claims nothing outside it. The primality itself is
**mathematics**. Machine idealization as elsewhere — the `n+1`-cell table
lives in one backing cell of an unbounded heap.

**Fuel bound.** `N = (n+1)·(49·(n+1) + 261) + 300` — a deliberately
generous QUADRATIC over-charge (every potential pass is billed a full
inner sweep; the true cost is the sieve's `n·(Σ 1/p)`-ish sum). **The
measurement is a much smaller number**: 55 / 279 / 340 / 1174 / 3296 at
`n = 0, 2, 3, 10, 30`, against bound values 610 / 1524 / 2128 / 9100 /
55480. A valid bound was preferred to a delicate one; neither is presented
as the other.

**∀ choices is vacuous here, and stated anyway.**

**Status.** NOT DESIGNATED — see the note in *How to read an entry*. Added
by the gallery campaign's hard lane (2026-08-15); the machine half was
proved by a delegated worker against a fixed statement and re-verified by
the lane owner (fresh axiom probes, deletion test re-run). In-build: the
`rfl` lowering pins (`countPrimes_pin` on the subject,
`sieveHarnessFunc_pin` on the harness), the golden-lowering guard on both
links, and the axiom pins above. Its deletion test was RUN —
`lean_minimal_hypotheses` on `sieve_ok`, **both explicit binders
load-bearing**. `sieve_readout` is the run-conditioned twin.

**Ground.** Differentially green on 11 corpus rows: `n0`, `n1`, `n2`,
`n10`, `n30`, `n60` (the subject), `prime`, `composite`, `beyond` (the
`isPrimeSieved` sibling subject), and the harness rows `harness-mid` and
`harness-zero`. All eleven are inside the theorem's domain — the corpus
deliberately has no extreme-`n` row, because `n` is an ALLOCATION size and
the boundedness rule outranks the generic edge-case rule (the wave's
recorded call).

## stein — binary GCD (Stein's algorithm), the extension-E3 consumer

**The Go** (`Corpus/coverage/exec/examples/stein/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/stein/main.go -->
```go
func isEven(x uint64) bool {
	return x%2 == 0
}
```

<!-- verbatim: Corpus/coverage/exec/examples/stein/main.go -->
```go
func steinGCD(a, b uint64) uint64 {
	if a == 0 {
		return b
	}
	if b == 0 {
		return a
	}
	shift := uint64(0)
	for isEven(a) && isEven(b) {
		a /= 2
		b /= 2
		shift++
	}
	for isEven(a) {
		a /= 2
	}
	for {
		for isEven(b) {
			b /= 2
		}
		if a > b {
			a, b = b, a
		}
		b = b - a
		if b == 0 {
			break
		}
	}
	return a << shift
}
```

<!-- verbatim: Corpus/coverage/exec/examples/stein/main.go -->
```go
// stein_harness: three-phase shape; setup and test are identities
// (argument-input subject, returned data is the observable).
func stein_harness(a, b uint64) uint64 {
	r := steinGCD(a, b)
	return r
}
```

**Why this example exists.** Idiomatic Go writes `isEven(a) && isEven(b)` —
a CALL in a short-circuit operand — and the frontend quarantined exactly
that, fail-closed, so this example was landed BLOCKED (nine red rows, the
recorded guardrail) and then PULLED extension E3: the frontend's
normalization of effectful short-circuit operands to the spec's own
conditional rewrite, its evaluation-order fidelity argued against the spec
text and pinned by corpus rows before the implementation landed
(`docs/gallery-campaign-log/g2.md`, "E3 — THE FIDELITY ARGUMENT"). The
subject was NOT rewritten to dodge the gap; the gap was closed under
guardrails, and this entry is E3's COMPLETE consumer.

**The claim.** For every `a` and `b` in the full `uint64 × uint64` domain —
no bound and no wrapping clause, because a gcd never exceeds its arguments,
the subtract loop runs only after the ordering swap, and the final
`a << shift` reassembles exactly the factors the first loop took apart —
`stein_harness(a, b)` finishes normally, at every nondeterminism choice,
and returns exactly `Nat.gcd a b`: Lean's textbook gcd, including
`gcd(0, 0) = 0`.

**The mathematics.** The three loop phases are mirrored by pure functions
(`commonTwos`, `stripTwos`, `steinSub` in
`proofs/GoLeanProofs/Examples/Stein/Pure.lean`) whose composition
`steinSpec` is proven equal to `Nat.gcd` from core Lean, no Mathlib — the
binary-GCD identities `gcd(2a,2b) = 2·gcd(a,b)`, `gcd(a,2b) = gcd(a,b)`
for odd `a`, and `gcd(a,b−a) = gcd(a,b)` for `a ≤ b`, each by
divisibility antisymmetry:

<!-- verbatim: proofs/GoLeanProofs/Examples/Stein/Pure.lean -->
```lean
theorem steinSpec_eq_gcd (a b : Nat) : steinSpec a b = Nat.gcd a b := by
```

The machine walk (`Examples/Stein/Run.lean`) is math-free: its phase
inductions run one-to-one against those functions' branch equations, and
the two halves meet in exactly that theorem.

**The theorem** (`proofs/GoLeanProofs/Examples/Stein.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Stein.lean -->
```lean
theorem stein_ok (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel steinLowered.typeDefs.toList
          steinLowered.funcs steinHarnessFunc
          #[.int (a : Int) .uint64, .int (b : Int) .uint64]
          steinLowered.methods ch
        = .ok { values := #[.int ((Nat.gcd a b : Nat) : Int) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/Stein.lean`, the example's shard of
`proofs/Audit.lean`):

<!-- verbatim: proofs/Audit/Stein.lean -->
```lean
/-- info: 'GoLean.Examples.Stein.stein_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms
(`steinSpec_eq_gcd` itself uses only `[propext, Quot.sound]`).

**Domain bounds, attributed — and this entry has none to exclude.** The
theorem's `a < 2^64` and `b < 2^64` are *Go's own* `uint64` argument domain
at the call boundary and nothing else: there is no toy cap (the harness
returns a single `uint64`, so no fixed-cap array has to cross the observation
boundary) and no wrap-region exclusion (a gcd never exceeds its arguments).
The gcd itself — `Nat.gcd` and the binary-GCD identities — is
**mathematics**. Machine idealization as elsewhere: entry from an empty heap,
an unbounded heap, allocation always succeeds.

**Fuel bound.** Explicit and affine in the loops' shared
strictly-decreasing measure: `N = 600 + 480·(a + b)` — a BOUND, not a
measurement (recorded so in the module; the measured `(12, 18)` run takes
896 steps against a bound of 15,000, and the early exits measure 57 and
66).

**Status.** NOT DESIGNATED — see the note in *How to read an entry*: this
example post-dates the 2026-08-14 designation, so its statement is not walked
by the mechanized statement-TCB gate and not replayed by the Comparator
judge. What it does have, in-build: the `rfl` lowering pins (`isEvenFunc_pin`
and `steinGCDFunc_pin` on the subject, `steinHarnessFunc_pin` and
`steinHarnessFuncRun_pin` on the harness), the golden-lowering guard
(`scripts/check-golden` against `baselines/golden/stein-lowered.repr`), and
the axiom pins above. Its deletion test was RUN by hand —
`lean_minimal_hypotheses` on `stein_ok`, **all three explicit binders
load-bearing**. `stein_readout` is the run-conditioned twin, derived through
the shared bridge.

**Ground.** Differentially green on 9 corpus rows: `zero-zero`, `a-zero`,
`zero-b`, `coprime`, `common`, `pow2` (a pure power-of-two pair), `big`
(`(2^63−1, 3074457345618258602)`), and the harness rows `harness-common`
and `harness-big` — all nine RED at `frontend-export` until E3 landed,
which was the point. The evaluation-order behaviour of the normalization
this lowering rides on is separately pinned by the 16-row
`bools/short-circuit-effects/*` guardrail family (counter, order-witness,
nested, loop-guard, and expression-position shapes).

---

## wordfreq — word frequency over a string via `strings.Fields`, the extension-E5 consumer

**The Go** (`Corpus/coverage/exec/examples/wordfreq/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/wordfreq/main.go -->
```go
// wordFreq: the subject — split the text into words with
// strings.Fields (the idiomatic Go spelling this example exists to
// exercise: extension E5, the stdlib-shim boundary), count each word
// in a map, and report the queried word's count plus the maximum
// count over all words. The max loop RANGES over the map, so its
// iteration order is nondeterministic; the summary is order-invariant
// by construction. `counts[query]` on an absent key is Go's
// zero-value read.
func wordFreq(text string, query string) (uint64, uint64) {
	words := strings.Fields(text)
	counts := make(map[string]uint64)
	for i := 0; i < len(words); i++ {
		counts[words[i]]++
	}
	best := uint64(0)
	for _, c := range counts {
		if c > best {
			best = c
		}
	}
	return counts[query], best
}
```

<!-- verbatim: Corpus/coverage/exec/examples/wordfreq/main.go -->
```go
// buildText: the differential driver passes only integer arguments,
// so the harness builds its text from (n, seed): n single-letter
// words from the family {"a","b","c"} (word i = 'a' + (seed+i)%3,
// Go's own uint64 wrap in seed+i kept honestly), with the separator
// VARIED by position — one space, two spaces, or a tab — and a
// leading space, so Fields' leading/trailing/consecutive/mixed
// whitespace classes are exercised on every built input.
func buildText(n, seed uint64) string {
	out := " "
	for i := uint64(0); i < n; i++ {
		out += string(rune(97 + (seed+i)%3))
		if i%3 == 0 {
			out += " "
		} else if i%3 == 1 {
			out += "  "
		} else {
			out += "\t"
		}
	}
	return out
}
```

<!-- verbatim: Corpus/coverage/exec/examples/wordfreq/main.go -->
```go
// wordfreq_harness_r: the S3 RELATIONAL harness — setup builds the
// text and the queried word from (n, seed, qsel); the returned
// quadruple (pre, q, hits, best) is the observable, all pure values
// (strings cross the observation boundary by contents). The
// postcondition relates the RETURNED data: hits = the multiplicity
// of q among pre's words, best = the maximum multiplicity.
func wordfreq_harness_r(n, seed, qsel uint64) (string, string, uint64, uint64) {
	pre := buildText(n, seed)
	q := string(rune(97 + qsel%3))
	hits, best := wordFreq(pre, q)
	return pre, q, hits, best
}
```

**Why this example exists.** Idiomatic Go writes
`words := strings.Fields(text)` — a STANDARD-LIBRARY call — and the
machine has no standard library: the frontend quarantined exactly that
call, fail-closed, so this example landed BLOCKED (14 red rows, the
recorded guardrail) and PULLED extension E5: frontend-level shims for
an allowlisted set of pure stdlib functions
(`docs/gallery-campaign-log/g2.md`, "E5 — THE FIDELITY ARGUMENT"). The
subject was NOT rewritten around the gap (a hand-rolled splitter would
be a green example of a program nobody writes); the gap was closed
under guardrails, and this entry is E5's COMPLETE consumer.

**What the machine actually runs — and why that is the claim's
honesty clause, not a footnote.** `go run` executes the REAL
`strings.Fields`; the machine executes the frontend's SHIM — a
byte-level scan over the full Unicode White_Space class, injected into
the program and lowered through the ordinary pipeline (its lowered
body is part of this example's golden pin). The theorem below is a
theorem about the SHIM's semantics. Three things tie the shim to the
stdlib: (1) every differential row through the call is a direct oracle
test of shim fidelity — including the dedicated
`strings/fields-conformance/*` suite with the non-ASCII White_Space
members, a White_Space=No negative pin, and invalid UTF-8, all green;
(2) a 600,000-trial randomized shim-vs-stdlib equivalence fuzz (0
mismatches), run under the real Go runtime; (3) the Lean spec
`wordsOf` is `#guard`-pinned inside the proof against the same
go-run-confirmed splits the corpus pins. What is NOT claimed: a proof
that shim = stdlib for all inputs — that correspondence is
differentially validated evidence, exactly like the machine's own
semantics.

**The claim.** For every `n < 2^60`, `seed < 2^64`, `qsel < 2^64`,
running `wordfreq_harness_r(n, seed, qsel)` completes normally past
one fuel bound, at every nondeterminism-choice stream, and returns
FOUR values: the built text `pre` (with exactly `n` words), the
queried word `q`, the multiplicity of `q` among `pre`'s words, and the
maximum multiplicity over `pre`'s words — where "words" means
`wordsOf pre`, the byte-level Fields spec, stated over the RETURNED
data.

**The theorem** (`proofs/GoLeanProofs/Examples/WordFreq.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/WordFreq.lean -->
```lean
theorem wordfreq_ok (n seed qsel : Nat) (hn : n < 2 ^ 60)
    (hseed : seed < 2 ^ 64) (hqsel : qsel < 2 ^ 64) :
    ∃ pre q : List UInt8, (wordsOf pre).length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel wordfreqLowered.typeDefs.toList
            wordfreqLowered.funcs wordfreqHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (qsel : Int) .uint64]
            wordfreqLowered.methods ch
          = .ok { values := #[.string (gs pre), .string (gs q),
                              .int (multiplicity q (wordsOf pre) : Nat) .uint64,
                              .int (maxMultiplicity (wordsOf pre) : Nat) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/WordFreq.lean`):

<!-- verbatim: proofs/Audit/WordFreq.lean -->
```lean
/-- info: 'GoLean.Examples.WordFreq.wordfreq_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project
axioms (`wordsOf_textFamily` — the family bridge — uses only
`[propext, Quot.sound]`).

**Honesty clauses.**

* **`∀ ch` is load-bearing, and in BOTH of the gallery's two ways** —
  this is the only entry where that happens. *Map-iteration order*: the
  `for range counts` max loop consumes one choice per iteration, so the
  claim holds at EVERY order — provable precisely because
  `maxMultiplicity` is a function of the returned data and cannot see
  the order. *`append` capacity*: the injected `strings.Fields` shim
  builds its result with `out = append(out, …)`, so every spilling
  append of the fields slice draws a capacity from the choice stream
  (the same envelope `stack`, `queue` and `rle` quantify over below),
  and the claim holds at every draw — nothing the harness returns
  depends on which capacity the allocator picked.
* **`wordsOf` is a scan-shaped specification** — it walks the bytes
  left to right consuming separator widths, much as the split itself
  does, so by itself it would be a program-shaped spec (`twosum`'s
  clause above makes the same admission about `twoSumSpec`). Two
  things carry it: its separator class is written out independently as
  the full Unicode White_Space set in UTF-8 byte patterns (`sepWidth`,
  `Examples/WordFreq/Pure.lean`) rather than as "whatever the shim
  does", and the `#guard`s at the bottom of that module pin it
  byte-exactly against the go-run-confirmed splits of all 8
  `strings/fields-conformance` rows. The first-order readout
  `wordfreq_hits_eq` then states the queried count with no `wordsOf`
  in the statement at all — plain residue arithmetic over
  `(n, seed, qsel)`.
* **The queried count is the map read, zero value included** —
  `counts[query]` on an absent word yields `0`, `multiplicity` is `0`
  in exactly that case; rows `lit-miss` and `harness-one-miss` pin it
  on the oracle.
* **No fixed-cap toy bound**: strings cross the observation boundary
  by contents; the returned text is unbounded. The bounds that DO
  appear are attributed: `seed, qsel < 2^64` are Go's `uint64`
  argument domain; `n < 2^60` keeps the built text (at most `3n+1`
  bytes) inside Go's `int` domain for the subjects' `int` loop
  indices — mathematics needs none of them.
* **`∃ pre, q` is still family-determined**: the witnesses are
  `textFamily n seed` and `qWord qsel` — the program's own
  arithmetic, uint64 wrap included. The statement merely avoids
  SAYING so; the first-order corollary below says it exactly.
* **Machine idealization** as everywhere: empty-heap entry, unbounded
  heap and strings, allocation always succeeds.

**Fuel bound.** Explicit and affine: `N = wfFuel n = 811·n + 582` — a BOUND, not a
measurement, composed from the four phases' branch-uniform worst cases
(build→scan `703·n + 402`, count `84·n + 85`, range head `16`, the
pick loop charged `n` iterations though the family yields at most
`min n 3` distinct words, exit `78`). The MEASURED minimal fuels,
recorded separately: `582/1145/2007/2575/3206/4056/4612/5243/6093/8686`
at `n = 0…8, 12` (seed/qsel-independent at fixed `n`; the bound is
exact at `n = 0`).

**Status.** NOT DESIGNATED — see the note in *How to read an entry*: this
example post-dates the 2026-08-14 designation, and designation is arc-end
work under user sign-off, so its statement is not walked by the mechanized
statement-TCB gate and not replayed by the Comparator judge. What it does
have, in-build: four `rfl` lowering pins (`buildText_pin`, `wordFreq_pin`,
`wordfreqHarnessRFunc_pin` and — the one this entry turns on —
`goleanShimStringsFields_pin` on the INJECTED shim's own lowered body, all
in `Examples/WordFreq/Machine.lean`), the golden-lowering guard
(`scripts/check-golden` against `baselines/golden/wordfreq-lowered.repr`,
which includes that shim body, so shim drift is golden drift), and the
axiom pins above (`proofs/Audit/WordFreq.lean`). The deletion test was RUN
— `lean_minimal_hypotheses` on `wordfreq_ok`, **all four explicit binders
load-bearing** (`n seed qsel`, `hn`, `hseed`, `hqsel`).
`wordfreq_readout` is the run-conditioned twin;
`wordfreq_hits_eq` is the first-order readout corollary (the hits
value as pure residue arithmetic over `(n, seed, qsel)`).

**Ground.** Differentially green on 15 corpus rows (six literal-input
rows incl. empty text, all-space text, tabs/newlines and a missing
query; eight family-harness rows incl. `n = 0`, `n = 12`, a wrapping
seed and a wrapping `qsel`; plus the setup control) — 14 of them RED
at `frontend-export` until E5 landed, which was the point. The shim
itself is additionally pinned by the 8-row
`strings/fields-conformance/*` suite (leading/trailing/consecutive
mixed whitespace, NBSP/NEL/EM-SPACE/IDEOGRAPHIC-SPACE splitting, the
U+200B non-split, invalid UTF-8), each split observed byte-exactly
via a `'|'` join against the real stdlib.

---

## stack — LIFO through a growing slice, and a non-map `∀ choices`

**The Go** (`Corpus/coverage/exec/examples/stack/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/stack/main.go -->
```go
func push(s []uint64, v uint64) []uint64 {
	return append(s, v)
}

func pop(s []uint64) ([]uint64, uint64) {
	v := s[len(s)-1]
	return s[:len(s)-1], v
}

func peek(s []uint64) uint64 {
	return s[len(s)-1]
}

func size(s []uint64) uint64 {
	return uint64(len(s))
}
```

<!-- verbatim: Corpus/coverage/exec/examples/stack/main.go -->
```go
const stackCapN = 8

// stack_harness_r: the S3 RELATIONAL harness. Setup pushes the family
// seed + i (wrapping) for i < n, recording each pushed value; the test
// pops min(k, n) values, recording them in pop order; the observable is
// (pushed, popped, remaining size). The Lean postcondition relates the
// returned data directly: popped is the suffix of pushed, reversed —
// popped[j] = pushed[n-1-j] for j < min(k, n) — and remaining =
// n - min(k, n). Real Go, ghost ladder rung 0.
func stack_harness_r(n, seed, k uint64) ([stackCapN]uint64, [stackCapN]uint64, uint64) {
	s := []uint64{}
	var pushed [stackCapN]uint64
	for i := uint64(0); i < n; i++ {
		v := seed + i
		s = push(s, v)
		pushed[i] = v
	}
	m := k
	if n < m {
		m = n
	}
	var popped [stackCapN]uint64
	for j := uint64(0); j < m; j++ {
		var v uint64
		s, v = pop(s)
		popped[j] = v
	}
	return pushed, popped, size(s)
}
```

**The specification** (`proofs/GoLeanProofs/Examples/SliceStack.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/SliceStack.lean -->
```lean
/-- The returned fixed-cap array: the observed value list, zero-padded to
the harness's `stackCapN = 8` slots. Deliberately NOT shared with the
identically shaped arrays of other examples (the §11 closure rule). -/
def stArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map (fun v => .int v .uint64)⟩
```

**The specification is two list operations, and that is the whole point.**
LIFO is `pushed.reverse.take k` — pop order is push order reversed, truncated
at what the stack actually holds. The remaining size is `n - k` in **Nat**
subtraction, which truncates at zero, so an over-large `k` simply drains the
stack. No `min` appears anywhere in the statement: `List.take` already does
it. Read the sibling `queue` entry beside this one — its specification is the
same sentence with `.reverse` deleted, and that single word is the difference
between a stack and a queue.

**The theorem** (`proofs/GoLeanProofs/Examples/SliceStack.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/SliceStack.lean -->
```lean
theorem stack_ok (n seed k : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64)
    (hk : k < 2 ^ 64) :
    ∃ pushed : List Int, pushed.length = n ∧
      ∃ N : Nat, ∀ fuel ≥ N, ∀ ch : Choices,
        runFunctionWithContextM fuel stackLowered.typeDefs.toList
            stackLowered.funcs stackHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (k : Int) .uint64]
            stackLowered.methods ch
          = .ok { values := #[stArr8 pushed,
                              stArr8 (pushed.reverse.take k),
                              .int ((n - k : Nat) : Int) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/SliceStack.lean`):

<!-- verbatim: proofs/Audit/SliceStack.lean -->
```lean
/-- info: 'GoLean.Examples.SliceStack.stack_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/SliceStack.lean -->
```lean
/-- info: 'GoLean.Examples.SliceStack.stack_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**`∀ choices` does real work here, and it does so without a map** — this is
the first LIFO/stack-shaped entry of that kind; `rle` above is the gallery's
first non-map `∀ choices` entry, on the same `append`-capacity envelope.
`push` is Go's `append`, and the Go
specification does not fix the capacity a spilling `append` allocates: it
promises only "a new, sufficiently large underlying array". Real `gc` picks a
capacity by an amortized growth rule *and* by element-size-dependent
size-class rounding and stack buffering. The machine therefore does not pin
one number — it admits an **envelope** of capacities and consumes one
nondeterministic choice at each spilling append to select from it. So the
harness's own run is genuinely nondeterministic in its memory layout, and
`∀ ch` quantifies over that.

What the proof had to be, as a result: **capacity- and address-generic**. The
push-loop invariant carries the backing array's address and capacity as
*existentials* and never names them, so the theorem holds at every member of
the envelope. Three things are worth stating plainly about that:

- **The returned values do not depend on the choice** — capacity is not
  observable through this harness — which is why the postcondition mentions
  no capacity at all.
- **The step count does not depend on the choice either** (probe-checked at
  several streams): an `append` is one machine step whether it spills or not.
  That is what lets a single fuel bound cover every stream.
- **The heap layout does depend on it**, and so does *how many choices the run
  consumes*: a stream granting a large first capacity suppresses a later
  spill. A proof that had unrolled the loop to the concrete capacities of one
  stream would have been a true statement about that stream and a false one
  about `∀ ch`.

**Domain bounds, attributed.** `n ≤ 8` is **the program's own arithmetic**
(`stackCapN = 8`, visible in the corpus Go — Go's pass-by-value fragment
cannot return unbounded data). `seed < 2^64` and `k < 2^64` are **Go's
domain**, all of it; no hypothesis excludes the wrap region. The LIFO
relation itself is **mathematics**. Machine idealization as elsewhere.

**`∃ pushed` is family-determined.** The witness is the setup family
`seed + i` reduced mod 2^64; the statement merely avoids naming it. Genuine
∀-data needs the ghost rung-1 annotation, which is designed and not built.

**Fuel bound.** `N = 257·n + 254` — a branch-uniform **bound** that charges
every element the widest path (`min(k,n) = n`, plus the taken `n < k`
branch). **The measurement is a different number**: the exact count is
`242 + 130·n + 127·min(k,n) + 12·[n < k]`, probe-verified at `n = 0…8` with
`k` under, at and over `n`, and proved as an equality inside the module. The
two coincide exactly when `k > n` — the drain-everything rows — and the bound
is loose by `127·(n − k) + 12` when `k ≤ n`. Neither is presented as the
other.

**Status.** NOT DESIGNATED — see the note in *How to read an entry*. Added by
the gallery campaign (2026-08-15). In-build: the `rfl` lowering pins
(`push_pin`, `pop_pin`, `size_pin` on the subject, `stackHarnessRFunc_pin` on
the harness), the golden-lowering guard on both links, and the axiom pins
above. Its deletion test was RUN by the lane owner —
`lean_minimal_hypotheses` on `stack_ok`, **all four explicit binder groups
load-bearing** (`(n seed k)`, `hcap`, `hseed`, `hk`) — and then sharpened by a
machine probe, because "the proof needs it" and "the claim fails without it"
are different statements. `hcap` is a **totality** bound (at `n = 9` the
subject panics, `index out of range [8] with length 8`); `hk` is a **truth**
bound (the probe ran `n = 3, seed = 5, k = 2^64`: the machine normalizes `k`
to `0`, pops nothing and returns size `3`, against a postcondition that reads
`k` as the Nat `2^64`); `hseed` is a
**proof-structure** bound only (at `seed = 2^64` machine and statement still
agree — both reduce mod 2^64). `stack_readout` is the run-conditioned twin.

**Ground.** Differentially green on 13 corpus rows: `lifo-three`, `lifo-dup`,
`lifo-extremes`, `peek-two`, `empty-size`, and the relational harness at
`harness-empty`, `harness-one`, `harness-mid`, `harness-cap-drain`,
`harness-k0`, `harness-kn`, `harness-kover` and `harness-maxseed`. All eight
harness rows are inside the theorem's domain. **One honest gap between oracle
and theorem:** the largest seed any row pins is `2^63 − 1`
(`harness-maxseed`), because the differential driver's arguments are
int64-limited, so the region `[2^63, 2^64)` is claimed by the theorem and not
pinned by `go run`. It was probe-matched against the machine at
`seed = 2^64 − 1` and `2^64 − 2`; that is a weaker check and is labelled as
one.

## queue — FIFO through a growing slice, the same sentence with `.reverse` deleted

The sibling of the `stack` entry above, and the reason the wave built both:
the two programs differ only in which end they take from, and the two
theorems differ only by one word.

**The subject** (`Corpus/coverage/exec/examples/queue/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/queue/main.go -->
```go
func enqueue(q []uint64, v uint64) []uint64 {
	return append(q, v)
}

func dequeue(q []uint64) ([]uint64, uint64) {
	v := q[0]
	return q[1:], v
}
```

`enqueue` is Go's `append` at the back; `dequeue` reads `q[0]` and re-slices
`q[1:]`, which moves the header's offset forward and leaves the backing array
untouched. Both halves matter to the proof: the first is a growing slice, the
second is a slice expression whose *base is already a slice*.

**The harness** (same file):

<!-- verbatim: Corpus/coverage/exec/examples/queue/main.go -->
```go
func queue_harness_r(n, seed, k uint64) ([queueCapN]uint64, [queueCapN]uint64, uint64) {
	q := []uint64{}
	var enqueued [queueCapN]uint64
	for i := uint64(0); i < n; i++ {
		v := seed + i
		q = enqueue(q, v)
		enqueued[i] = v
	}
	d := k
	if n < k {
		d = n
	}
	var dequeued [queueCapN]uint64
	for i := uint64(0); i < d; i++ {
		var v uint64
		q, v = dequeue(q)
		dequeued[i] = v
	}
	return enqueued, dequeued, qsize(q)
}
```

**The specification** (`proofs/GoLeanProofs/Examples/SliceQueue.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/SliceQueue.lean -->
```lean
def qArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map (fun v => .int v .uint64)⟩
```

**FIFO is `enqueued.take k`.** Put it beside the stack's
`pushed.reverse.take k` and the difference between a stack and a queue is
one word of Lean. Nothing else in the two statements differs: same
zero-padded fixed-cap arrays, same Nat subtraction `n - k` for the remaining
size (truncating at zero, because the Go dequeues `min(k, n)` times and
returns `len(q)`), same absence of any `min` in the statement — `List.take`
supplies it.

**The theorem** (`proofs/GoLeanProofs/Examples/SliceQueue.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/SliceQueue.lean -->
```lean
theorem queue_ok (n seed k : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64)
    (hk : k < 2 ^ 64) :
    ∃ enqueued : List Int, enqueued.length = n ∧
      ∃ N : Nat, ∀ fuel ≥ N, ∀ ch : Choices,
        runFunctionWithContextM fuel queueLowered.typeDefs.toList
            queueLowered.funcs queueHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
              .int (k : Int) .uint64]
            queueLowered.methods ch
          = .ok { values := #[qArr8 enqueued,
                              qArr8 (enqueued.take k),
                              .int ((n - k : Nat) : Int) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit/SliceQueue.lean`):

<!-- verbatim: proofs/Audit/SliceQueue.lean -->
```lean
/-- info: 'GoLean.Examples.SliceQueue.queue_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/SliceQueue.lean -->
```lean
/-- info: 'GoLean.Examples.SliceQueue.queue_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**`∀ choices` does real work here too, for the same reason as `stack`.**
`enqueue` is `append`, so a spilling enqueue consumes one nondeterministic
choice to fix the fresh backing array's capacity inside the machine's growth
envelope. The enqueue-phase invariant is therefore **capacity- and
address-generic**: it carries the backing address, the capacity and the dead
cell tail as existentials and never names them. Measured at `n = 8, k = 4`:
the run takes **1750 steps at every stream**, while `nextAddr` lands at 97 or
96 and the run consumes 2 choices or 1 depending on the stream — an early
large capacity suppresses a later spill. Returned values and step count are
choice-invariant; layout and choice count are not.

**The dequeue half is choice-free, and that is a fact about `q[1:]`.**
Re-slicing only advances the header's offset — no allocation, no copy — so
the whole dequeue phase rides the stream through unchanged. It is the reason
the two loops have different per-iteration costs (130 steps per enqueue
against 117 per dequeue).

**Domain bounds, attributed.** `n ≤ 8` is **the program's own arithmetic**
(`const queueCapN = 8`, visible in the corpus Go). `seed < 2^64` and
`k < 2^64` are **Go's domain**, all of it, wrap region included. FIFO itself
is **mathematics**. Machine idealization as elsewhere.

**`∃ enqueued` is family-determined.** The witness is `seed + i` reduced mod
2^64; the statement avoids naming it, as in `stack`, `histogram` and
`dotprod`. Genuine ∀-data needs the ghost rung-1 annotation, which is
designed and not built.

**Fuel bound.** `N = 247·n + 254` — a branch-uniform **bound** that charges
every element the widest path. **The measurement is a different number**: the
exact count is `242 + 130·n + 117·min(k,n) + 12·[n < k]`, proved as an
equality inside the module (`q_run`) and probe-confirmed at thirteen `(n,k)`
points. The two coincide exactly when `k > n` — the drain-everything rows,
where the measured count at `n = 8, k = 9` is 2230 and the bound is 2230 —
and the bound is loose by `117·(n − k) + 12` when `k ≤ n`. Neither is
presented as the other.

**Status.** NOT DESIGNATED — see the note in *How to read an entry*. Added by
the gallery campaign (2026-08-15). In-build: the `rfl` lowering pins
(`enqueue_pin`, `dequeue_pin`, `qsize_pin` on the subject,
`queueHarnessRFunc_pin` on the harness), the golden-lowering guard on both
links, and the axiom pins above. `queue_readout` is the run-conditioned twin.

**Ground.** Differentially green on 13 corpus rows. **The same honest gap as
its sibling:** the differential driver's arguments are int64-limited, so no
row pins a seed above `2^63 − 1`, and the region `[2^63, 2^64)` is claimed by
the theorem and not pinned by `go run`. It was probe-matched against the
machine at `seed = 2^64 − 1` and `2^64 − 2`, across four choice streams; that
is a weaker check and is labelled as one.

## matmul — 3×3 matrix multiply, the first 2-D example and the GAP-RFL-COST closure

The gallery's twenty-fifth entry has a history the others don't: it is
the example that DISCOVERED the campaign's one recorded cost-class
blocker (GAP-RFL-COST, `docs/gallery-campaign-log/g1.md` unit G1.9), was
withdrawn rather than shipped unverified, and lands now as the measured
acceptance test of the WP arc's mirror symbolic evaluator — the same
statements, a different discharge for exactly the segments that blocked.
The two-stage numbers are at the end of this entry.

**The subject** (`Corpus/coverage/exec/examples/matmul/main.go`):

<!-- verbatim: Corpus/coverage/exec/examples/matmul/main.go -->
```go
func matMul(a, b [matN][matN]uint64) [matN][matN]uint64 {
	var c [matN][matN]uint64
	for i := 0; i < matN; i++ {
		for j := 0; j < matN; j++ {
			var sum uint64
			for k := 0; k < matN; k++ {
				sum += a[i][k] * b[k][j]
			}
			c[i][j] = sum
		}
	}
	return c
}
```

with `const matN = 3` and the seeded input family (same file):

<!-- verbatim: Corpus/coverage/exec/examples/matmul/main.go -->
```go
func seedMat(seed uint64) [matN][matN]uint64 {
	var m [matN][matN]uint64
	for i := 0; i < matN; i++ {
		for j := 0; j < matN; j++ {
			m[i][j] = seed + uint64(i*matN+j)
		}
	}
	return m
}
```

**The harness** (same file):

<!-- verbatim: Corpus/coverage/exec/examples/matmul/main.go -->
```go
func matmul_harness_r(seed uint64) ([matN][matN]uint64, [matN][matN]uint64, [matN][matN]uint64) {
	a := seedMat(seed)
	b := seedMat(1)
	return a, b, matMul(a, b)
}
```

Go arrays are VALUES: `[3][3]uint64` arguments and results cross the
call and return boundaries by copy, which is why a genuinely 2-D
example fits the pass-by-value fragment with no fixed-cap workaround —
the harness returns all three matrices whole and the postcondition is
an S3 RELATION over the returned data.

**The specification** (`proofs/GoLeanProofs/Examples/MatMul.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/MatMul.lean -->
```lean
def matSpec (a b : List (List Int)) : List (List Int) :=
  (List.range 3).map (fun i =>
    (List.range 3).map (fun j =>
      ((List.range 3).map (fun l => mmGet a i l * mmGet b l j)).sum
        % (2 ^ 64 : Int)))
```

with `mmGet m i j = (m.getD i []).getD j 0` — the obvious mathematical
matrix product, each entry the true integer sum `Σₖ aᵢₖ·bₖⱼ` reduced
ONCE mod 2^64. A reader can check it against the Go triple loop by eye.

**The theorem** (`proofs/GoLeanProofs/Examples/MatMul.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/MatMul.lean -->
```lean
theorem matmul_ok (seed : Nat) (hseed : seed < 2 ^ 64) :
    ∃ a b : List (List Int),
      a.length = 3 ∧ b.length = 3 ∧
      (∀ r ∈ a, r.length = 3) ∧ (∀ r ∈ b, r.length = 3) ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel matmulLowered.typeDefs.toList
            matmulLowered.funcs matmulHarnessRFunc
            #[.int (seed : Int) .uint64]
            matmulLowered.methods ch
          = .ok { values := #[mmArr3 a, mmArr3 b, mmArr3 (matSpec a b)] } := by
```

**Axioms** (pinned in `proofs/Audit/MatMul.lean`):

<!-- verbatim: proofs/Audit/MatMul.lean -->
```lean
/-- info: 'GoLean.Examples.MatMul.matmul_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit/MatMul.lean -->
```lean
/-- info: 'GoLean.Examples.MatMul.matmul_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project
axioms — including through the transported segments (the refinement
theorem they ride is itself classical-trio, and it is a PROOF DEVICE:
no `GoLean.Sym` constant appears in the statement's closure).

**THE ARITHMETIC WRAPS, AND THE CLAIM SAYS SO.** Every multiply and
every accumulation in `matMul` is uint64 and genuinely reduces mod
2^64; `matSpec` is the true integer sum with ONE final reduction, and
the theorem covers the FULL `seed < 2^64` domain — no hypothesis
excludes the wrap region. The per-step wrapping equals the single
reduction because normalization is idempotent and mod distributes over
sum and product (`mm_c_final` — proved by `omega`, not assumed; linear
because `b`'s entries are the literals `1…9`).

**`∃ a b` is family-determined.** The witnesses are `aClean seed`
(`a[i][j] = seed + (3i+j)`, wrapped) and the CONSTANT
`b = [[1,2,3],[4,5,6],[7,8,9]]` — `b` IS `seedMat 1`, a constant
matrix, and a reader should not have to discover that; the statement
merely avoids saying so. Genuinely ∀-quantified input matrices need the
ghost rung-1 annotation, which is designed and not built.

**Domain bounds, attributed.** The `3×3` shape is the PROGRAM's own
`matN` constant; `seed < 2^64` is Go's uint64 domain, wrap region
included; the matrix product is mathematics. Machine idealization as in
every other entry.

**Fuel bound.** `N = 5247`, EXACT and constant — `matN = 3` is a
compile-time constant, so the control flow is fully concrete and every
run takes exactly 5247 steps; the triple loop contributes `matN³ = 27`
inner iterations, so the constant is cubic in the (fixed) dimension.
Bound and probe measurement COINCIDE (both 5247, re-probed at THIS
tree at `seed = 0`, `5`, `2^63−1`: 5247 succeeds, 5246 fails), and the
proof's 82 chained segment counts sum to it. Neither is presented as
the other. **`∀ ch` is vacuous and stated anyway** — the run consumes
no choice (no map ranges, no `append`).

**Deletion test** — RUN as a machine probe, the `queue` pattern.
`hseed` comes back PROOF-STRUCTURE load-bearing only: at
`seed = 2^64`, `2^64 + 5`, and `2^65 + 7` — all outside the theorem's
domain — the machine's returned triple still matches the wrapped
family postcondition (entry normalization and `aClean` reduce mod 2^64
together), so `hseed` is a frontier of the proof (it feeds the entry
equation's normal form and every `omega` bridge), not of the truth.
`seed` itself is the argument and trivially load-bearing.

**The proof, and the GAP-RFL-COST closure — the two-stage record.**
This module's proof is a straight-line chain of 75 per-window segment
lemmas (no loop induction: all control flow is concrete), assembled
over exactly 5247 steps. It is the artifact that DISCOVERED the
campaign's one cost-class blocker, and landing it produced TWO
closures, measured in two stages at the landing tree (full record:
`docs/wp-arc-log/s4.md` unit S4.11):

- *Stage (a), restore + retrofit alone (the baseline):* the withdrawn
  2,375-line layer, retrofitted to the current kit (−14 lines: two
  local arithmetic lemmas subsumed by the s1-lift op-facts), still
  does NOT elaborate under default options — a bounded single-segment
  probe re-measured one 291-step `seedMat` store window at **61.4 s**
  of `rfl` tactic time (the campaign's recorded 61–326 s class), and
  the whole-file elaboration was cut INCOMPLETE at **117 min** with
  the three worst segments already excluded (the campaign's three
  cuts: 57–114 min, with them included).
- *Stage (b), the landing:* the three measured blocker segments (the
  291-step `seedMat(seed)` outer iterations) are discharged through
  the WP arc's mirror symbolic evaluator — `symEvalWindow_refines'`:
  a compiled `#guard` of the window's step count, one kernel `rfl` on
  the count projection, the refinement theorem, and a defeq `exact`
  landing on the statement's own spelling — at **~1.3 s each**
  (47–250× the raw class), statements BYTE-IDENTICAL to the withdrawn,
  probe-confirmed forms. **And the root cause fell out of the
  landing:** the class is a MetaM smart-unfolding pathology,
  elaboration-side only — the kernel re-checked the same proofs in
  milliseconds throughout, and under `set_option smartUnfolding
  false` the worst raw segment takes **1.09 s**. The other 72 windows
  stay raw `rfl` under that option. Whole module: **109 s wall /
  2.30 GiB peak** bare elaboration; `scripts/proof-costs` records
  **167.00 s / 2450 MiB** for the in-lake build (under the campaign's
  ~2560 MiB bar; `Audit.MatMul` 0.66 s / 1664 MiB). The all-raw
  variant with the option alone measures 107 s — the entry credits
  the option, not the evaluator, with that part of the win.

The evaluator is OUTSIDE the statement: `GoLean.Sym` is proof
automation (WP arc slice 4), mechanically refused from designated
statement closures by the statement-TCB walker, and this statement's
own closure is interpreter vocabulary + `matSpec`/`mmArr3` + the
pinned harness only.

**Status.** NOT DESIGNATED — see the note in *How to read an entry*.
Corpus half added by the gallery campaign's guardrails wave; headline
landed by the WP arc (2026-08-18) as slice 4's chartered acceptance.
In-build: the `rfl` lowering pins (`seedMat_pin`, `matMul_pin` on the
subjects, `matmulHarnessRFunc_pin` on the harness), the golden-lowering
guard on both links (`scripts/check-golden` ok), and the axiom pins
above. `matmul_readout` is the run-conditioned twin.

**Ground.** Differentially green on 11 corpus rows (products against
identity, zero, scalar-diagonal matrices; seed traces; the harness
itself at basic and wrap seeds). **The same honest gap as `stack` and
`queue`:** the differential driver's arguments are int64-limited, so no
row pins a seed above `2^63 − 1`; the region `[2^63, 2^64)` is claimed
by the theorem and was probe-matched against the machine (an
independently re-implemented spec, seeds `2^64−1`, `2^64−2`, `2^64−6`,
re-run at the landing tree) — a weaker check, labelled as one.

## The derived twins, and the one axiom line they share

Each "run-conditioned twin" (`fib_readout`, `reverse_readout`, …) says: *any*
successful run of the harness, at any fuel and any choice stream, returns
that value. They are not re-proved — they are derived from the headline
through one shared bridge, whose axioms are pinned like everything else:

<!-- verbatim: proofs/Audit.lean -->
```lean
/-- info: 'GoLean.Surface.harness_readout_of_total' depends on axioms: [propext, Quot.sound] -/
```

## Staleness

Every Go, Lean and axiom block above is marked in the source of this file
with `<!-- verbatim: <path> -->` and must match that path byte-for-byte:

    scripts/render-gallery            # exit 0 = fresh, 1 = stale, 2 = broken

It is a speedbump, not a proof: it checks that the quotes are real, not that
the English is faithful — that check is a reader's, which is exactly why the
programs, the harnesses and the theorems are all printed here in full. It is
standalone (not part of `scripts/ci`); run it after touching an example
module, a corpus example program, `proofs/Audit.lean`, or this file.
