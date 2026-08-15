# Verified examples — the gallery (2026-08-14)

Eight Go programs, and for each one a GoLean theorem you can read.

This file is the **object of agreement**: it exists so that a reader who is
not a Lean expert can check, by eye, that the top-level statement really
establishes the property they want — *no errors, and returns the correct
value* — for a Go program they can also read. Nothing here is summarised
from a proof: every Go snippet, every theorem, and every axiom line below is
quoted **verbatim** from the file it comes from, and `scripts/render-gallery`
re-checks those quotes byte-for-byte (see *Staleness*, at the end).

Arc record: `docs/2026-08-14_examples-phase2-arc-charter.md` — the phase-2
arc, which swapped three of the headlines and designated all eight; the
founding arc is `docs/2026-08-12_verified-examples-arc-charter.md`. The
statement form and the rulings behind it:
`docs/2026-08-12_example-spec-form.md` §11.

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
  **The ninth entry, `histogram`, is NOT designated.** It was added by the
  gallery campaign (2026-08-15) and designation is a separate, user-signed
  act at the end of that arc: it is deliberately absent from
  `Examples/Targets.lean`, from `scripts/ci`'s trusted-closure allowlist and
  from the Comparator judge's set. Its deletion test was therefore RUN by
  hand rather than by the gate — `lean_minimal_hypotheses` on
  `histogram_ok`, all four explicit binders load-bearing — and that is
  exactly the weaker standing that undesignated means. Its axioms are pinned
  in-build like everyone else's (`proofs/Audit/Histogram.lean`).
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
holds at **every** such stream. For six of the eight examples this quantifier
is cheap (their runs consume no choices). For word-count and histogram it
does real work: `for … range` over a Go map consumes one choice per
iteration, because Go deliberately does not fix map iteration order — so the
theorem covers every order, and the specification is *forced* to be
order-independent. A spec saying "the count of the first key" would be
unprovable there. That unprovability is the model working.

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

**The family** (`proofs/GoLeanProofs/Examples/Reverse.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Reverse.lean -->
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
