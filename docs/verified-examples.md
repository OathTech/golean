# Verified examples — the gallery (2026-08-14)

Seven Go programs, and for each one a GoLean theorem you can read.

This file is the **object of agreement**: it exists so that a reader who is
not a Lean expert can check, by eye, that the top-level statement really
establishes the property they want — *no errors, and returns the correct
value* — for a Go program they can also read. Nothing here is summarised
from a proof: every Go snippet, every theorem, and every axiom line below is
quoted **verbatim** from the file it comes from, and `scripts/render-gallery`
re-checks those quotes byte-for-byte (see *Staleness*, at the end).

Arc record: `docs/2026-08-12_verified-examples-arc-charter.md`; the statement
form and the rulings behind it: `docs/2026-08-12_example-spec-form.md` §11.

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
- **The program in each theorem is not retyped by hand.** It is the
  frontend's lowering of the corpus `main.go`, pinned by `scripts/check-golden`
  on both links — a fresh frontend emit + decode must reproduce the checked-in
  baseline, and the checked-in Lean term must print the same. Each proof module
  additionally pins the harness function *inside* that lowering by `rfl`, so
  "the theorem is about this Go file" is a checked chain rather than a claim.
- **Nothing else.** The statements mention interpreter vocabulary, the pinned
  program, and specification functions defined in the same file (`fibSpec`,
  `findSpec`, …). No separation logic, no weakest-precondition machinery, no
  Iris appears in any statement — those are proof devices, and deleting the
  entire proof layer leaves these statements elaborating unchanged.
- **The heap is empty at entry.** Each theorem starts the harness from an
  empty state with its arguments at the call boundary, so the harness
  allocates everything it touches. There is nothing to frame, and no
  heap-level clause appears in any statement — the memory analysis happens in
  Go, inside the verified footprint.

## What "∀ choices" means

`Choices` is the stream of nondeterministic decisions the machine consumes at
points where Go does not promise an outcome. `∀ ch : Choices` says the claim
holds at **every** such stream. For six of the seven examples this quantifier
is cheap (their runs consume no choices). For word-count it does real work:
`for … range` over a Go map consumes one choice per iteration, because Go
deliberately does not fix map iteration order — so the theorem covers every
order, and the specification is *forced* to be order-independent. A spec
saying "the count of the first key" would be unprovable there. That
unprovability is the model working.

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
  (`n ≤ 93`, `len < 2^63`, `len < 2^62`), the entry says whether it is the
  mathematics, Go's own type domain, or the program's own arithmetic —
  including where the bound exists because the program has a real,
  famous bug.

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

**The specification function** (`proofs/GoLeanProofs/Examples/Fib.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Fib.lean -->
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

**Axioms** (pinned in `proofs/Audit.lean`):

<!-- verbatim: proofs/Audit.lean -->
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
// reverse_harness: three-phase harness (harness ruling 2026-08-13).
// setup_reverse_state: build s from the scalar parameters — the
// input FAMILY s[i] = seed + i (wrapping); test_reverse_state:
// verify the reversal element-wise in Go and fold into a verdict.
func reverse_harness(n, seed uint64) uint64 {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i
	}
	reverse(s)
	ok := uint64(1)
	for i := uint64(0); i < n; i++ {
		if s[i] != seed+(n-1-i) {
			ok = 0
		}
	}
	return ok
}
```

**The claim.** For every length `n < 2^63` and every `seed < 2^64`,
`reverse_harness(n, seed)` finishes normally, at every nondeterminism choice,
and returns `1`. **What `1` means is in the Go above**: setup builds
`s[i] = (seed + i) mod 2^64`, `reverse` runs, and the test phase checks
element-wise — in Go, inside the verified footprint — that `s[i]` now equals
`seed + (n-1-i)` (again in wrapping `uint64` arithmetic). The claim is exactly
*"that check passed, for every `(n, seed)` in the domain"*, and no more.

The bound `n < 2^63` is **Go teaching us its own domain**, not a proof
limitation: `make([]uint64, n)` takes a Go `int`, so past `2^63` the length is
no longer an `int` value at all — it wraps negative and the program panics.
The statement says where the program works rather than pretending the
boundary is not there.

Input honesty: the quantifiers are the scalars `(n, seed)` — an input
*family*, not all slices. The wrapping is deliberate, so the family crosses
the `2^64` boundary.

**The family** (`proofs/GoLeanProofs/Examples/Reverse.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Reverse.lean -->
```lean
def revFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i) % 2 ^ 64 : Nat) : Int))
```

**The theorem** (`proofs/GoLeanProofs/Examples/Reverse.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/Reverse.lean -->
```lean
theorem reverse_ok (n seed : Nat) (hn : n < 2 ^ 63) (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel reverseLowered.typeDefs.toList
          reverseLowered.funcs reverseHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          reverseLowered.methods ch
        = .ok { values := #[.int 1 .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit.lean`):

<!-- verbatim: proofs/Audit.lean -->
```lean
/-- info: 'GoLean.Examples.Reverse.reverse_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and affine: `N = 189·n + 260`.

**Status.** `reverse_readout` is the run-conditioned twin. The stronger
input claim lives beneath as `reverse_framed`: for **any** list of `uint64`
values, wherever it sits in memory and whatever else is present, `reverse`
finishes and that memory then holds the list reversed with nothing else
touched. It is genuinely ∀-data — the harness family does not subsume it —
and it is kept as supporting material because the user-facing form observes
only returned values.

**Ground.** Differentially green on 8 corpus rows (four/three/one/empty
element drivers and an `int64`-boundary value) plus the harness at `(5,100)`,
`(0,7)` and a near-`2^63` wrapping seed.

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
// minmax_harness: three-phase harness — setup builds the family
// s[i] = seed + i (wrapping); the returned pair is the observable
// (returned data preferred over a verdict where arity permits).
func minmax_harness(n, seed uint64) (uint64, uint64) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i
	}
	return minMax(s)
}
```

**The claim.** For every `n` with `1 ≤ n < 2^63` and every `seed < 2^64`,
`minmax_harness(n, seed)` finishes normally, at every nondeterminism choice,
and returns exactly the pair (minimum, maximum) of the family
`s[i] = (seed + i) mod 2^64`. Here the harness returns *data*, not a verdict,
so the claim is the value itself.

Two bounds, both Go's own. `1 ≤ n`: `minMax` reads `s[0]`, so the empty slice
panics — the theorem excludes it honestly instead of quietly succeeding, and
the corpus pins that panic against `go run` (row `harness-empty-panics`).
`n < 2^63`: Go's `int` domain for lengths again. Because the family wraps at
`2^64`, the answer is not simply the first and last element once `seed + n`
crosses the boundary.

**The specification functions** (`proofs/GoLeanProofs/Examples/MinMax.lean`;
their `[]` cases are unreachable here, since `n ≥ 1`):

<!-- verbatim: proofs/GoLeanProofs/Examples/MinMax.lean -->
```lean
def minSpec : List Int → Int
  | [] => 0
  | [v] => v
  | v :: w :: rest => min v (minSpec (w :: rest))
```

<!-- verbatim: proofs/GoLeanProofs/Examples/MinMax.lean -->
```lean
def maxSpec : List Int → Int
  | [] => 0
  | [v] => v
  | v :: w :: rest => max v (maxSpec (w :: rest))
```

<!-- verbatim: proofs/GoLeanProofs/Examples/MinMax.lean -->
```lean
def mmFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i) % 2 ^ 64 : Nat) : Int))
```

**The theorem** (`proofs/GoLeanProofs/Examples/MinMax.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/MinMax.lean -->
```lean
theorem minmax_ok (n seed : Nat) (h1 : 1 ≤ n) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel minMaxLowered.typeDefs.toList
          minMaxLowered.funcs mmHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          minMaxLowered.methods ch
        = .ok { values := #[.int (minSpec (mmFamily n seed)) .uint64,
                            .int (maxSpec (mmFamily n seed)) .uint64] } := by
```

**Axioms** (pinned in `proofs/Audit.lean`):

<!-- verbatim: proofs/Audit.lean -->
```lean
/-- info: 'GoLean.Examples.MinMax.minmax_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and affine: `N = 145 + 149·n`.

**Status.** `minmax_readout` is the run-conditioned twin; `minmax_framed` /
`minmax_framed_readout` are the memory-quantified companions — ∀ list, with
the additional claim that the input slice comes back unchanged (the program
is read-only on its input) and other memory is untouched. Supporting
material.

**Ground.** Differentially green on 9 corpus rows including the empty-slice
panic (both through the driver and through the harness) and an
`int64`-boundary value, plus the harness at `(5,40)` and `(1,7)`.

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
(`proofs/GoLeanProofs/Examples/BinSearch.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/BinSearch.lean -->
```lean
def findSpec (xs : List Int) (t : Int) : Int :=
  match xs with
  | [] => -1
  | v :: rest =>
      if v = t then 0
      else if findSpec rest t < 0 then -1 else findSpec rest t + 1
```

<!-- verbatim: proofs/GoLeanProofs/Examples/BinSearch.lean -->
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

**Axioms** (pinned in `proofs/Audit.lean`):

<!-- verbatim: proofs/Audit.lean -->
```lean
/-- info: 'GoLean.Examples.BinSearch.search_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and affine: `N = 220 + 132·n`.

**Status.** This is the one entry with **no run-conditioned twin at the
harness form** — `search_framed_readout` exists for the memory-quantified
companion only. `search_framed` is that companion (∀ sorted list, at any
placement, other memory preserved, input array unchanged); both are
supporting material. Also proved on the way: the post-loop `&&` really is
lazy — when `lo = len(s)`, the out-of-bounds read `s[lo]` never happens.

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

`n < 2^63` is Go's `int` domain for lengths, as in reverse. Input honesty:
the quantifiers are the scalars `(n, seed)`.

**The family** (`proofs/GoLeanProofs/Examples/InsertionSort.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/InsertionSort.lean -->
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

**Axioms** (pinned in `proofs/Audit.lean`):

<!-- verbatim: proofs/Audit.lean -->
```lean
/-- info: 'GoLean.Examples.InsertionSort.isort_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit.lean -->
```lean
/-- info: 'GoLean.Examples.InsertionSort.isort_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and **quadratic**, honestly so — the harness's
count-based permutation check is O(n²):
`N = (92·n+160)·n + (110·n+220)·n + 285·n + 505`.

**Status.** `isort_readout` is the run-conditioned twin. The mathematical
sortedness claim lives beneath, in the memory-quantified companion
`isort_framed`: for **any** list of `uint64` values, wherever it sits in
memory, the slice afterwards holds `sortSpec xs` — proven sorted
(`sortSpec_sorted`), of the same length (`sortSpec_length`) and a permutation
(`sortSpec_count`: every value keeps its multiplicity) — with other memory
untouched. That companion, not the harness verdict, is where "insertion sort
sorts" is stated in mathematics. Also proved on the way: at `j = 0` the
machine provably never reads `s[j-1]` — Go's short-circuit `&&` is
load-bearing here, and it is exhibited in a theorem rather than only in
tests.

**Ground.** Differentially green on 11 corpus rows
(shuffled/sorted/reversed/duplicates/`int64`-boundary/three/one/empty) plus
the harness at `(5,37)`, `(6,0)` (all-equal family) and `(0,5)`.

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
// wordcount_harness: three-phase harness — setup builds the word
// family w[i] = seed + i%3 (controllable multiplicities); the
// returned max count is the observable (returned data).
func wordcount_harness(n, seed uint64) uint64 {
	w := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		w[i] = seed + i%3
	}
	return maxCount(w)
}
```

**The claim.** For every `n < 2^63` and every `seed` in the `uint64` domain,
`wordcount_harness(n, seed)` finishes normally and returns exactly
`(n+2)/3` — that is `⌈n/3⌉`, the largest number of times any word id occurs
in the family `w[i] = (seed + i%3) mod 2^64` (the ids cycle through three
values, so the most frequent one appears `⌈n/3⌉` times — including the short
cases `n = 0, 1, 2`). There is no side condition on `seed`: the three
residues cannot collide at any seed, wrap included.

**This is the entry where `∀ ch : Choices` earns its keep.** The subject
iterates over a Go **map**, and Go deliberately does not fix map iteration
order; the machine therefore consumes one nondeterministic choice per
iteration, and the theorem holds at every one of them — i.e. **at every
iteration order Go could exhibit**. That forces the specification to be
order-independent: "the largest multiplicity" is provable, while "the count
of the first key visited" would not be, since different orders would give
different answers. The envelope rejects order-dependent claims by
construction.

`n < 2^63` is Go's `int` domain for lengths; `seed < 2^64` is just the
argument's type.

**The specification layer** (`proofs/GoLeanProofs/Examples/WordCount.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/WordCount.lean -->
```lean
def multiplicity (v : Int) (ws : List Int) : Nat :=
  (ws.filter (· = v)).length
```

<!-- verbatim: proofs/GoLeanProofs/Examples/WordCount.lean -->
```lean
def maxMultiplicity (ws : List Int) : Nat :=
  ws.foldl (fun acc v => max acc (multiplicity v ws)) 0
```

<!-- verbatim: proofs/GoLeanProofs/Examples/WordCount.lean -->
```lean
def wcFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i % 3) % 2 ^ 64 : Nat) : Int))
```

and the closed form that ties the family to the returned number:

<!-- verbatim: proofs/GoLeanProofs/Examples/WordCount.lean -->
```lean
theorem wcFamily_maxMult (n seed : Nat) :
    maxMultiplicity (wcFamily n seed) = (n + 2) / 3 := by
```

**The theorem** (`proofs/GoLeanProofs/Examples/WordCount.lean`):

<!-- verbatim: proofs/GoLeanProofs/Examples/WordCount.lean -->
```lean
theorem wordcount_ok (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel wordCountLowered.typeDefs.toList
          wordCountLowered.funcs wordcountHarnessFunc
          #[.int ((n : Nat) : Int) .uint64, .int ((seed : Nat) : Int) .uint64]
          wordCountLowered.methods ch
        = .ok ⟨#[.int (((n + 2) / 3 : Nat) : Int) .uint64]⟩ := by
```

Two rendering notes, recorded rather than edited (statements are never
reshaped for the gallery): `⟨#[…]⟩` is the same `Result` record the other
entries spell `{ values := #[…] }`, written with the anonymous constructor;
and `((n : Nat) : Int)` is a redundant-looking but harmless coercion of an
argument that is already a `Nat`.

**Axioms** (pinned in `proofs/Audit.lean`):

<!-- verbatim: proofs/Audit.lean -->
```lean
/-- info: 'GoLean.Examples.WordCount.wordcount_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

<!-- verbatim: proofs/Audit.lean -->
```lean
/-- info: 'GoLean.Examples.WordCount.wordcount_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
```

Lean's classical trio; no `sorry`, no native evaluation, no project axioms.

**Fuel bound.** Explicit and affine: `N = 229 + 165·n`.

**Status.** `wordcount_readout` is the run-conditioned twin. Beneath the
harness form sits the stronger input claim `maxCount_total_canonical`: for
**any** list of word ids (not just the three-residue family), at every
choice stream, the subject finishes and delivers the maximum multiplicity —
the ∀-data claim the scalar family does not subsume. `wordcount_empty_ok`
covers the zero-argument degenerate harness. Supporting material.

**Ground.** Differentially green on 8 corpus rows (distinct / all-same /
mode-of-three / two-pairs / one / empty) plus the harness at `(7,50)` and
`(0,9)`; the `(n+2)/3` closed form was additionally cross-checked against
`go run` at seeds `0`, `50`, `2^63−1`, `2^64−3`, `2^64−2`, `2^64−1` before
any of it was written in Lean.

---

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
