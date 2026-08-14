# Harness spec-style scoping study (2026-08-14)

Status: SCOPING STUDY — no verification, no proofs. All seven gallery
examples were drafted in every candidate harness spec style that is not a
degenerate repeat, EXCEPT three S4 cells (minmax, binsearch, wordcount)
noted in the matrix as the same pattern as an already-drafted cell —
13 drafts and 9 probes on disk. Every draft
was **executed** (`go run` — real test code) and **run through the real
pipeline** (`tools/nativefrontend` emit → `golean native-json-run`),
and every proposed Lean headline was **elaborated** against the actual
machine vocabulary (`.tmp/scoping/statements.lean`, `sorry` proofs,
scratch only). Context: the harness ruling
(`docs/2026-08-12_example-spec-form.md` §11), the shipped gallery
(`docs/verified-examples.md`). Scratch artifacts: `.tmp/scoping/`
(probes + drafts + wire.json + the statements file; not tracked).

The brief (user framing, verbatim): the current value+family style "is
a bit of a hack because it's saying something like 'Here's a function
in Go (including setup/teardown) — here's a model in Lean' — but it
doesn't directly state anywhere in Lean what binsearch is." The ideal:
"all the harnesses are simple Go that can be executed as test code and
understood in the 'testing mock' style."

## §0 Standing constraints ruled during the study (user, 2026-08-14)

**C1 — Harnesses are COMPILABLE GO.** Every harness in every style is
plain Go source that `go build` accepts and `go run` executes — no
pseudo-syntax, no stub intrinsics. Spec-level extras (ghost values,
nondeterminism markers) are COMMENTS/ANNOTATIONS with zero execution
effect (CN/Gobra-style magic comments). Semantics: the compiled harness
executes at its concrete written values — ONE witnessed family member,
the differential lower bound; the annotation tells the VERIFIER what to
generalize (e.g. `// @ghost nondet` on an assignment means the theorem
draws that value from the choice stream). The same file is both the
runnable test and the quantified theorem subject; the two-bounds
doctrine is the coherence story (executed = membership witness,
annotated = envelope). Every draft below passes this check — all 13
were run with `go run` as-is.

Frontend integration point (DESIGNED, not built): annotations are
parsed at the **NativeToIR boundary**, fail closed on unknown markers,
and never become GoCore nodes — the standing frontend-quarantine
architecture applied to annotation vocabulary.

**C2 — The decoupling design rule** (doctrine-adjacent; record): spec
styles are THIN ADAPTERS over a style-neutral proof core — the
canonical-run segments, segment composition, fuel measures, entry glue,
and the framed theorems. No style vocabulary leaks below the statement
layer; annotation parsing stays quarantined at NativeToIR. Evidence:
both form pivots this arc (cell-readback → memory-quantified →
harness-return) cost only the statement layer — ~95% of the proof core
was reused, measured across the restatements. The stack must support
OTHER spec styles later if this one fails ("a bit decoupled from the
actual interpreter / verification machinery"). Each style below is
therefore also scored on **adapter thinness**: how much style-specific
machinery it would demand below the statement layer.

## §1 The styles

- **S1 VERDICT** — the test phase checks the property in Go; the Lean
  post is `return = 1`. (The shipped isort entry is already exactly
  this; shipped reverse is a family-formula variant of it.)
- **S2 VALUE+FAMILY** (status quo) — the harness returns computed data;
  the Lean post equates it with a spec function of the arguments, with
  family functions (`mmFamily`, `bsFamily`, …) re-describing the setup.
- **S3 RELATIONAL over the value fragment** — the harness returns BOTH
  pre-state and post-state as pure Go values (structs / fixed-size
  arrays / scalars); the Lean post relates them directly
  (`post = pre.reverse`, `lo = minSpec pre`, `idx = findSpec pre t`).
- **S4 RELATIONAL-STRING** — pre/post encoded as strings
  (fmt.Sprint-shaped); the Lean post relates the strings through a
  Lean-side rendering of the quantified data.

Interface principle under test: **the harness interface is Go's own
pass-by-value fragment** — scalars, structs, fixed-size arrays, strings
cross the boundary as pure values; slices/maps/reference types live in
memory and get setup/test treatment. §6 assesses it against the
evidence.

Evaluation axes per cell: DIRECTNESS (does Lean state the subject's
property, or only a harness↔model correspondence?), READER SURFACE
(what must be read), FEASIBILITY TODAY (probed, never assumed),
PROOF-COST FORECAST (grounded in this arc's segment/measure/StepKit
techniques), ANNOTATION VOCABULARY needed (C1; more = worse on the
testing-mock ideal), ADAPTER THINNESS (C2).

## §2 Feasibility findings — probe evidence (all verbatim)

Pipeline per probe: `go run` (oracle) → `go run ./tools/nativefrontend
--dir <d> --out wire.json` → `.lake/build/bin/golean native-json-run
--input wire.json --function <harness> --arg-int …`. Probe sources:
`.tmp/scoping/probes/`.

| # | Probe | Machine classification (verbatim status/value) |
|---|-------|------------------------------------------------|
| P1 | struct return (`Pair{A,B uint64}`) | `"status":"ok"` — `{"tag":"struct","typeName":"Pair","fields":[…]}` |
| P2 | fixed-array return (`[4]uint64`) | `"status":"ok"` — `{"tag":"array","values":[10,11,12,13]}` |
| P3 | struct-of-arrays return (`{Pre,Post [4]uint64; N}`) | `"status":"ok"` — full nested contents observed |
| P7 | multi-return `([4]uint64, [4]uint64, uint64)` | `"status":"ok"` — all three values observed |
| P4 | string return + `+` concat | `"status":"ok"` — `{"tag":"string","bytes":[97,98]}` |
| P6 | manual decimal formatter (`string('0'+rune(d))`, concat loop) | `"status":"ok"` — `"[0 1 4 9]"` as bytes |
| P5 | **`fmt.Sprint(s)`** | **`"status":"unsupported"` — `"normalizing frontend-quarantined: selector call Sprint is not a method value"`** |
| P9 | slice return (`[]uint64`) | `"status":"ok"` but a HANDLE only: `{"tag":"slice","base":{"id":3,…},"len":3,…}` — contents NOT observed |
| — | **calls inside `\|\|`/`&&` operands** (first fib-S1 draft) | **`"status":"unsupported"` — `"normalizing frontend-quarantined: call/allocation in short-circuit operand (would change evaluation order)"`** |
| P11 | fork/join: `go func` workers + unbuffered-channel joins | `"status":"ok"`, value 14 — and the SAME observation under a perturbed `--choices 1,0,2,1,0` stream (schedule-invariant fold) |

Consequences:

- **S3 is fully feasible today**: struct, fixed-array, struct-of-array
  and multi-array returns all cross the boundary as observed pure
  values (P1/P2/P3/P7). No machine or frontend work needed.
- **S4 is mechanically feasible but not idiomatically**: string
  returns and concatenation work (P4/P6), but `fmt.Sprint` is
  frontend-quarantined (P5, fail-closed as designed) — the encoder must
  be hand-rolled harness Go (`formatU64s` below). A finding with an
  exact boundary, not a bug.
- **P9 confirms the value-fragment principle's boundary in the
  machine itself**: a returned slice is observed as a handle, never as
  contents — return-only observation genuinely cannot see through
  reference types, which is exactly the line the principle draws.
- **The short-circuit quarantine shapes S1 style**: verdict phases must
  hoist calls into locals before `&&`/`||` chains (the fixed fib-S1
  draft below). Cosmetic, but it is a real deviation from fully
  idiomatic test code; recorded as frontend-arc input.
- **Driver limitation (differential rows only)**: `native-json-run`
  accepts only `--arg-int`, so harness PARAMETERS must be integers for
  oracle rows today. Lean-side `runFunctionWithContextM` takes any
  `GoValue` arguments; the restriction binds the differential harness
  rows, not the theorems.
- **P11 grounds the capstone (§8)**: the fork/join shape is compilable
  Go that runs on the machine today, and the ∀ch quantifier does real
  scheduling work over it.

All proposed Lean statements below elaborate against the real machine
vocabulary (`.tmp/scoping/statements.lean`, exit 0; statements
parameterized over the harness `Func` — the lowerings exist and run,
they just have no checked-in Lean decode, which scoping does not need).

## §3 The matrix — 7 examples × 4 styles

Legend: **SHIPPED** = the current gallery entry is this style.
DEGEN = degenerates to another cell. Every non-DEGEN cell was drafted and
executed except the three marked "not drafted (same pattern)", which were
judged from an already-executed sibling cell rather than run; ✓go =
`go run` green, ✓m = machine run green.

| Example | S1 verdict | S2 value+family | S3 relational-value | S4 relational-string |
|---|---|---|---|---|
| fib | drafted ✓go ✓m — recurrence check; **under-determines** (§4.1) | **SHIPPED** (degenerate: no family) | DEGEN = S2 (args are already pure values) | DEGEN (scalar return; string adds nothing) |
| gcd | drafted ✓go ✓m — divides + trial maximality (O(min a b)) | **SHIPPED** (`Nat.gcd a b`, no family) | DEGEN = S2 | DEGEN |
| reverse | drafted ✓go ✓m — **copy-relational** check (better than shipped; §4.3) | SHIPPED variant (verdict against family formula) | drafted ✓go ✓m — `post = pre.reverse`, cap 8 | drafted ✓go ✓m — hand-rolled encoder |
| minmax | drafted ✓go ✓m — bounds + attained | **SHIPPED** (`minSpec (mmFamily n seed)`) | drafted ✓go ✓m — `lo = minSpec pre` | not drafted (same pattern as reverse-S4) |
| binsearch | drafted ✓go ✓m — search contract (hit ∧ first, or scan-miss) | **SHIPPED** (`findSpec (bsFamily n seed) t`) | drafted ✓go ✓m — `idx = findSpec pre t` | not drafted (same pattern) |
| isort | **SHIPPED** (sorted + permutation counts) | — (verdict is the shipped form) | drafted ✓go ✓m — `post = sortSpec pre` | drafted ✓go ✓m |
| wordcount | drafted ✓go ✓m — brute-force multiplicity vs subject | **SHIPPED** (`(n+2)/3` closed form) | drafted ✓go ✓m — `best = maxMultiplicity words` | not drafted (same pattern) |

Key structural observation: **for scalar-in/scalar-out subjects (fib,
gcd) the status quo already IS the direct relational statement** —
"value+family" without a family is just `returned = spec(args)`. The
"hack" feeling the brief names arises only for memory-input subjects,
where the family re-description (`mmFamily`, `bsFamily`) stands between
the reader and the property. That is precisely what S3 removes.

## §4 The drafts (Go verbatim from executed files + proposed Lean)

All Go below is verbatim from `.tmp/scoping/drafts/<cell>/main.go`
(subject functions elided here — they are the unchanged corpus
subjects; every file also carries a `main()` and was run). Lean
statements are verbatim from the elaborated scratch file, with
`H : Func` standing for the pinned harness lowering a real build would
substitute.

### §4.1 fib

**S1 (recurrence verdict)** — drafted to test the style's limit:

```go
func fib_harness_v(n uint64) uint64 {
	// calls hoisted out of || operands: the frontend quarantines
	// call/allocation inside short-circuit operands (probe finding).
	f0 := fib(0)
	f1 := fib(1)
	if f0 != 0 || f1 != 1 {
		return 0
	}
	fn := fib(n)
	fn1 := fib(n + 1)
	fn2 := fib(n + 2)
	if fn2 != fn+fn1 { // wrapping uint64 ==
		return 0
	}
	return 1
}
```

```lean
theorem s1_fib_shape … (n : Nat) (hn : n < 2 ^ 64 - 2) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel [] fns H #[.int (n : Int) .uint64] #[] ch
        = .ok { values := #[.int 1 .uint64] }
```

**Honest finding — the verdict channel UNDER-DETERMINES value
subjects.** The ∀n verdict family pins "the program's fib satisfies the
base cases and the recurrence at every n", but the VALUE `fib(n)` never
crosses the observation boundary, so no Lean corollary can equate it
with `fibSpec` — there is nothing in the statement to equate. To
recover the pointwise claim you need a value-returning observation
somewhere, i.e. S2. (The domain bound `n < 2^64 − 2` is also new and
artificial: `n+2` must not wrap for the recurrence check to be the
recurrence.) S1 is the wrong style for fib; recorded, not recommended.

**S2 (SHIPPED, = degenerate S3).** `fib_ok` / `fib_total` as in the
gallery. Direct: `returned = fibSpec n` names what fib is.

### §4.2 gcd

**S1 (property verdict)** — the one style where gcd's FULL specifying
property can live in Go:

```go
func gcd_harness_v(a, b uint64) uint64 {
	r := gcd(a, b)
	if a == 0 && b == 0 {
		if r == 0 {
			return 1
		}
		return 0
	}
	if r == 0 || a%r != 0 || b%r != 0 {
		return 0
	}
	for d := r + 1; d <= a && d <= b; d++ {
		if a%d == 0 && b%d == 0 {
			return 0
		}
	}
	return 1
}
```

Executes and runs green both sides — but the maximality trial loop is
O(min(a,b)): as TEST code it is honest, as the quantified subject it
means the proof walks a 2^64-iteration loop family (fuel bound ~2^64 —
provable with the measure rule, absurd to read), and the verdict still
does not export the VALUE `gcd(a,b)` (same under-determination as fib).
The shipped S2 `= Nat.gcd a b` says strictly more, in one line, over
the full domain. Not recommended.

**S2 (SHIPPED, = degenerate S3).** `gcd_ok` as in the gallery.

### §4.3 reverse

**S1 copy-relational (drafted — an IMPROVEMENT on the shipped
harness):**

```go
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

The shipped harness's test phase re-derives the family formula
(`s[i] != seed+(n-1-i)`) — the reader must re-check the setup algebra
to see what was tested. This draft saves a pre-copy and checks
`s[i] == t[n-1-i]`: the test phase states the reversal RELATION itself,
no formula, exactly the testing-mock ideal — and with a future
`// @ghost nondet` on the setup element it becomes ∀-data with the SAME
test phase (the family-formula version cannot: its check encodes the
family). Lean statement: identical shape to the shipped `reverse_ok`
(`= .ok #[1]`). Same proof technique, one extra O(n) copy loop of fuel.

**S3 (drafted, cap 8):**

```go
const capN = 8

func reverse_harness_r(n, seed uint64) ([capN]uint64, [capN]uint64) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i // @ghost nondet: verifier draws s[i] from the choice stream (∀-data)
	}
	var pre [capN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	reverse(s)
	var post [capN]uint64
	for i := uint64(0); i < n; i++ {
		post[i] = s[i]
	}
	return pre, post
}
```

```lean
theorem s3_reverse_shape … (n seed : Nat) (hn : n ≤ 8) (hs : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ pre post : List Int,
        pre.length = n ∧ post.length = n ∧
        runFunctionWithContextM fuel [] fns H
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64] #[] ch
          = .ok { values := #[goArr8 pre, goArr8 post] }
        ∧ post = pre.reverse
```

with the one new statement-vocabulary def (the whole S3 adapter):

```lean
def goArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map (fun v => .int v .uint64)⟩
```

DIRECTNESS: this is the style that states "reverse reverses" in Lean
on the harness's own returned data — `post = pre.reverse`, no family,
no heap. Honest contrivances, named: (i) the fixed cap — `n ≤ 8` is a
toy bound in the statement, and the harness carries copy loops plus
zero-padding semantics that exist only for observation (a real unit
test would not copy into `[8]uint64`); (ii) without the nondet
annotation the ∃`pre` is family-determined anyway — the statement
merely avoids SAYING so; genuine ∀-data arrives only with C1's
annotation. The bounded-shape trick is real but visibly a trick.

**S4 (drafted):**

```go
func reverse_harness_s(n, seed uint64) (string, string) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i
	}
	pre := formatU64s(s)
	reverse(s)
	post := formatU64s(s)
	return pre, post
}
```

(`formatU64s`/`formatU64`: 20 lines of hand-rolled decimal rendering —
required because `fmt.Sprint` is quarantined, P5.) Lean side:

```lean
def renderU64s (xs : List Nat) : String :=
  "[" ++ String.intercalate " " (xs.map toString) ++ "]"

theorem s4_reverse_shape … :
    … ∃ xs : List Nat, xs.length = n ∧
        … = .ok { values := #[goStr (renderU64s xs), goStr (renderU64s xs.reverse)] }
```

The Lean-side ugliness, honestly: the statement carries a **second
encoder** — `renderU64s` mirrors `formatU64s`, so the claim's meaning
routes through TWO renderings (Go's, walked by the proof; Lean's, read
by the reader) that must agree, plus `GoString.fromLeanString`'s UTF-8
byte model. Relating pre to post through strings needs encoder
injectivity lemmas the moment the post is anything but "render of a
transformed list". The only genuine win over S3 is unbounded length.

### §4.4 minmax

**S1 (drafted):** test phase checks `lo ≤ s[i] ≤ hi` for all i and
both bounds attained; `return ok`. ✓go ✓m. Natural test code; verdict
does not export the values (fib's finding, milder — min/max are
FULLY pinned by bounds+attained, so here the verdict family actually
does determine the subject pointwise; the Lean reader just cannot see
the values, only that the Go check passed).

**S2 (SHIPPED).** `minmax_ok`: returned pair `= minSpec/maxSpec
(mmFamily n seed)` — the family re-description the brief names.

**S3 (drafted, cap 8):**

```go
func minmax_harness_r(n, seed uint64) ([capN]uint64, uint64, uint64) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i
	}
	var pre [capN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	lo, hi := minMax(s)
	return pre, lo, hi
}
```

```lean
theorem s3_minmax_shape … (h1 : 1 ≤ n) (hn : n ≤ 8) … :
    … ∃ pre : List Int, pre.length = n ∧
        … = .ok { values := #[goArr8 pre,
                              .int (minSpec pre) .uint64,
                              .int (maxSpec pre) .uint64] }
```

`lo = minSpec pre` ON THE RETURNED DATA — direct, family-free. The
returned-pre pattern (input echoed back as a value) is the S3 idiom for
read-only subjects; less contrived than reverse's double array since
only one copy loop exists.

### §4.5 binsearch

**S1 (drafted):** the search CONTRACT in Go — nonnegative index hits
the target and is the first hit; `-1` confirmed by linear scan. ✓go ✓m
(including the `uint64(idx)` int→uint64 conversion). Natural test code;
note it verifies the contract but never exports `idx`.

**S2 (SHIPPED).** `search_ok`: `= findSpec (bsFamily n seed) t`.

**S3 (drafted, cap 8):**

```go
func search_harness_r(n, seed, t uint64) ([capN]uint64, int) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + 2*i
	}
	var pre [capN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	idx := search(s, t)
	return pre, idx
}
```

```lean
theorem s3_binsearch_shape … (hn : n ≤ 8) (hw : seed + 2 * n < 2 ^ 64) … :
    … ∃ pre : List Int, pre.length = n ∧
        … = .ok { values := #[goArr8 pre, .int (findSpec pre t) .int] }
```

**This is the brief's own test case, answered:** `idx = findSpec pre t`
states in Lean what binsearch IS — the index of the first occurrence of
`t` in the (returned) array it searched. The sortedness PRECONDITION is
the remaining wart: it still lives in the setup family (nothing in the
statement says `pre` is sorted; the claim is true because the family
is). An honest S3 binsearch wants `pre.Sorted → idx = findSpec pre t`
with ∀-data — which needs the choice-input annotation plus a
constructive sorted setup (see §5).

### §4.6 isort

**S1 (SHIPPED).** The gallery's sorted+permutation verdict — the
strongest existing S1 exhibit; kept as the canonical unbounded form.

**S3 (drafted, cap 8):**

```go
func isort_harness_r(n, seed uint64) ([capN]uint64, [capN]uint64) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed * (i + 1)
	}
	var pre [capN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	insertionSort(s)
	var post [capN]uint64
	for i := uint64(0); i < n; i++ {
		post[i] = s[i]
	}
	return pre, post
}
```

```lean
theorem s3_isort_shape … (hn : n ≤ 8) … :
    … ∃ pre : List Int, pre.length = n ∧
        … = .ok { values := #[goArr8 pre, goArr8 (sortSpec pre)] }
```

`post = sortSpec pre` — "insertion sort sorts" in mathematics, on
returned values, replacing the O(n²) Go permutation check with the
already-proven `sortSpec_sorted`/`sortSpec_count` lemma layer. The
quadratic-fuel verdict phase disappears from the harness. Bounded cap
remains the price.

**S4 (drafted).** Same shape as reverse-S4 (`formatU64s` pre/post);
✓go ✓m. Post: `postStr = render (sortSpec xs)`. Same double-encoder
tax; unbounded n is the only win.

### §4.7 wordcount

**S1 (drafted):** brute-force O(n²) multiplicity recomputation vs the
subject; classic differential mock. ✓go ✓m. Note the ∀ch order-
independence teaching point becomes INVISIBLE in S1 — the verdict
compares two Go numbers; the reader no longer sees that the spec had to
be order-independent.

**S2 (SHIPPED).** `wordcount_ok`: `= (n+2)/3` closed form.

**S3 (drafted, cap 8):**

```go
func wordcount_harness_r(n, seed uint64) ([capN]uint64, uint64) {
	w := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		w[i] = seed + i%3
	}
	var words [capN]uint64
	for i := uint64(0); i < n; i++ {
		words[i] = w[i]
	}
	best := maxCount(w)
	return words, best
}
```

```lean
theorem s3_wordcount_shape … (hn : n ≤ 8) … :
    … ∃ words : List Int, words.length = n ∧
        … = .ok { values := #[goArr8 words,
                              .int ((maxMultiplicity words : Nat) : Int) .uint64] }
```

`best = maxMultiplicity words` on returned data — MORE direct than the
shipped closed form (which states the family's answer, `(n+2)/3`, not
the subject's property). The ∀ch/order-independence story survives
intact (unlike S1). Strong S3 candidate.

## §5 Choice-input (nondet) variants — expressibility notes per example

Per C1 these are annotation-form sketches (`// @ghost nondet` on a
setup assignment; executes at the written concrete value = one
witnessed member; the verifier ∀-quantifies via the choice stream).
DIFFERENTIAL OBLIGATION carried from §11's ruling: the pick needs a
go-run counterpart so the oracle can witness picked inputs.

- **fib, gcd** — no change: the inputs are already ∀-quantified
  arguments; the annotation adds nothing.
- **reverse, isort, wordcount** — the big win: annotating the one
  setup assignment (`s[i] = … // @ghost nondet`) turns EVERY style's
  scalar family into genuine ∀-data with the same harness text.
  S1-copy-relational + nondet ≈ the framed ∀-data companions at
  return-observation strength; S3 + nondet = full relational ∀-data
  (`post = pre.reverse` over ALL inputs), subsuming the family
  honesty-caveats in the gallery today.
- **minmax** — same as reverse; additionally kills the family's
  wrap-order caveat text.
- **binsearch** — the interesting case: raw nondet elements BREAK the
  sortedness precondition. Expressible without new annotation
  vocabulary by CONSTRUCTIVE setup: draw nondet GAPS and prefix-sum
  them (`s[i] = s[i-1] + g` with `g // @ghost nondet`), so every pick
  yields a sorted array and the theorem covers all sorted arrays (with
  a no-overflow side condition). Preconditions-as-constructive-setup is
  the pattern; record it as the alternative to a richer
  assumption-annotation (`// @assume sorted(s)`), which would be new
  vocabulary and a worse testing-mock fit.
- **wordcount** — nondet words make `maxMultiplicity` the only
  statable spec (closed form gone), which is the honest general claim.

Annotation-vocabulary axis summary: **one marker (`@ghost nondet`)
covers every example in every style**; binsearch avoids a second marker
via constructive setup. No style requires style-specific annotations —
S1/S2/S3 all score equally minimal; S4 needs none either but gains
nothing from them.

## §6 The value-fragment principle, assessed

**It holds, and the machine already enforces its boundary.** Scalars,
structs, fixed-size arrays (nested in structs, in multi-returns) and
strings all cross the return boundary as fully-observed pure values
(P1–P7); slices come back as handles with invisible contents (P9) and
maps/channels likewise (per the observation schema) — so "reference
types get setup/test treatment" is not a convention we impose but what
return-only observation can actually see. Nothing in the seven examples
needed heap readback: every property fit through returned values in at
least two styles.

**Where unbounded data strains it.** The pass-by-value fragment carries
unbounded data only as (i) a Go-side FOLD of it (S1 verdicts, the
shipped unbounded forms — data itself never crosses), (ii) a
FIXED-CAP array (S3 — direct but bounded), or (iii) a STRING encoding
(S4 — unbounded and direct but double-encoder-taxed). The examples that
pull hardest are the pre/post relational ones (reverse, isort); the
pre+scalar ones (minmax, binsearch, wordcount) sit comfortably in
S3-bounded; fib/gcd never leave scalars.

**Decoder vs emit-trace, weighed for the escape hatch:** a Lean-side
string DECODER (parse the returned string back to a list) puts a parser
in the statement TCB — strictly worse than S4's encoder (parsers are
bigger and partial). An EMIT-TRACE channel (the machine records an
output stream of values as part of `Result`) would give unbounded
value-typed observation without encoders — but it is a machine
extension (new observation surface + differential story), out of scope
here. **Neither is needed for this corpus**: the C1 choice-input
annotation upgrades the existing scalar-family harnesses to ∀-data
without changing the interface, and boundedness then remains only where
S3's direct statement form is wanted verbatim. Recorded as the ranking:
annotation route ≫ emit-trace ≫ string decoder.

## §7 Proof-cost and adapter-thinness forecast

| Style | Proof cost (this arc's techniques) | Adapter thinness (C2) |
|---|---|---|
| S1 | KNOWN — shipped isort/reverse ARE verdict proofs; cost = more Go to walk (isort's O(n²) check ⇒ quadratic fuel bound; gcd-S1's trial loop ⇒ ~2^64 fuel, prohibitive to state). Segment/measure kit unchanged. | THINNEST — statement layer only; zero new defs. |
| S2 | KNOWN — status quo, all seven proven. | THIN — spec/family fns, statement-side only. |
| S3 | MODERATE, no new machinery CLASS — array-typed locals and copy loops walk with the same `with_unfolding_all rfl` segments; returned-array pinning is the existing SliceMem-style executable-fact class on array cells; ∃pre/∃post witnessed by the canonical run. With `@ghost nondet`: inputs become ch-drawn ⇒ symbolic-content segments (the §10c class, priced there; the wordcount range-loop induction is the template). | THIN — one statement def (`goArr8`); the array facts below are style-neutral (serve any style). |
| S4 | HIGHEST — needs a GoString-concat executable-fact family ("StringMem" analog, new) for O(n) growing-string loops, plus encoder-agreement/injectivity pure lemmas; the Lean encoder enters the statement TCB. | THICKEST — encoder model is style-specific statement vocabulary; string facts below are new. |

Evidence for C2's rule as stated: both restatement pivots this arc
reused the canonical-run segments, measures, and entry glue unchanged
(~95% by module content; only statement shells and readout glue
changed). S1↔S2↔S3 restatements of the same example would sit on the
same core; S4 alone demands a new below-statement fact family.

## §8 North-star capstone — the raft harness (assessment only)

The user's sketch (2026-08-14; reconstructed to the agreed schema):

```
fn raft_harness(num_threads) {ghost_choices} {
  for i in 1..num_threads { fork(i, ...) }
  for i in 1..num_threads { ret[i] = join(i) }
  assert_consensus(ret)  // or return and assert in a postcondition
}
```

(a) **The shape is compilable Go today** — P11's fork/join probe
(`go func` workers + channel joins, schedule-invariant fold) runs green
through the machine, same observation under a perturbed choice stream.
Ghost choices are C1 annotations; `consensus(ret)` over returned values
is exactly the relational-directness ideal at the north star:
S3's form (`return ret; Lean post: Agreement ret`) and S1's form
(`assert_consensus` folding to a verdict in Go) are BOTH expressible,
and the styles scoped here transfer — join results are scalars/structs,
inside the value fragment.

(b) **THE SAFETY/LIVENESS SPLIT — form-level finding, flagged.** The
gallery's ∃N-∀fuel-∀ch idiom is a LIVENESS claim (every choice stream
completes past one bound). Raft under an adversarial choice envelope
CANNOT satisfy it — election livelock is a real infinite behavior (the
FLP tension); an adversarial `ch` starves progress forever. So the raft
family splits:

- **SAFETY form (first target)**: completion CONDITIONED, not claimed —
  every completed run agrees. Elaborated against the machine
  (`.tmp/scoping/statements.lean`, `capstone_safety_shape`):

  ```lean
  ∀ (fuel : Nat) (ch : Choices) (r : Result),
    runFunctionWithContextM fuel [] fns H #[.int (nt : Int) .uint64] #[] ch
      = .ok r →
    Agreement r
  ```

  This matches the Verdi agreement-translation target. **Every style
  expresses it cleanly** — the conditioned form is exactly the existing
  run-conditioned readout twins (`*_readout`, already shipped and
  bridged), with the ∃N clause deleted rather than derived. S3 states
  `Agreement` on returned data (the ideal); S1 folds it in Go and
  conditions `= .ok #[1]`; no style is disadvantaged, so the
  conditioned-safety axis does not separate the candidates.
- **LIVENESS form (later)**: needs a `Fair : Choices → Prop` predicate
  as designed spec vocabulary (`∀ ch, Fair ch → ∃ N, …`) — new
  statement-TCB vocabulary with a real fidelity argument (what
  fairness Go's scheduler promises); a named future design, not
  sketched further here.

(c) **Open**: quantified `num_threads` vs fixed small clusters (3/5)
first. Fixed-3/5 gives concrete fork/join segment proofs on the
existing kit; quantified nt needs induction over spawned-pool size —
new but shaped like the measure rule. Lean toward fixed-first.

No raft drafting beyond this assessment (per the addendum's scope).

## §9 Per-example recommendations

One shipped harness per example stays the rule (gallery surface cost).
Recommendations, for the user's decision:

- **fib** — KEEP S2 (it is already the direct statement; no family
  exists). S1 recorded as under-determining.
- **gcd** — KEEP S2 (`Nat.gcd`, full domain, one line). S1's
  self-contained check is honest test code but proof-absurd (2^64-step
  verdict loop) and weaker.
- **reverse** — ADOPT the S1 **copy-relational** harness (§4.3) in
  place of the shipped family-formula verdict: same statement shape and
  proof technique, strictly more testing-mock (the check is the
  relation, not the setup algebra), and it is nondet-annotation-ready.
  S3 is the direct-statement upgrade; recommend it WITH the annotation
  (∀-data), not before (a bare `n ≤ 8` gallery entry reads as a toy).
- **minmax** — S3 now (returned-pre + `minSpec pre` equations; the cap
  is the only cost and minmax's harness is the least contrived S3);
  or hold with S2 until the annotation lands. Mild preference: S3.
- **binsearch** — the brief's target: S3 states `idx = findSpec pre t`
  directly. Recommend S3 WITH the constructive-sorted nondet setup
  (§5) so the precondition is honest; until the annotation exists,
  S2 remains the honest form (S3-bounded adds directness but keeps the
  family doing the sorting silently).
- **isort** — KEEP shipped S1 as the unbounded headline (the
  permutation check is the genre classic and reads perfectly); add S3
  (`post = sortSpec pre`) as the direct-math companion when the
  annotation lands, which also retires the O(n²) verdict fuel bound
  from the headline.
- **wordcount** — S3 (`best = maxMultiplicity words`) is strictly more
  direct than the shipped closed form and keeps the ∀ch teaching point;
  adopt at the next restatement window.

Cross-cutting: S4 NOT recommended anywhere — its only advantage
(unbounded data) is delivered better by the choice-input annotation,
and it alone thickens the below-statement layer (C2) and doubles the
encoder surface. Record it as the explored-and-rejected branch.

## §10 Open decisions for the user

**RULING (user, 2026-08-14, resolving decisions 1–2 — recorded
near-verbatim):** *"we don't introduce ghosts at all now, everything is
real Go. We might in future need them in harnesses, but now we don't."*
So: NO annotation vocabulary this arc — decision 1 is DEFERRED (the
choice-input marker is a designed future rung, not the next build
item), decision 2 is moot until then. The GHOST LADDER, recorded as the
standing design (cheapest rung first, each adopted only when a claim
needs it):
  rung 0 — REAL GO (current position): history ghosts as ordinary
    harness code (the copy-relational pre-copy), input families as
    ordinary setup loops; no annotations anywhere.
  rung 1 — `// @ghost nondet` (designed, §11 of the form note): binds a
    site to the existing ∀ch; executable run = one witness stream (the
    two-bounds coherence); carries the differential-counterpart
    obligation and the choice-indexing alignment detail.
  rung 2 — shadow signatures (Gobra/CN style, designed only): ghost
    data crossing the SUBJECT boundary; fail-closed erasure check at
    the NativeToIR quarantine. The "no free lunch" horizon lives here.
Consequence for decision 3: feasible-now swaps are exactly the real-Go
ones (reverse copy-relational; minmax/wordcount S3 at today's return
boundary); binsearch's `findSpec pre t` form WAITS at rung 1.

1. **Adopt the choice-input annotation as the next build item?** It is
   the single mechanism that converts the S3 drafts from
   bounded-cap curiosities into the direct ∀-data form, upgrades S1
   harnesses to ∀-data, and carries the differential-counterpart
   obligation (§11's recorded design). Everything in §9's "with the
   annotation" hinges on it.
2. **Annotation surface**: is `// @ghost nondet` (one marker +
   constructive setup for preconditions) the v1 vocabulary, or is an
   assumption marker (`// @assume …`) wanted despite the worse
   testing-mock fit? (Scoping's evidence: one marker suffices for all
   seven.)
3. **Per-example adoptions** (§9): reverse copy-relational swap now?
   minmax/wordcount S3 now or with the annotation? binsearch waits.
4. **Fixed-cap S3 in the gallery before the annotation** — acceptable
   (`n ≤ 8` stated plainly) or hold?
5. **Capstone**: confirm the safety-first split (conditioned Agreement
   form as the raft target; `Fair` deferred) and fixed-3/5 clusters
   before quantified `num_threads`.
   **RULED (user, 2026-08-14): safety-first confirmed, no fairness for
   now — "but we want to make decisions that don't preclude it later."
   Non-preclusion, concretely: (a) the safety form stays stated over
   the SAME ∀ch streams a future `Fair : Choices → Prop` would
   restrict, so the liveness upgrade is `∀ch, Fair ch → …` — a
   strengthened hypothesis on the existing quantifier, never a new
   statement language; (b) REQUIREMENT ON THE CONCURRENCY RE-ENVELOPE
   ARC (recorded here as a design input): when the `Choices`
   representation is reshaped for the widened envelope, it must retain
   enough structure to DEFINE fairness — scheduling picks identifiable
   as such, and the schedulable-set at each pick recoverable (a
   fairness predicate must be able to say "every continuously
   schedulable goroutine is eventually picked"). A stream of bare
   naturals with no site structure would preclude this; do not flatten.
6. **Frontend-arc inputs recorded here**: the short-circuit
   call-hoisting quarantine (S1 ergonomics), `fmt.Sprint` support
   (would make S4/debug harnesses idiomatic), non-integer `--arg-int`
   driver extension (string/struct harness params for oracle rows).

## §11 Scratch inventory (not tracked)

`.tmp/scoping/probes/` — p1-struct, p2-array, p3-structarr, p4-string,
p5-sprint, p6-strbuild, p7-multiarr, p9-slice, p11-forkjoin.
`.tmp/scoping/drafts/` — {fib,gcd,reverse,minmax,binsearch,wordcount}-s1,
{reverse,minmax,binsearch,isort,wordcount}-s3, {reverse,isort}-s4 —
each with `main.go` (runnable), emitted `wire.json`, machine-run green
except where a finding says otherwise. `.tmp/scoping/statements.lean` —
all proposed statements + capstone safety shape, elaborated exit 0
(`sorry` proofs only; nothing here is committed).
