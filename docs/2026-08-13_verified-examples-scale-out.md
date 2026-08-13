# Verified-examples scale-out (slice 2c) — session record (2026-08-13)

**HOLD RESOLVED (2026-08-13): THE HARNESS RULING** — final form ruled
by the user; full record in the form note §11 (charter cross-marked).
Consequences executed in order: (i) records (this banner, §11, charter);
(ii) three-phase harness functions added to every example's corpus
program with harness-shaped oracle rows + re-pin; (iii) the shared
entry-layer glue (`runConfig` fold/terminal lemmas) + the fib
restatement as exemplar; (iv) per-example restatements over
`runFunctionWithContextM` (old cell-readback headline shells deleted
at each restatement; framed theorems + sliceCells/frame vocabulary
KEPT as the proof-side supporting layer per the ruling); (v) gallery
drafts re-rendered harness-style. Ledger below updated per example as
restatements land.

The original hold banner, kept for the record:

**FORM HOLD (2026-08-13, mid-slice — operator direction)**: a
harness-only alternative headline form (closed specs: inputs as
harness parameters, harness-allocated memory, canonical seed) is under
active discussion with the user, vs the committed memory-quantified
form. Ruling pending. Consequences recorded honestly: gcd / minmax /
isort / binsearch were ALREADY COMMITTED in the memory-quantified form
before the hold arrived — their statement layers are THIN (a
canonical-run private theorem carries ~all of each proof; the framed
headline is a frame-theorem corollary; the readout twin is derived),
so a harness-only ruling re-derives new headlines over the SAME
segments without re-proving anything. The §5 gallery drafts below are
DRAFTS, form-contingent, not gallery finalizations. Word-count's
statement layer is held in-flight (worker instructed: deliver the
form-independent machinery + canonical-run theorem; hold the framed
headline). Audit registrations already landed for the four committed
examples stand as records of what was proven; re-registration follows
the ruling if the form changes.

Status: IN PROGRESS (updated as examples land). Charter:
`docs/2026-08-12_verified-examples-arc-charter.md` (slice 2 → 2c after
the 2a/2b split); form of record:
`docs/2026-08-12_example-spec-form.md` §9 (memory-quantified headlines)
and §10 (the map form, designed this session before proving). Lane
`foundation`, branch `foundation-s1`.

## §1 The slice's shape

Five examples over the two established exemplars (fib = argument-input,
reverse = memory-input): gcd, min/max-of-a-slice, binary search,
insertion sort, map word-count. Per example: canonical corpus Go +
oracle rows (landed FIRST, guardrails-first — infra commit `0d911df8`,
38 rows, full-differential re-pin in-session), pinned lowering
(check-golden, both links), headline in the settled memory-quantified
∃N-total form + D1 run-conditioned twin, Audit registration with axiom
pins, gallery entry draft (§5 below / worker reports).

Delegation (recorded): gcd built by the lead (the argument-input
template instance); minmax / binsearch / isort / wordcount executed by
Fable workers from lead-written designs (Fable per the standing
worker-model policy for proof slices; the arc instruction's Opus
allowance for replication was not exercised — proof-slice risk
dominates the cost saving). Conceptual design stayed with the lead: the
map form (§10 of the form note), the isort nested-induction design, the
binsearch invariant/spec design, the minmax total-heap-preservation
form — all specified in the worker briefs verbatim.

## §2 Standing decisions made this slice (recorded here, not in chat)

1. **The D1 twin for direct-route examples is DERIVED, not re-proven**:
   `GoLean.Surface.normal_readout_of_total` (FuelMeasure) — a total
   ∃N-completes-and-verdict headline already determines every normal
   completion (`execStmt` is a function of `(fuel, ch)`; success is
   fuel-monotone with the same result), so each example ships
   `<x>_readout` in ~3 lines. This realizes D1-BOTH on the sequential
   carrier. C-carrier (`GoSpecC`) twins are NOT shipped for the
   scale-out examples — matching the reverse exemplar's precedent (the
   direct route has no `GoSpec` to transfer); recorded as a
   merge-window curation question, not silent.
2. **`Sorted` is shared spec vocabulary** (`GoLean.SliceMem.Sorted`,
   one first-order definition) — binary search's precondition and
   insertion sort's postcondition mean ONE thing in the gallery.
3. **gcd's arithmetic treatment**: fib's bounded-exact/full-wrapped
   theorem PAIR collapses — `a % b` and `Nat.gcd` cannot wrap — so gcd
   ships one full-domain EXACT framed headline. FD-E3 honesty here is
   the recorded observation that no wrap exists to state.
4. **Harness arg-width limit (recorded)**: the go-harness parses case
   args as int64, so oracle rows witness inputs only up to `2^63 − 1`;
   the upper half of the uint64 domain is covered symbolically by the
   theorems, not by rows. (Same limit already implicit in reverse's
   rows.)
5. **The map form** is §10 of the form note (designed before proving,
   per the arc instruction): `mapCells`/`mapVal` vocabulary, the
   order-independence discipline (an order-dependent spec is
   UNPROVABLE against the enveloped iteration — by design), the
   choice-pick induction shape, and the priced symbolic-address
   obstruction in range-loop segments.

## §3 Per-example ledger (updated as they land)

| example | headline | route | status |
|---|---|---|---|
| gcd | **HARNESS-RESTATED**: `gcd_ok` over `runFunctionWithContextM` (gcd_harness, returned data = `Nat.gcd a b`, full uint64²); memory forms kept as `gcd_framed`/`gcd_framed_readout` | segments + b-value induction ported to the harness layout; entry equation + runConfig glue | **RESTATED + COMMITTED**, classical trio, fuel `91 + 45·b` |
| min/max | **HARNESS-RESTATED**: `minmax_ok` over `runFunctionWithContextM` (minmax_harness, setup family `s[i] = seed + i`, returned pair = `minSpec/maxSpec (mmFamily n seed)`; input-family honesty recorded); memory forms kept as `minmax_framed`/`minmax_framed_readout` | setup-loop invariant over make-replicate backing + ported induction | **RESTATED + COMMITTED**, classical trio |
| binary search | `search_ok` — sorted precondition (`SliceMem.Sorted`), `findSpec` first-occurrence-or-−1, **domain `len < 2^62`: the Bloch mid-overflow bug carried as the honest domain bound (the teaching point)**; landed character-for-character as designed | reverse's route; strong induction on `hi − lo` (strict decrease both branches); post-loop `&&` walked lazily (the `lo = len` exit provably never reads `s[lo]`); per-iteration `mid` allocation handled by a garbage-suffix freshness invariant | **PROVEN + COMMITTED**, axioms classical trio, fuel `123 + 75·len` |
| insertion sort | `isort_ok` — memory-input read-write, `sortSpec` + `sortSpec_sorted`/`sortSpec_count`/`sortSpec_length` corollaries ("sorted permutation" said honestly); statement landed as designed (only the pre-recorded `hlen` delta) | direct segments; **nested-loop composition = plain nested strong inductions — no measure-rule variant needed** (the sugar gap is WP-route-only); PLUS the finding-8 in-run frame-rebase composition | **PROVEN + COMMITTED**, axioms classical trio (pure corollaries `[propext, Quot.sound]`), fuel `76 + (92·len + 160)·len` (quadratic, explicit) |
| word-count | `wordcount_ok` — map build + enveloped range; spec `maxMultiplicity`, order-independent BY NECESSITY (the ∀-choices quantifier does real work — the teaching point) | §10 design: counting-loop assoc-list invariant + choice-pick induction; symbolic-address glue per §10c | worker in flight; §10d fallback = named foundation debt |

## §4 Findings so far

1. (gcd) The §5c sketch held exactly: the ≤-decrease shape absorbed the
   non-unit `a % b < b` decrease via plain strong induction; the only
   new executable fact was the emod one it predicted. The direct route
   again carried value + completion from one induction (reverse's
   lesson confirmed on an argument-input example).
2. (form) Total headlines make run-conditioned D1 twins free (§2.1) —
   the earlier per-example second walk (fib's `fib_wraps` route) is
   unnecessary wherever the ∃N headline exists.
3. (harness) §2.4 int64 arg-width limit.
4. (binsearch, by design) The honest domain bound for the textbook
   `(lo+hi)/2` implementation is `len < 2^62`, not `2^63`: `lo + hi`
   is computed in Go int and wraps at `2^63` — the classic "nearly all
   binary searches are broken" bug surfaces as a DOMAIN CONDITION in
   the theorem. Pending worker confirmation of the exact boundary.
5. (minmax route notes, from the build) (a) `len(s)` sits inside the
   for-condition, so EVERY iteration pays a conditioned
   `applyStrictOp_len_slice` step (reverse computed its bound once at
   entry); (b) Go's lowering re-evaluates `s[i]` afresh in a taken
   branch's RHS — up to 5 conditioned indexGet steps per iteration;
   (c) results double-normalize at exit (`$res` store + frame-exit
   store), cleaned by two `unorm_of_range` rewrites; (d) the machine's
   `>` transcribes as flipped `decide (· < ·)` — no greaterCmp fact
   needed.
6. **Shared-kit promotion candidates (flagged, not moved)**:
   `stepFnIter_one` + `stepFn_strict_apply` now have THREE private
   copies (Reverse, Gcd, MinMax) — promote to the FuelMeasure kit at
   the next shared-file window; `applyStrictOp_lessCmp_int`,
   `getElem?_mapU`, `getD_mem`, `locSup_mapU` likewise (second/third
   copies). Held out of this slice's commits to keep worker-parallel
   file ownership disjoint; recorded so the audit sees the
   duplication as deliberate.
7. **Gate mechanics while workers are in flight (recorded)**:
   `scripts/ci`'s proofs-file audit-coverage step enumerates ALL
   on-disk `proofs/**/*.lean`, so a sibling worker's in-progress module
   keeps the FULL gate red until integrated. Per-example integration
   commits are therefore validated by the capped proofs build (the
   in-build Audit axiom/non-vacuity gate) + escape-hatch scan of the
   committed files; the full `scripts/ci` (and `--diff` standing) is
   re-established at the slice tip. No gate is weakened — the coverage
   step's complaint is precisely "file exists but not yet in the
   audited closure", which integration resolves in order.
8. **(isort — the slice's principal nested-loop finding)** The machine
   RE-ALLOCATES the inner loop's `j`/`$forFirst` cells on every outer
   pass (the inner `for`'s declarations re-enter their block;
   `nextAddr` grows by 2 per pass, dead cells accumulate) — so
   reverse-style fixed-address segments cannot describe the outer head
   at one placement. Resolution (machine-forced, recorded in the
   module): each pass is proven ONCE at a tight 6-cell canonical
   placement and transferred through the executable frame theorem at
   the accumulated-garbage shift, with the retired cell pair REBASED
   into the frame between passes — i.e. the frame theorem is
   load-bearing INSIDE the canonical run (garbage cells are frames),
   then consumed a second time at the input-relocating renaming for
   the ∀-placement headline. Nothing is re-run at any framed
   placement. This is a new consumption pattern for the frame theorem
   (beyond §9c's original transfer role); a generalized
   "retire-prefix-into-frame" Frame/ lemma is a recorded growth point
   if a third nested-allocation example appears.
9. **(isort/binsearch) Short-circuit `&&` machine shape**: `Expr.and`
   pushes an `andK` continuation; a false left conjunct short-circuits
   in ONE step to the if-continuation — at `j = 0` the machine
   provably never reads `s[j-1]` (the `isort_andFalse_raw` one-step
   segment IS that fact). The laziness is load-bearing and now
   exhibited in a theorem, not just oracle rows.
10. **(binsearch) The 2^62 boundary, verified while proving**: the
    midpoint is computed only under `lo < hi`, so `lo + hi ≤ 2·len−1`
    and the first UNSAFE length is `2^62 + 1` (`len = 2^62` itself
    still safe); the stated `< 2^62` is the clean power-of-two bound
    one step inside. One lemma (`mid_clean`) consumes it. The
    element-range hypothesis `hxs` turned out UNCONSUMED by the proof
    (the machine's `<`/`==` are kind-agnostic and the program never
    writes the array) — kept in the statement as the honest
    uint64-domain restriction, recorded in-module.
11. **(binsearch — a second per-iteration-allocation resolution)**
    Unlike isort's frame-rebase, binsearch handles its per-iteration
    `mid :=` allocation by carrying an ABSTRACT GARBAGE SUFFIX in the
    loop-state family with a freshness invariant (∀ a ≥ na, the
    suffix owns no ⟨a⟩) — no frame-theorem consumption inside the
    canonical run. Two working patterns for the same machine behavior
    are now on record (suffix-invariant vs rebase-into-frame); which
    generalizes better is a cleanup-arc question. Related: `seqCont`'s
    environment DecidableEq (`if env' = env`) BLOCKS definitional
    evaluation whenever the env carries a symbolic address — the
    module's `stepFn_seqn_splice` (an `if_pos rfl` discharge) is the
    reusable fix and a strong shared-kit candidate.
12. **(wordcount, from the paused worker's state report — the owed
    ledger note)** Phase C (the counting loop) ALSO allocates two
    fresh cells per iteration (`$c1`/`$c2` composite-literal temps),
    so BOTH halves of wordcount sit in the symbolic-address regime —
    §10c's assumption that only the range half pays the α-route cost
    was wrong by half. The worker's delivered machinery (map
    executable facts, countsList invariant, counting-loop induction at
    fuel `84n+23`, choice-pick glue incl. `stepFn_pick`) is
    form-independent and survives the harness restatement; its
    remaining gap at the stop order was one goal in the §10b range
    induction + the exit segments.
    (further findings appended as workers report)

## §5 Gallery entry drafts

### gcd — Euclid's algorithm over uint64

```go
func gcd(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}
```

**Claim.** For every `a` and `b` in the full `uint64` domain — no
bound, no wrap: gcd's arithmetic cannot overflow — and with anything
else in memory: `gcd(a, b)` completes normally (no panic, no error,
no non-termination: with enough fuel, under every nondeterminism
choice), returns exactly `gcd(a, b)` — Lean's `Nat.gcd`, the textbook
function — and touches nothing but its result cell. Every quantifier
is discharged symbolically.

**The theorems** (`proofs/GoLeanProofs/Examples/Gcd.lean`):

```lean
theorem gcd_ok (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (fr : Heap) (na : Nat)
    (hfr : Heap.lookup fr (.base ⟨0⟩) = none)
    (hwf : MachineWf
      { functions := gcdLowered.funcs,
        heap := (.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩) :: fr,
        nextAddr := na }
      (.exec (gcdCall a b) gcdEnv .stop)) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel gcdEnv (gcdSeedFr fr na) ch (gcdCall a b)
          = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩)
            = .ok (.int ((Nat.gcd a b : Nat) : Int) .uint64)
        ∧ ∀ (addr : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨addr⟩) = some c →
            Heap.lookup σf.heap (.base ⟨addr⟩) = some c
```

(`gcd_readout` beneath it: any normal completion, at any fuel and any
choice stream, delivers the same — the run-conditioned reading.)

**Axioms:** `[propext, Classical.choice, Quot.sound]` (Lean's classical
trio; no `sorry`, no native evaluation, no extra axioms).

**Ground:** the program in the theorem is the toolchain's pinned
lowering of the Go source above (staleness-guarded by
`scripts/check-golden`); the same source is differentially tested
against `go run` (`Corpus/coverage/exec/examples/gcd/`, 7 rows incl.
`gcd(0,0) = 0`, one-sided zeros, coprime, and the int64-boundary
pair).

### minmax — min and max of a slice

```go
func minMax(s []uint64) (uint64, uint64) {
	lo, hi := s[0], s[0]
	for i := 1; i < len(s); i++ {
		if s[i] < lo { lo = s[i] }
		if s[i] > hi { hi = s[i] }
	}
	return lo, hi
}
```

**Claim.** For any nonempty list `xs` of uint64 values, wherever it
lives in memory, with anything else present: `minMax(s)` completes
normally (no panic, no error, no non-termination: with enough fuel,
under every nondeterminism choice), the result cells then hold exactly
the minimum and maximum of `xs`, the slice itself is unchanged — the
program is read-only on its input — and no other memory is touched.
On the empty slice Go panics at `s[0]`; the theorem excludes it
honestly (`xs ≠ []`), and the corpus pins the panic against `go run`.
Every quantifier is discharged symbolically.

**The theorems** (`proofs/GoLeanProofs/Examples/MinMax.lean`):

```lean
def minSpec : List Int → Int
  | [] => 0
  | [v] => v
  | v :: w :: rest => min v (minSpec (w :: rest))

def maxSpec : List Int → Int
  | [] => 0
  | [v] => v
  | v :: w :: rest => max v (maxSpec (w :: rest))

theorem minmax_ok (xs : List Int) (hne : xs ≠ [])
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63)
    (base : Nat) (hb0 : base ≠ 0) (hb1 : base ≠ 1)
    (fr : Heap) (na : Nat)
    (hfb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hf0 : Heap.lookup fr (.base ⟨0⟩) = none)
    (hf1 : Heap.lookup fr (.base ⟨1⟩) = none)
    (hwf : MachineWf
      { functions := minMaxLowered.funcs,
        heap := resCells ++ sliceCells xs base ++ fr, nextAddr := na }
      (.exec (minMaxCall xs base) minMaxEnv .stop)) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel minMaxEnv (minMaxSeed xs base fr na) ch
            (minMaxCall xs base)
          = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int (minSpec xs) .uint64)
        ∧ loadLoc σf (.base ⟨1⟩) = .ok (.int (maxSpec xs) .uint64)
        ∧ Heap.lookup σf.heap (.base ⟨base⟩)
            = some ⟨some (.array xs.length (.int .uint64)),
                .array ⟨xs.map (fun v => .int v .uint64)⟩⟩
        ∧ ∀ (a : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨a⟩) = some c →
            Heap.lookup σf.heap (.base ⟨a⟩) = some c
```

(`minmax_readout` beneath it: the run-conditioned reading, derived.)

**Axioms:** `[propext, Classical.choice, Quot.sound]`.

**Ground:** pinned lowering of the source above (check-golden, both
links); differentially tested on 6 rows in
`Corpus/coverage/exec/examples/minmax/`, including `empty-panics` (the
`s[0]` panic pinned against `go run`) and an int64-boundary value.

### isort — insertion sort (nested loops, short-circuit `&&`)

```go
func insertionSort(s []uint64) {
	for i := 1; i < len(s); i++ {
		for j := i; j > 0 && s[j-1] > s[j]; j-- {
			s[j-1], s[j] = s[j], s[j-1]
		}
	}
}
```

**Claim.** For any list `xs` of uint64 values, wherever it lives in
memory, with anything else present: `insertionSort` completes
normally — past one fuel bound, at every nondeterminism-choice
stream — the slice then holds a **sorted permutation of `xs`**
(`sortSpec_sorted`: the result is sorted; `sortSpec_count`: every
value keeps its multiplicity; `sortSpec_length`), and no other memory
is touched. The strict `>` keeps equal elements in place (stability,
visible in `insertSpec`'s `≤` branch). At `j = 0` the machine provably
never reads `s[j-1]` — Go's short-circuit `&&`, realized as the
model's one-step false delivery. Every quantifier is discharged
symbolically.

**The theorems** (`proofs/GoLeanProofs/Examples/InsertionSort.lean`):

```lean
def insertSpec (v : Int) : List Int → List Int
  | [] => [v]
  | w :: rest => if w ≤ v then w :: insertSpec v rest else v :: w :: rest

def sortSpec (xs : List Int) : List Int :=
  xs.foldl (fun acc v => insertSpec v acc) []

theorem isort_ok (xs : List Int) (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64)
    (hlen : xs.length < 2 ^ 63)
    (base : Nat) (fr : Heap) (na : Nat)
    (hb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hwf : MachineWf
      { functions := isortLowered.funcs,
        heap := sliceCells xs base ++ fr, nextAddr := na }
      (.exec (isortCall xs base) [] .stop)) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel [] (isortSeed xs base fr na) ch (isortCall xs base)
          = .ok (.normal σf, ch')
        ∧ Heap.lookup σf.heap (.base ⟨base⟩)
            = some ⟨some (.array xs.length (.int .uint64)),
                .array ⟨(sortSpec xs).map (fun v => .int v .uint64)⟩⟩
        ∧ ∀ (a : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨a⟩) = some c →
            Heap.lookup σf.heap (.base ⟨a⟩) = some c
```

(plus `sortSpec_sorted` / `sortSpec_count` / `sortSpec_length` and the
derived `isort_readout`.)

**Axioms:** `isort_ok`/`isort_readout`:
`[propext, Classical.choice, Quot.sound]`; the pure corollaries:
`[propext, Quot.sound]`.

**Ground:** pinned lowering of
`Corpus/coverage/exec/examples/isort/main.go` (check-golden, both
links); differentially green on 8 rows
(shuffled/sorted/reversed/duplicates/int64-boundary/three/one/empty).

### binsearch — first-occurrence binary search over a sorted []uint64

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

**Claim.** For any SORTED list `xs` of uint64 values of length below
`2^62`, any in-range target, wherever the input lives in memory, with
anything else present: `search(s, target)` completes normally — with
enough fuel, under every nondeterminism choice — and returns the index
of the FIRST occurrence of the target, or `-1`; the input array is
unchanged and no other memory is touched. The `2^62` length bound is
the program's own domain, not ours: `mid := (lo + hi) / 2` computes
`lo + hi` in Go `int`, and at greater lengths the sum can wrap
negative — the classic "nearly all binary searches are broken"
overflow bug (Bloch 2006); below the bound the proof carries the
no-wrap fact through every iteration. The post-loop `&&` is proved
lazy: when `lo = len(s)`, the out-of-bounds read `s[lo]` never
happens.

**The theorems** (`proofs/GoLeanProofs/Examples/BinSearch.lean`):

```lean
def Sorted (xs : List Int) : Prop :=          -- GoLean.SliceMem.Sorted, shared
  ∀ i j : Nat, i < j → j < xs.length → xs.getD i 0 ≤ xs.getD j 0

def findSpec (xs : List Int) (t : Int) : Int :=
  match xs with
  | [] => -1
  | v :: rest =>
      if v = t then 0
      else if findSpec rest t < 0 then -1 else findSpec rest t + 1

theorem search_ok (xs : List Int) (t : Int)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (ht : 0 ≤ t ∧ t < 2 ^ 64)
    (hsorted : GoLean.SliceMem.Sorted xs)
    (hlen : xs.length < 2 ^ 62)
    (base : Nat) (hb0 : base ≠ 0)
    (fr : Heap) (na : Nat)
    (hfb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hf0 : Heap.lookup fr (.base ⟨0⟩) = none)
    (hwf : MachineWf
      { functions := searchLowered.funcs,
        heap := resCell ++ sliceCells xs base ++ fr, nextAddr := na }
      (.exec (searchCall xs base t) searchEnv .stop)) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel searchEnv (searchSeed xs base fr na) ch
            (searchCall xs base t)
          = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int (findSpec xs t) .int)
        ∧ Heap.lookup σf.heap (.base ⟨base⟩)
            = some ⟨some (.array xs.length (.int .uint64)),
                .array ⟨xs.map (fun v => .int v .uint64)⟩⟩
        ∧ ∀ (a : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨a⟩) = some c →
            Heap.lookup σf.heap (.base ⟨a⟩) = some c
```

(`search_readout` beneath it: the run-conditioned reading, derived.)

**Axioms:** `[propext, Classical.choice, Quot.sound]`.

**Ground:** pinned lowering of
`Corpus/coverage/exec/examples/binsearch/main.go` (check-golden, both
links); differentially green on 11 rows incl. the
duplicates-lower-bound row (first occurrence, not any occurrence) and
an int64-boundary value.

(the wordcount draft appended at integration from the worker report)

## §6 TCB-grounding walks (per-export discipline)

**`gcd_ok`/`gcd_readout`** statement closure, every identifier to its
ground: `execStmt`, `execStmtLoop`, `loadLoc`, `Heap.lookup`,
`ExecState`, `Choices`, `ExecOutcome.normal`, `GoValue.int`,
`IntKind.uint64`, `Loc.base`, `HeapCell`, `MachineWf` — interpreter
vocabulary (the differentially validated trust surface);
`gcdSeedFr`/`gcdEnv`/`gcdCall` — three literal defs over `gcdLowered`;
`gcdLowered` — GENERATED from the frontend's lowering of the corpus
source, byte-pinned by `scripts/check-golden` (both links);
`Nat.gcd` — Lean core's gcd (the mathematical reference; no in-module
spec function needed); `Nat`/`Int`/quantifiers — Lean core. NO Iris,
no WP, no Frame vocabulary in the statement closure (`FrameSim`/
`renameLoc` appear only in proofs). Deletion test: the statements
survive deleting the entire proof layer.

**`minmax_ok`/`minmax_readout`**: interpreter vocabulary as gcd's plus
`sliceCells` (SliceMem, the §9a shared constructor — 5 lines of
first-order constructor application); `minSpec`/`maxSpec` — six-line
recursive references, in-module; `resCells`/`minMaxEnv`/`minMaxCall`/
`minMaxSeed` — literal defs over `minMaxLowered` (GENERATED, byte-
pinned by check-golden). No Iris/WP/Frame names in the statement
closure; deletion-test clean.

**`isort_ok`/`isort_readout` + corollaries**: interpreter vocabulary +
`sliceCells` + `SliceMem.Sorted` (shared, first-order) +
`insertSpec`/`sortSpec` (in-module, readable recursion/fold) + literal
seed/call defs over the pinned `isortLowered`. The frame theorem's
vocabulary appears ONLY in proofs (both consumption sites — the
in-run rebase and the ∀-placement transfer); deletion-test clean.

**`search_ok`/`search_readout`**: interpreter vocabulary +
`sliceCells` + `SliceMem.Sorted` (shared) + `findSpec` (in-module,
readable recursion) + literal seed/call defs over the pinned
`searchLowered`. No Iris/WP/Frame names in the statement closure;
deletion-test clean.

(walks for the remaining examples appended at integration)
