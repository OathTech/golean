# Verified-examples scale-out (slice 2c) — session record (2026-08-13)

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
| gcd | `gcd_ok` — framed TOTAL, full uint64², EXACT `Nat.gcd a b`; + `gcd_readout` | direct segments; ONE strong induction on the b-value (§5c non-unit ≤-decrease realized directly); `%`'s divide-by-zero branch = the single conditioned step (`applyStrictOp_mod_u64`, the §5c-predicted emod fact); frame transfer = fib's uniformShift pattern | **PROVEN + COMMITTED** (`c264c9f7`), axioms classical trio, fuel `71 + 45·b` |
| min/max | `minmax_ok` — memory-input read-only, TOTAL-HEAP preservation (result cells + input cell pinned + frame pointwise); `hne : xs ≠ []` (Go panics on empty — corpus row pins it) | reverse's route; ONE strong induction on `len − m`; relocation fixing result cells 0/1; headline landed VERBATIM as designed (zero statement deltas) | **PROVEN + COMMITTED**, axioms classical trio, fuel `37 + 96·len` |
| binary search | `search_ok` — sorted precondition (`SliceMem.Sorted`), `findSpec` first-occurrence-or-−1, **domain `len < 2^62`: the Bloch mid-overflow bug carried as the honest domain bound (the teaching point)** | reverse's route; strong induction on `hi − lo` (halving absorbed by strict decrease); short-circuit `&&` laziness in the post-loop guard is load-bearing | worker in flight |
| insertion sort | `isort_ok` — memory-input read-write, `sortSpec` + `sortSpec_sorted`/`sortSpec_count` corollaries ("sorted permutation" said honestly) | direct segments; **nested-loop composition = plain nested strong inductions on the direct route — no measure-rule variant needed** (the rule-composition sugar gap is a WP-route concern only); quadratic fuel | worker in flight |
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

(binsearch / isort / wordcount drafts appended at integration from
the worker reports)

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

(walks for the remaining examples appended at integration)
