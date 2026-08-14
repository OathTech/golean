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
| gcd | **HARNESS-RESTATED**: `gcd_ok` over `runFunctionWithContextM` (returned data = `Nat.gcd a b`, full uint64²) + `gcd_readout` twin; memory forms kept as `gcd_framed`/`gcd_framed_readout` | segments + b-value induction ported; entry equation | **RESTATED + COMMITTED**, classical trio, fuel `91 + 45·b` |
| min/max | **HARNESS-RESTATED**: `minmax_ok` over `runFunctionWithContextM` (minmax_harness, setup family `s[i] = seed + i`, returned pair = `minSpec/maxSpec (mmFamily n seed)`; input-family honesty recorded); memory forms kept as `minmax_framed`/`minmax_framed_readout` | setup-loop invariant over make-replicate backing + ported induction | **RESTATED + COMMITTED**, classical trio |
| binary search | **HARNESS-RESTATED**: `search_ok` over `runFunctionWithContextM` (search_harness: sorted family `seed + 2i` under `hnowrap`, raw target; returned index = `findSpec (bsFamily n seed) t`; the 2^62 Bloch bound carries over); memory forms kept as `search_framed`/`search_framed_readout` | setup-loop induction + full subject-phase port under the harness continuation | **RESTATED + COMMITTED**, classical trio, fuel `220 + 132·n` |
| insertion sort | **HARNESS-RESTATED (gap closed 2026-08-13)**: `isort_ok` over `runFunctionWithContextM` (isort_harness(n, seed): setup family `s[i] = seed·(i+1) mod 2^64`; verdict 1 = sortedness scan AND count-based permutation check, both IN GO) + `isort_readout` twin; memory forms kept as `isort_framed`/`isort_framed_readout` | subject-phase port under the harness continuation + the whole test phase: scan/rebuild/count proven as ONE canonical run from the post-subject 11-cell state, transferred in a SINGLE frame application; second frame-rebase layer (threshold 21, retire 4/pass) for the count loops | **RESTATED + COMMITTED**, classical trio, fuel `(92n+160)n + (110n+220)n + 285n + 505` |
| word-count | **HARNESS-RESTATED, G1 CLOSED (consolidation slice 2026-08-14)**: `wordcount_ok` over `runFunctionWithContextM` (wordcount_harness(n, seed): setup family `w[i] = seed + i%3`; hypotheses just `n < 2^63`, `seed < 2^64`; returned data = `(n+2)/3` via the proven `wcFamily_maxMult`) + `wordcount_readout` twin; plus the earlier `maxCount_total_canonical` (∀ws ∀ch, STRONGER than any scalar family — kept as the supporting inner-run theorem) and `wordcount_empty_ok` | the placement-generic composition layer (`wcIter_generic`/`wcLoop_generic`/`wcRange_generic`, consolidation slice): compositions stated once over an abstract state family, both placements instantiate; storm diagnosis + closure record in `docs/2026-08-13_consolidation-slice.md` §1 and the module | **RESTATED + COMMITTED**, classical trio, fuel `229 + 165·n`. Finding 21's storm: root-caused and structurally removed (the "combination" theory refuted) |

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
    18. **(wordcount, verification-method)** Two of the wordcount
    worker's intermediate "green" checks were FALSE greens — emptied
    command output read as success. Its final state was re-verified at
    integration with explicit exit codes (elaboration exit 0, zero
    hatches, axiom prints matching). Standing rule reaffirmed: an
    empty output stream is not a verdict; only an explicit exit code
    plus the artifact is (CLAUDE.md's async-diagnosis note, now bitten
    from the other side).
19. **(infra)** During the post-outage re-verification the systemd
    user manager reported `degraded` and `scripts/capped` scopes were
    killed at ~90s regardless of cap size (RSS ~180MB — not memory).
    The loud `GOLEAN_MEM_MAX=none` opt-out was used for exactly the
    three wordcount verification commands, recorded here; the full
    builds and gates below went back through the cap wrapper
    normally.

20. **(wordcount) THE SEED-WRAP CAVEAT IS REFUTED** — a recorded
    caveat that was simply wrong, caught by re-deriving it instead of
    encoding it. The slice record and the Audit prose both claimed the
    `i%3` family "collides at `seed ≥ 2^64 − 2`", so G1 would need
    `hseed : seed + 2 < 2^64`. Family values are `(seed + r) mod 2^64`
    for `r ∈ {0,1,2}`; two are equal iff `r ≡ r' (mod 2^64)`, which is
    impossible for distinct `r, r' ≤ 2`. **No collision exists at any
    seed.** So the wrap belongs INSIDE the family definition (`wcFamily`,
    mirroring isort's `isFamily`), the only seed hypothesis is the
    uint64 domain `seed < 2^64` (consumed solely by the entry
    equation's argument normalization), and the returned max count is
    `⌈n/3⌉ = (n+2)/3` UNCONDITIONALLY — now the theorem
    `wcFamily_maxMult`, which is where the no-collision analysis is
    actually consumed. Cross-checked against the `go run` oracle at
    seeds `0, 50, 2^63−1, 2^64−3, 2^64−2, 2^64−1` before any Lean was
    written. Method note: the cheap move was deriving the caveat from
    the Go semantics rather than inheriting it from the record — an
    inherited hypothesis that nobody re-derives is how a statement
    silently narrows.

21. **(wordcount — the G1 blocker, and a NEW obstruction class)** The
    recipe's premise held exactly where it was tested: every
    per-segment `with_unfolding_all rfl` lemma of the phase-C tower
    re-instantiates at the harness placement (16-cell front, map data
    at 12, the harness after-call continuation), as do the entry
    equation and the whole setup phase. What does NOT port is the
    **composition** layer: `wcH_count_iter`/`wcH_count_loop`, verbatim
    address-renames of canonical originals that pass under 2M
    heartbeats, hit an elaborator isDefEq/whnf storm — heartbeat-linear
    grind at 2M/4M/12M (`BEq.beq` unfolds 2.0M @4M vs 6.1M @12M,
    `Heap.lookup` reduced ~134k times @4M, ~1M `f a =?= f b` heuristic
    hits), RSS observed to 52 GB.
    **This is explicitly NOT a false goal** — the `#eval`-before-you-
    decide doctrine was applied and cleared it: every segment equation
    `rfl`-checks and the concrete `(n,seed) = (4,7)` run agrees end to
    end (841 steps, returns `2 = (4+2)/3`). Bisected across scratch
    copies `wcB-mod-v3a…v3b8`: ignites at the `storeTarget_addr`
    application for the `$c1` store, insensitive to argument style,
    instant in isolation even with the real payload, and NOT cured by
    dropping the segment chains — the trigger is the combination of a
    `rw`-surgered hypothesis (carrying `Param`-projection cells and
    `declare`-spelled envs) with a subsequent large application.
    Self-contained repro `.tmp/wcB-repro4.lean`; three-step pickup plan
    in the module docstring. This is the ELABORATOR-COST cousin of
    finding 15c (re-spelling a state term the unifier could infer sends
    `isDefEq` into a whnf storm) — 15c priced it as a hazard to avoid at
    an application site; here it is load-bearing enough to block a
    headline, which promotes it from method note to obstruction class.
    Disposition (operator direction): G1 is re-attempted AFTER the §8
    consolidation slice builds the shared kit, as that kit's first
    consumer — the placement-generic segment/composition lift is
    exactly the >200-line row the grind flagged (~800+ lines on this
    module alone, and it removes the storm class rather than working
    around it).

22. **(process) Two 64 G-capped elaborations over-committed the box.**
    Mid-session the wordcount lane had two probe elaborations running
    concurrently at 52 GB and 24 GB, each inside its own verified 64 G
    scope, on a 125 G machine also hosting an unrelated build — 35 GB
    free and both still climbing. The per-job cap did its job (no job
    could take the box alone) but the CAP BUDGET is not enforced by
    anything: two legal caps sum past the machine. The lead killed the
    stale scope and moved probe work to `GOLEAN_MEM_MAX=24G`. Recorded
    as a live instance of CLAUDE.md's cap-budget rule (which scoped it
    to parallel LANES; it applies just as much to parallel PROBES
    inside one lane), and as evidence that a probe needing >24 GB is a
    diagnostic signal, not a memory request.

## §5 Gallery entry drafts

Read note (2026-08-14): the statements printed in this section are the
PRE-PIVOT memory-quantified forms. The harness ruling (form note §11)
moved those names to the harness headlines and renamed the forms below
`<example>_framed`/`<example>_framed_readout` — so `gcd_ok` here is
today's `gcd_framed`, and so on. The shipped gallery is
`docs/verified-examples.md`.

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

(`search_framed_readout` beneath it: the run-conditioned reading,
derived.)

**Axioms:** `[propext, Classical.choice, Quot.sound]`.

**Ground:** pinned lowering of
`Corpus/coverage/exec/examples/binsearch/main.go` (check-golden, both
links); differentially green on 11 rows incl. the
duplicates-lower-bound row (first occurrence, not any occurrence) and
an int64-boundary value.

(the wordcount draft appended at integration from the worker report)

## §6 TCB-grounding walks (per-export discipline)

**`gcd_framed`/`gcd_framed_readout`** statement closure, every identifier to its
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

**`minmax_framed`/`minmax_framed_readout`**: interpreter vocabulary as gcd's plus
`sliceCells` (SliceMem, the §9a shared constructor — 5 lines of
first-order constructor application); `minSpec`/`maxSpec` — six-line
recursive references, in-module; `resCells`/`minMaxEnv`/`minMaxCall`/
`minMaxSeed` — literal defs over `minMaxLowered` (GENERATED, byte-
pinned by check-golden). No Iris/WP/Frame names in the statement
closure; deletion-test clean.

**`isort_framed`/`isort_framed_readout` + corollaries**: interpreter vocabulary +
`sliceCells` + `SliceMem.Sorted` (shared, first-order) +
`insertSpec`/`sortSpec` (in-module, readable recursion/fold) + literal
seed/call defs over the pinned `isortLowered`. The frame theorem's
vocabulary appears ONLY in proofs (both consumption sites — the
in-run rebase and the ∀-placement transfer); deletion-test clean.

**`search_framed`/`search_framed_readout`**: interpreter vocabulary +
`sliceCells` + `SliceMem.Sorted` (shared) + `findSpec` (in-module,
readable recursion) + literal seed/call defs over the pinned
`searchLowered`. No Iris/WP/Frame names in the statement closure;
deletion-test clean.

**`isort_ok`/`isort_readout` (the §11 HARNESS headline, gap closed
2026-08-13)** — statement closure, every identifier to its ground:
`runFunctionWithContextM`, `Choices`, `Result`, `GoValue.int`,
`IntKind.uint64` — interpreter/native-entry vocabulary (the
differentially validated trust surface); `isortLowered.typeDefs`/
`.funcs`/`.methods` — GENERATED from the frontend's lowering of the
corpus source, byte-pinned by `scripts/check-golden` (both links);
`isortHarnessFunc` — the harness `Func` record transcribed literally
and tied to the lowering by an `rfl` pin; `Nat`/`Int`/`∃`/`∀` — Lean
core. **NO heap vocabulary at all**: no `loadLoc`, no `Heap.lookup`,
no `sliceCells`, no seed/env/frame names, no `MachineWf` — the verdict
is computed IN GO inside the verified footprint, which is precisely
the §11 ruling's point (2) and (3). No Iris, no WP, no Frame names;
the frame theorem appears only in proofs (now at THREE in-run
consumption sites plus the ∀-placement transfer). Deletion test: run
this session — the statement elaborates against
`Examples/InsertionSortProgram` + `FuelMeasure` alone, with the whole
proof layer gone.

**`isort_framed`/`isort_framed_readout`** — unchanged from the
memory-quantified walk above (same closure: interpreter vocabulary +
`sliceCells` + `SliceMem.Sorted` + `insertSpec`/`sortSpec` + literal
seed/call defs over the pinned `isortLowered`); the rename does not
touch the closure.

**`wcFamily_maxMult` (wordcount, the only new wordcount export)** —
closure is PURE: `wcFamily` (one `List.range`/`map` line, the wrap in
the definition), `maxMultiplicity`/`multiplicity` (in-module folds over
`List.filter`), `Nat` arithmetic. No interpreter vocabulary at all —
it is the pure arithmetic content the refuted seed caveat was really
about. (Superseded 2026-08-14: this paragraph used to close by saying
the G1 headline's walk was not written because the headline was not
shipped. `wordcount_ok` SHIPPED at `f8820d62` — gap G1 closed — and its
statement-closure walk lives in `proofs/Audit.lean` (the wordcount
block, "Statement closure: interpreter/native-entry vocabulary …"), so
there is no unwritten walk here.)

## §7 Harness-restatement round (post-ruling; appended at integration)

Fib + reverse (the exemplars) and gcd/minmax/binsearch restated over
`runFunctionWithContextM`; isort = recorded gap with groundwork
(ledger). Key round findings:

13. **The entry-equation recipe works first-try when the RHS mirrors
    the source's own do-syntax** (both exemplar workers converged on
    it independently): one `with_unfolding_all rfl` per example, ∀
    fuel ∀ ch — the prelude is fuel-independent and branch-on-
    constructors, so symbolic argument payloads ride through;
    bindParams leaves ONE stuck `IntKind.normalize` per argument,
    cleaned after the rewrite, never inside the equation.
14. **fib's harness pair drops `Classical.choice`** —
    `[propext, Quot.sound]` only: no Iris and no frame layer anywhere
    in the direct-segment + entry-glue derivation. The reverse/gcd/
    minmax/binsearch headlines keep the trio solely through
    `Machine.Heap.lookup_set_ne`-rooted facts (e.g.
    `buildDefaultArrayValue_int`).
15. **The harness form's own frictions, priced by the round**: (a) the
    harness tail stacks a THIRD normalizing store on every returned
    value (subject `$res0` → local write-back → harness `$res0`) —
    three `unorm` collapses per value is the whole cost; (b)
    `make([]uint64, n)` at symbolic `n` is one conditioned step via
    the pre-existing `buildDefaultArrayValue_int` (Laws/StmtOps),
    imported PROOF-SIDE by the memory-input example modules — the
    statement closures stay Iris-free; (c) an elaborator hazard worth
    a method note: re-spelling a large state term at an application
    site the unifier could infer sends `isDefEq` into a whnf storm —
    always let the hypothesis pin the state.
16. **FuelMeasure gained the full shared entry kit**: `runConfig_unfold/
    step/of_stepFnIter/next_stop/mono`, `runFunctionWithContextM_mono`,
    `harness_readout_of_total` — witnesses `fib_readout`,
    `reverse_readout`, `gcd_readout`, `minmax_readout`. The `_seeded`
    renames (fib) and `_framed` renames (all others) keep every old
    proof layer compiling; binsearch's temporary Audit-compat stub was
    deleted at integration (the orphaned-shell rule).
17. **Gallery drafts for the harness round live in the worker reports
    and the Audit prose**; the §5 drafts above remain the
    memory-form record (superseded as gallery material, kept as the
    proof-side layer's documentation). Slice 3 renders from the
    harness headlines.

## §8 PROMOTION-CANDIDATES LEDGER (operator direction, 2026-08-13)

Standing rule adopted mid-slice: **every time a pattern is instantiated
for the SECOND-or-later time, it gets a row here** — pattern, consumers,
approximate per-use line cost, and whether the lift is a LEMMA or a
TACTIC/macro shape. The lifting itself is NOT done in this lane; a
dedicated consolidation slice follows (brick-wp lesson: repeated
patterns become shared abstractions for leverage, and grind is the
signal that one is missing). Costs are measured from the landed files
and marked approximate where the pattern is interleaved with
example-specific algebra.

Hard density figures behind the rows (measured at the gap-closing tip):
`with_unfolding_all rfl` segments per module — fib 18, reverse 37,
gcd 14, minmax 42, binsearch 59, **isort 78**, **wordcount 66**; and
6–8 duplicated `private` kit lemmas in EACH of reverse / minmax /
binsearch / isort / wordcount.

| # | pattern | consumers | ~per-use cost | lift shape |
|---|---|---|---|---|
| P1 | `stepFnIter_one`, `stepFn_strict_apply`, `stepFn_store_step` (conditioned one-step glue) | reverse, gcd, minmax, binsearch, isort, wordcount (6) | ~25 lines | **LEMMA** (straight move to the FuelMeasure kit; zero design work) |
| P2 | `getElem?_mapU`, `getD_mem`, `locSup_mapU`, `mem_set_of_mem` (slice-value plumbing) | reverse, minmax, binsearch, isort, wordcount (5) | ~30 lines | **LEMMA** (SliceMem) |
| P3 | `unorm_of_range` / `unorm_nat_mod` / `inorm_nat_of_lt` normalization cleanups | all 7 | ~10 lines, but invoked 5–15× per module | **LEMMA + simp set** — a `unorm` simp-set is the real win, not the individual lemmas |
| P4 | **The §11 entry equation** (`σ*0` state def + env def + `with_unfolding_all rfl` mirror of the source do-syntax) | fib, reverse, gcd, minmax, binsearch, isort, wordcount (7) | ~30 lines | **TACTIC/macro** — the state term is mechanically derivable from the `Func` record's args/results; a `derive_entry_equation` elaborator would erase all 7 copies (finding 13 already says the RHS is a syntactic mirror) |
| P5 | **The setup-loop induction over `make([]uint64, n)` + a scalar family** (makeSlice apply at symbolic `n`, replicate-backing start, `fam i ++ replicate (n−i) 0` invariant, `storeTarget_slice_u64` element store, `57·(n−i)`-style step accounting) | reverse (`su_loop`), minmax, binsearch, isort (`hIsetup_loop`), wordcount (4) | **~250–350 lines** | **LEMMA (parameterized)** — one induction abstracted over the family function `f : Nat → Nat → Int` and the backing/handle addresses. Highest-value row in the table. isort instantiates it TWICE inside one module (setup + the test phase's rebuild loop). |
| P6 | `natFromNonneg_cast'` + the symbolic-`n` makeSlice apply | reverse, binsearch, isort (×2 in-module: cells 3/4 and 14/15), wordcount | ~40 lines | **LEMMA** |
| P7 | **The test-phase verdict walk** (flat `for` scan whose body conditionally clears `ok`, invariant "`ok` stays 1 given a pure fact") | reverse (`tst_loop`), isort (sortedness scan + the count-loop verdict) | ~150 lines | **LEMMA (parameterized)** — abstract over the per-index predicate and the pure discharge |
| P8 | **Frame-rebase-into-garbage at a threshold** (`transfer_seg`/`rebaseSim`/`frameSim_zero` plumbing: prove a pass at a tight canonical placement, transfer at the accumulated-garbage shift, retire the dead cell block into the frame) | isort ×3 IN ONE FILE (thresholds 4, 11, 21; retire 2 / 0 / 4 cells per pass), binsearch's alternative (garbage-suffix invariant) | ~200 lines per instantiation | **LEMMA family** — "retire-prefix-into-frame at threshold K, retire r cells/pass" in `Frame/`. Finding 8 predicted this growth point at a THIRD nested-allocation example; it arrived as a third instantiation inside the FIRST such example. |
| P9 | `stepFn_seqn_splice` (the `if_pos rfl` discharge for `seqCont`'s environment `DecidableEq` blocking defeq under symbolic addresses) | binsearch, wordcount | ~15 lines | **LEMMA** (finding 11 already flagged it as a strong candidate) |
| P10 | Accumulator ↔ `List.count`/`List.filter` bridge (`cntSpec`/`cntSpec_eq_count`/`cntSpec_take_succ`) | isort (count loops), wordcount (`countsList`/`multiplicity`) | ~80 lines | **LEMMA** — wanted by any future counting harness |
| P11 | Heap-append/lookup reasoning at a symbolic split (`lookup_append_right` + a `front*_none` side condition per state family) | binsearch, isort, wordcount | ~40 lines | **LEMMA + simp set** |

**Where a lift would have saved >200 lines on a gap ground out this
session** (the consolidation slice's priority order): **P5** (isort's
gap paid the setup-loop induction a second time in-module for the
rebuild loop — a parameterized version saves ~300 lines there alone,
and wordcount's gap paid it a fourth time across the arc); **P8**
(three hand-instantiated frame-rebase layers in isort ≈ 600 lines, of
which a lemma family would leave maybe 60); **P4** (7 copies × ~30
lines, and it is the ONE pattern that is purely syntactic — the
cheapest lift with the widest reach). P1–P3 are near-zero-risk moves
that should ride along.
