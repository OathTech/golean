# Examples phase-2, slice 1 — spec-style swaps: slice record (2026-08-14)

Status: **PARTIAL — guardrail half landed; proof half landed for
REVERSE only (swap 1 of 3).** Read this before continuing the slice; it
is the handoff. The session record for the proof half is
§"Proof half — session 2" near the end of this file; the sections
between here and there are the ORIGINAL session-1 record, kept verbatim
for the measurement trail.

Charter: `docs/2026-08-14_examples-phase2-arc-charter.md` §"Slice 1".
Per-example recommendations: `docs/2026-08-14_harness-style-scoping.md`
§9 (drafts were `.tmp/scoping/drafts/`, foundation lane, read-only).
Standing rulings: harness form + ghost ladder rung 0 (real Go, NO
annotations) — form note §11; active abstraction loop — §12.

## What landed

**The guardrail half, per the repo's own "differential tests before
tool buildout" rule**: the new harnesses are real, compiled, executed
Go, differentially green against `go run`, and pinned end-to-end
through the frontend — BEFORE any proof is written. That is the
intended order, not a shortcut.

| swap | harness added | style | corpus rows | machine |
|---|---|---|---|---|
| reverse | `reverse_harness_v` | S1 copy-relational | `harness-v-five`, `harness-v-empty`, `harness-v-wrapping` | green |
| minmax | `minmax_harness_r` | S3 relational | `harness-r-five`, `harness-r-one`, `harness-r-eight`, `harness-r-empty-panics` | green |
| wordcount | `wordcount_harness_r` | S3 relational | `harness-r-seven`, `harness-r-eight`, `harness-r-empty` (re-landed by slice 1.5; was REVERTED, see below) | green |

* Both new harnesses are **ghost rung 0**: ordinary Go. reverse's
  pre-copy `t` is a HISTORY GHOST materialized as real harness code
  (form note §11's "computable observation-only history is
  harness-materializable"); minmax's `pre` is an ordinary fixed-size
  array local. No annotations anywhere.
* The **bounded cap is visible in the Go**: `const minmaxCapN = 8`, so
  the harness's own domain bound is `n ≤ 8` and the future Lean
  headline carries it as a hypothesis rather than hiding it (scoping
  §10 decision 4 — "acceptable, stated plainly").
* Old harnesses and all their rows are KEPT (`reverse_harness`,
  `minmax_harness`): the old headlines still stand and still build.
* Golden re-pin: `baselines/golden/{reverse,minmax}-lowered.repr` and
  the generated `Examples/{Reverse,MinMax}Program.lean` terms
  regenerated in the same commit. The re-pin is **purely additive** —
  no existing line of either repr changed, only new `Func` records
  appended — which is why every existing `with_unfolding_all rfl`
  segment and every lowering pin stayed true (verified: `MinMax` and
  `Reverse` rebuild green).
* Baseline re-pin: `baselines/native-full.tsv` gains exactly the seven
  new ids, all PASS.

New differential coverage bought, beyond the swap itself: the
**fixed-size-array return path** (`[8]uint64` crossing the observation
boundary as a fully-observed value, plus `pre[i] = s[i]` stores into an
array-typed local through `.indexAddr (.ref "pre")`) is now
oracle-checked; the scoping study had only probed it.

## What did NOT land, and why

**No new headline proof landed.** The three headline theorems, the
old-headline demotions, the Audit-shard updates and the gallery
re-renders are all still to do. The honest reason is scope: each swap
is a NEW harness `Func` at a NEW address layout, so the whole
machine-segment layer (~30–40 `with_unfolding_all rfl` segments, each
requiring a probe-and-transcribe cycle) has to be rebuilt per example.
The shipped `reverse_ok` harness proof is ~1250 lines for one such
layer. That is a multi-session build, not a session's work, and the
divergence guard says an honest gap beats a grind.

Nothing dishonest ships as a result: the gallery still describes the
OLD harnesses (which are still the proved ones), the old headlines are
unrenamed and unweakened, and the new harnesses are corpus-only.

## THE WORDCOUNT BLOCKER — measured, and it is a real cost defect

`wordcount_harness_r` was written, ran green through `go run` and the
machine, and had three green differential rows. **It was reverted**,
because adding one function to `Corpus/coverage/exec/examples/wordcount/main.go`
pushed `GoLeanProofs.Examples.WordCount.EmptyRun` past the memory cap:

| state of `wordcount/main.go` | `wc_empty_run` peak |
|---|---|
| as shipped (slice 0 measurement, 2026-08-14) | **50.8 GiB** |
| + `wordcount_harness_r` (this slice, measured) | **~77 GiB** (box-used 90.2 GiB peak against a 13 GiB idle baseline; FAILS at `GOLEAN_MEM_MAX=62G`, succeeds at 90G) |

`wc_empty_run` is a single 158-step `with_unfolding_all rfl` over a
CONCRETE configuration whose state embeds `wordCountLowered.funcs`.
Its cost therefore scales with the size of the whole pinned program,
not just with the run — so **any** future addition to that corpus file
(another harness, another driver, another example row) is blocked by
the same wall. Slice 0 already named this declaration "the whole repo's
memory ceiling"; this slice measured the growth law behind it: it is
superlinear in the program the state carries, and the default 64G cap
is already breached by one extra function.

**RESOLVED by slice 1.5 (2026-08-14, operator-inserted): see the
section "Slice 1.5" below.** The blocker record is kept as written for
the measurement trail; route 2 below is what shipped, and the growth
law is severed — the corpus program can grow again.

**Prerequisite for the wordcount swap** (and for any further growth of
that corpus program): restate `wc_empty_run`. Two routes, cheapest
first —

1. **Chunk it.** Split the 158-step `rfl` into ~5 shorter
   `stepFnIter_chain`ed segments, naming the statement pieces and
   continuations the way `Examples/Reverse.lean` names `hS2`…`hS7` and
   `suHeadTail` so the split-point configurations are writable. Purely
   mechanical once the split points are probed; a working probe recipe
   is recorded below.
2. **Make it placement/program-generic** (charter lever 4, the E-form):
   condition the heap-touching steps on `Heap.lookup`/`storeTarget`
   facts so no concrete front reaches the kernel. Strictly better, more
   work.

The charter's "verified reflection" research direction remains the
endgame lever; neither route above needs it.

### The probe recipe (reusable, works today)

`Config` has no `Repr` instance in the proof layer, but one can be
derived locally in a scratch file, and `#eval`/`lean --run` uses the
COMPILER (cheap) rather than kernel whnf (the expensive thing). So
split points and target configurations can be read off directly:

```lean
import GoLeanProofs.Examples.WordCount.EmptyRun
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
deriving instance Repr for GoLean.GoCore.Machine.Cont
deriving instance Repr for GoLean.GoCore.Machine.Config

def probe (k : Nat) : IO Unit := do
  match stepFnIter k σ0 c0 [] with
  | .ok (c, σ, _) => IO.println (repr c); IO.println (repr σ.heap)
  | .error e => IO.println s!"ERROR {repr e}"
```

Run it with `scripts/capped lake env lean --run <file>` from `proofs/`.
This is the loop that makes the segment layer transcription-bound
rather than search-bound; it is worth keeping.

Two gotchas, both hit and both cheap to avoid: `Func` has no
`Inhabited` instance (use a `match … with | some f => f | none => …`
rather than `.get!`), and a driver that single-steps to the terminal
—

```lean
while k < 3000 && !done do
  match stepFn σ cur [] with
  | .ok (c', σ', _) => cur := c'; σ := σ'; k := k + 1
                       match c' with | .next .stop => done := true | _ => pure ()
  | .error e => IO.println s!"ERROR at k={k}: {repr e}"; done := true
```

— gives the exact step count per `n` in one run, which is how the fuel
bound below was measured rather than guessed.

## Slice 1.5 — the long-concrete-run class RETIRED (2026-08-14)

Operator-inserted slice: re-prove `wc_empty_run` (statement
byte-identical, `wordcount_empty_ok`'s axiom pin unchanged) so the
kernel never whnf's a configuration embedding the whole program, then
re-land the reverted `wordcount_harness_r` as the real test.

**The diagnosis, confirmed by controlled experiment** (probes capped
24G): the memory went exactly where the blocker record guessed —
elaborator+kernel whnf across the 158-step reduction carries the
`ExecState` with `functions := wordCountLowered.funcs` through every
intermediate term, and the per-step unfold/rebuild of that
program-embedding state is what cost 50.8 GiB (superlinear in program
size because the fronts are re-compared without sharing). The
controlled half: the IDENTICAL 158-step run with only the program
context σ-abstracted elaborates at **1.9 GiB** — same statement shape,
same step count, ~29× memory drop, wall unchanged (~86 s, the whnf
step-walk itself).

**The fix (route 2, the E-form extended to PROGRAM-generic):** the run
has exactly ONE step that consults the program context — the
`maxCount` frame entry (probe-verified: every `defaultValue`/
`normalizeValueForTy` use is at structural types, the empty snapshot's
self-normalization check is vacuous, `methods` is `#[]`). So:

* two segments stated over abstract `σ : ExecState` with only
  `heap`/`nextAddr` pinned (`wc_empty_seg1`, 20 steps: harness
  prelude; `wc_empty_seg2`, 137 steps: `maxCount` body + frame exit +
  tail) — both close by `with_unfolding_all rfl` over ≤12-cell heaps;
* the entry step conditioned on its `enterFrame` fact
  (`wc_empty_enterFrame_step`, the P1-family shape, stated generically
  in-module — promotion candidate `stepFn_call_enter`, waiting on a
  second consumer per §12);
* `stepFnIter_chain` composition (`wc_empty_run_generic`), then the
  byte-identical `wc_empty_run` instantiates it, discharging the
  `enterFrame` fact by `rfl` — the ONLY point the pinned program is
  unfolded, and `maxCount` is the funcs array's head, so the scan
  stops immediately.

Technique recorded normatively in the StepKit module docstring
("Long CONCRETE runs: the PROGRAM-generic form"); worked template is
the EmptyRun shard itself. Promotion ledger: no lift shipped (single
consumer); `proof-costs` confirms no other example has a member of
this class (next-heaviest module ≈ 2.0 GiB).

**Measurements (acceptance):**

| item | before | after |
|---|---|---|
| `EmptyRun` shard elaboration (proof-costs / `time -v`) | 76–82 s, **50.8–53.5 GiB** | 86 s, **1.9 GiB** (24G-capped) |
| the same with `wordcount_harness_r` added | **~77 GiB** (breaks 64G cap) | **1.94 GiB** (whole WordCount subtree + Audit, 24G-capped, 2:12) |
| full `scripts/ci` | needs 64G (one declaration) | **PASS at `GOLEAN_MEM_MAX=48G`** — slice-0 lever-1 acceptance met |
| `wordcount_empty_ok` axioms | `[propext, Quot.sound]` | identical (Audit `#guard_msgs` pin, unchanged, green) |

**The real test — `wordcount_harness_r` re-landed:** the exact corpus
addition that broke the build now ships (harness text as recorded in
scoping §4.7; rows `examples/wordcount/harness-r-{seven,eight,empty}`,
all differentially green; golden + `WordCountProgram.lean` re-pins
purely additive, both `check-golden` links green; tracked baseline
re-pinned from a full 1560-case run — drift exactly the 3 new ids).
Growth in the pinned program no longer moves `EmptyRun`: the program
constant is only unfolded at the `enterFrame`/pin `rfl` discharges,
never inside the step reduction.

## Handoff: the proof designs, ready to build

### reverse — S1 copy-relational (`reverse_harness_v`)

Statement shape is UNCHANGED from the shipped `reverse_ok`
(`= .ok { values := #[.int 1 .uint64] }`, hypotheses `n < 2^63`,
`seed < 2^64`) — the swap's payoff is entirely in the Go: the test
phase checks `s[i] != t[n-1-i]` against the SAVED PRE-COPY instead of
re-deriving the setup formula `seed+(n-1-i)`, so the check IS the
reversal relation and the harness reads as an ordinary unit test. It is
also the nondet-annotation-ready form (ghost rung 1 later: annotating
the one setup assignment makes it ∀-data with the SAME test phase; the
family-formula version cannot, because its check encodes the family).

**Address layout — MEASURED, not predicted** (probe run 2026-08-14,
`nextAddr = 20` at every `n`, so the layout is `n`-independent):

| addr | cell | | addr | cell |
|---|---|---|---|---|
| 0 | `n` | | 10 | `t` |
| 1 | `seed` | | 11 | copy `i` |
| 2 | `$res0` | | 12 | copy `$forFirst` |
| 3 | `$c5` (s handle) | | 13 | reverse's `s` param |
| 4 | s backing array | | 14 | reverse's `i` |
| 5 | `s` | | 15 | reverse's `j` |
| 6 | setup `i` | | 16 | reverse's `$forFirst` |
| 7 | setup `$forFirst` | | 17 | `ok` |
| 8 | `$c6` (t handle) | | 18 | test `i` |
| 9 | t backing array | | 19 | test `$forFirst` |

**Step counts — MEASURED** (terminal `.next .stop`, seed 100):

| n | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|---|
| steps | 335 | 502 | 744 | 911 | 1153 | 1320 | 1562 | 1729 | 1971 |

The first differences alternate 167 / 242 — the 75-step gap is one
two-pointer swap, which happens every OTHER iteration, exactly as in
the shipped proof. So **`335 + 205·n` is a valid affine fuel bound**
(checked against all nine points; tight at even `n`). For comparison
the shipped `reverse_ok` bound is `189·n + 260`; the copy phase is the
whole difference.

Reusable as-is from `Examples/Reverse.lean` (drop `private`): the pure
layers `revFamily`, `suList`+`suList_set`+`suList_full`, the two-pointer
surgery `revSwap`/`revSwap_step`/`revSwap_reverse`, and
`getD_reverse_revFamily`. Genuinely new: the copy-loop induction
(invariant: `t`'s backing = family-prefix ++ zeros, `s` untouched) and
a test loop with TWO index reads per iteration instead of one.

Disposition of the old headline: `reverse_ok` → `reverse_ok_v1`
(supporting), the new one takes `reverse_ok`. NOT superseded outright —
the old harness's rows stay, so keeping it costs nothing.

### minmax — S3 relational (`minmax_harness_r`)

Target statement (elaborated in scoping, §4.4), with `mmFamily` GONE
from the statement:

```lean
theorem minmax_ok (n seed : Nat) (h1 : 1 ≤ n) (hn : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel … minmaxHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64] … ch
          = .ok { values := #[goArr8 pre,
                              .int (minSpec pre) .uint64,
                              .int (maxSpec pre) .uint64] }
```

One new statement-vocabulary def (the whole S3 adapter, style-neutral
below it):

```lean
def goArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map (fun v => .int v .uint64)⟩
```

Witness `pre := mmFamily n seed`; the existing prefix-min/max surgery
(`minSpec_take_succ` etc.) already delivers the value half, so the new
work is the machine layer only. NOTE the address shift: the S3 harness
has THREE result cells (`$res0 : [8]uint64`, `$res1`, `$res2`), so every
address moves by one relative to `minmax_harness` and the whole
`sh_*`/`mh_*` segment layer must be re-derived — which is precisely why
the charter says NEW proofs start placement-generic (StepKit's E-form
docstring). Do that here rather than re-transcribing concretely; minmax
is the natural first consumer, wordcount the second.

**Address layout — MEASURED** (probe run 2026-08-14; `nextAddr = 22`
at every `n`, declared types read straight off the terminal heap):

| addr | type | cell |
|---|---|---|
| 0 | `uint64` | `n` |
| 1 | `uint64` | `seed` |
| 2 | `[8]uint64` | `$res0` |
| 3 | `uint64` | `$res1` |
| 4 | `uint64` | `$res2` |
| 5 | `[]uint64` | `$c15` (handle) |
| 6 | `[n]uint64` | backing array (the ONE `n`-dependent type) |
| 7 | `[]uint64` | `s` |
| 8 | `uint64` | setup `i` |
| 9 | `bool` | setup `$forFirst` |
| 10 | `[8]uint64` | `pre` |
| 11 | `uint64` | copy `i` |
| 12 | `bool` | copy `$forFirst` |
| 13–21 | — | `minMax`'s frame (`$mn`,`$mx`, the `s` param at 15, `lo`/`hi`, the `int` loop counter at 20, `$forFirst` at 21) |

**Step counts — MEASURED**: exactly 186 per element, no alternation
(minmax has one uniform loop body), so `k = 234 + 186·n`, checked at
`n = 1…8` (420, 606, 792, 978, 1164, 1350, 1536, 1722).

Honesty clauses the gallery entry must carry when this lands
(scoping §4.3/§4.4, audited conventions): (i) the cap `n ≤ 8` is a toy
bound, stated plainly, and the harness carries copy loops plus
zero-padding that exist only for observation; (ii) without the ghost
rung-1 annotation the `∃ pre` is still family-determined — the
statement merely avoids SAYING so, and that must be said; (iii) the
machine-idealization clause (unbounded heap, allocation always
succeeds) as in the shipped entries.

### wordcount — S3 relational

Blocked on `wc_empty_run` (above). The harness text is recorded in
`docs/2026-08-14_harness-style-scoping.md` §4.7 and was verified green
through both `go run` and the machine during this slice before being
reverted; target post `best = maxMultiplicity words` over the returned
array, with `wcFamily_maxMult` supplying the value half.

## Unchanged by ruling (charter, recorded reasons)

fib and gcd keep S2 (already the direct statement — no family exists);
isort keeps its shipped S1 (the permutation check is the genre classic,
and the S3 math companion waits for the annotation); binsearch waits at
ghost rung 1, because its direct form needs the sortedness
precondition to stop living silently in the setup family.

## Promotion ledger

No lift was made this slice — no second consumer materialized, because
the proof half did not land. Recorded candidates for when it does (each
needs ≥2 consumers + a fixture in the same commit, per form note §12):

* **`goArr8`** — the S3 statement adapter; consumers minmax + wordcount.
  STATEMENT vocabulary, so it must be introduced under the §11 closure
  rules, not in a kit module.
* **the array-local store fact** — `storeTarget` at
  `.indexAddr (.ref x) i` on an array-typed local, the SliceMem analogue
  for arrays; consumers minmax + wordcount (and any future S3 harness).
  This is the one genuinely new below-statement fact family the S3 style
  needs, and scoping §7 predicted exactly it ("no new machinery CLASS").
* **the copy-into-observation loop schema** — a setup-shaped loop whose
  invariant is "prefix copied, suffix still default"; consumers reverse
  (slice→slice) and minmax/wordcount (slice→array). Same shape as the
  existing `suList` setup-loop schema, which is the argument for lifting
  all three together rather than one at a time.

---

## Proof half — session 2 (2026-08-14): swap 1 of 3 LANDED

### What landed: reverse (S1 copy-relational)

`reverse_ok` is now the verdict theorem over `reverse_harness_v`, in a
new shard `proofs/GoLeanProofs/Examples/Reverse/HarnessV.lean`
(~1050 lines). Verbatim statement:

```lean
theorem reverse_ok (n seed : Nat) (hn : n < 2 ^ 63) (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel reverseLowered.typeDefs.toList
          reverseLowered.funcs reverseHarnessVFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          reverseLowered.methods ch
        = .ok { values := #[.int 1 .uint64] } := by
```

* Fuel bound `N = 205·n + 335` — the measured law of the handoff above,
  reached (not the loose `242n + 335` the naive measure gives) by
  bounding the two-pointer loop with `75 * ((μ + 1) / 2) + 50` instead
  of `75 * μ + 50`: the measure `μ = (n-1) - 2m` drops by TWO per swap,
  so counting swaps rather than measure units is what makes the
  coefficient `167 + 75/2 ≤ 205`.
* Axioms `[propext, Classical.choice, Quot.sound]` (`#guard_msgs` pinned
  in `Audit/Reverse.lean`, green). No `sorry`, no `native_decide`, no
  project axioms. `reverse_readout` is the D1 twin, also pinned.
* Old-headline disposition: `reverse_ok` → `reverse_ok_v1`,
  `reverse_readout` → `reverse_readout_v1` — KEPT unweakened, proofs
  and corpus rows untouched, both re-pinned. `reverse_framed` (the
  genuinely-∀xs form) unchanged.
* Deletion test: dropping `hn` makes the `make([]uint64, n)` length
  wrap negative (the v1 precedent); dropping `hseed` breaks the
  `unorm_of_range` normalization of the `seed` argument at the entry
  equation. Both hypotheses are load-bearing at the statement, not
  proof convenience.

### What went generic, and the honest limit

**PROGRAM-generic, 22 of 22 raw segments.** Every segment is stated
over `vSt σ H na = { σ with heap := H, nextAddr := na }` with `σ`
abstract, so the kernel never whnf's a state embedding
`reverseLowered.funcs`. The pinned program is unfolded exactly TWICE in
the module: the lowering pin, and the single `enterFrame` discharge at
the `reverse(s)` call.

Measured effect, and it is the headline cost result of this session:
**4 s wall / ≤0.4 GiB** for a FOUR-loop example (setup, copy,
two-pointer, test) over a 20-cell heap. The v1 layer, address- and
program-concrete, is ~1250 lines inside a 3.0 s / 1.97 GiB module. The
whole segment layer of the new module elaborates in 2.7 s; the module
is nowhere near the 2.5 GiB bar.

**PLACEMENT (address) genericity was assessed and NOT taken** — the
brief's preferred shape, refused on measurement. The four loop phases
touch a heap cell at nearly every step, so an address-abstract
statement cannot close by `with_unfolding_all rfl` at all: each ~25-step
segment would become ~25 conditioned one-steps (`stepFn_var` +
`storeTarget` + `applyStrictOp` facts), i.e. roughly 10× the source for
a layer that already costs seconds. With only two prospective
instantiations (minmax, wordcount) whose LAYOUTS DIFFER ANYWAY — 20
cells vs 22, different scopes, different result arities — the generic
layer would not be shared even after paying for it. Program-genericity
is the lever that actually moved the number, and it is what the
`StepKit` docstring already recommends. Recorded so the next session
does not re-litigate it from taste.

### Promotion (form note §12): one lift SHIPPED

**`stepFn_call_enter`** (ledger row P1) lifted from
`WordCount/EmptyRun.lean`'s in-module `wc_empty_enterFrame_step` into
`GoLeanProofs/StepKit.lean`, now that a second consumer exists (this
module's `reverse` frame entry). Both consumers retrofitted in the
promotion commit and are its fixture witnesses; EmptyRun's local name
survives as a one-liner over the kit lemma, so its statement pins are
untouched. This is the promotion the 1.5 record predicted, discharged.

Not promoted (deltas to the ledger):

* **`goArr8`** — not reached; the S3 statement adapter is still
  candidate-only, still owed the §11 closure treatment when minmax
  lands.
* **the array-local store fact** — SCOPED but not written. Probe-pinned
  shape (this session): the target is
  `.chain (.addr (.base ⟨10⟩)) [.int iv .uint64] [.index]`, i.e. an
  ADDRESS-rooted chain, so `indexTargetLoc` takes the
  `.addr baseLoc → .array` arm and yields `Loc.index baseLoc i`; the
  store then bottoms out in the same `arraySet` + declared-type
  re-normalization tail as `storeTarget_slice_u64`. The lemma is a
  close mirror of that one and belongs beside it in `SliceMem`, with
  minmax and wordcount as its two consumers.
* **the copy-into-observation loop schema** — the reverse instance is
  built and works, but it is one consumer. Notably the copy loop needed
  NO new pure layer: `t[i] = s[i]` copies exactly the family element
  the setup loop wrote, so `suList`/`suList_set` serve both invariants
  and the only new pure fact in the whole swap is `getD_revFamily`.

### Reuse: the pure layer was shared, not restated

22 names in `Examples/Reverse.lean` were un-`private`d (the `revSwap`
two-pointer surgery, the `revFamily`/`suList` family surgery,
`getD_reverse_revFamily`, `reverse_short`, `ffBlock`) and consumed
verbatim by the new shard. No pure layer was duplicated.

### The probe recipe, extended (reusable)

`.tmp/s1/rvprobe.lean` / `.tmp/s1/mmprobe.lean` — the 1.5 recipe plus a
`trace` mode that prints ONE LINE PER STEP with a constructor tag
(`exec WHILE`, `retV bool | ifK`, `next storeK`, `exec CALL f`, …).
Grepping that trace for `WHILE|CALL|makeSlice|break|return` gives the
whole phase map (every loop head, every exit, the call point) in one
run, and the arithmetic between markers gives every segment's exact
step count BEFORE any Lean is written. That is what made this swap
transcription-bound rather than search-bound: the entire 22-segment
layer was written from one trace plus three `dump`s, and every segment
closed by `with_unfolding_all rfl` on the first attempt. Keep it.

### Gallery

The reverse entry is re-rendered for the swap: the new harness Go
verbatim; the verdict claim states "the check returned `1`" and says
what `1` means in the Go; a new paragraph states what the copy DOES buy
(annotation-readiness at ghost rung 1 — the v1 harness's check encodes
the family and so can never take a ∀-data input with the same test
phase) and what it does NOT (the input quantifier is still the scalar
family); the machine-idealization clause is kept and extended to name
the second observation-only allocation. `scripts/render-gallery` 45/45.

### NOT landed this session, and the honest reason

**minmax (swap 2) and wordcount (swap 3) proof halves.** Reverse
consumed the session. Both remain exactly as the handoff above
describes them, with these additions from this session's probing:

* **minmax layout re-confirmed and phase-mapped** (`n = 2`, seed 100):
  entry 0–53; setup loop heads 53/102/155, exit test 184; `var pre`
  + copy preamble 184→223 (NO makeSlice — `pre` is an array-typed
  local, one `.initialization`); copy loop heads 223/272/325, exit test
  355; `minMax` call at 367, frame entry allocating `s` at 15; minMax
  loop heads 428/504, exit 536; two returns (minMax's at 562, the
  harness's at 603); terminal 606 = `234 + 186·2` exactly.
  The copy body has the SAME 25/16/1/1/1/5 shape as reverse's, so
  `cp_*` transcribes directly.
* **The minMax segment layer ports by an address REMAP** from the
  shipped `minmax_harness` layer: setup-phase cells shift +1 (three
  result cells now, `$c15` at 5 vs `$c12` at 4), the minMax frame
  shifts +4 (old 11–17 → new 15–21), the call temporaries move 9/10 →
  13/14, and cells 10/11/12 (`pre`, copy `i`, copy flag) are new. The
  branch-heavy `mm_iter` case analysis ports unchanged.
* **wordcount** is unblocked (slice 1.5) but untouched.

Divergence guard: not triggered — no proof in this session took more
than a handful of probe iterations. The gap is budget, not difficulty,
and the next session starts from a worked template plus a phase map.
