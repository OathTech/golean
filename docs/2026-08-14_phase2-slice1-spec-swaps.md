# Examples phase-2, slice 1 — spec-style swaps: slice record (2026-08-14)

Status: **COMPLETE — all three swaps landed** (`3fbecfa2` reverse,
`3f4835ba` minmax, `67917d97` wordcount; headlines designated at
`e4202039`). Corrected in the audit response, 2026-08-15: this header
still read *"PARTIAL — guardrail half landed; proof half landed for
REVERSE only (swap 1 of 3)"* after swaps 2 and 3 landed in this same
file's later sections, and its navigation pointer sent readers to
§"Proof half — session 2" as if that were the end of the record. It is
not: §"Proof half — session 2, part 2" (swap 2 landed) and §"Swap 3 …
LANDED; SLICE 1 CLOSED" follow it, and the file ends at §"SLICE 1
CLOSURE". Read it front to back — the sections are in landing order,
and everything before the swap-1 proof section is the ORIGINAL
session-1 record, kept verbatim for the measurement trail.

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
(checked against all nine points). **CORRECTED (audit response,
2026-08-15): it is a BOUND, not a law, and it is tight only at
`n = 0`.** The earlier "tight at even `n`" here was wrong at four of
the five even points — the bound runs 1, 2, 3, 4 steps above the
measurements at `n = 2, 4, 6, 8` (and 38–41 above at odd `n`) — because
the true counts are not affine at all. For comparison
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

* Fuel bound `N = 205·n + 335` — the affine BOUND on the measurements
  recorded in the handoff above (not a "measured law": the true counts
  are non-affine and the bound is tight only at `n = 0`; corrected in
  the audit response, 2026-08-15),
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
* Deletion test — RUN, not asserted (`lean_minimal_hypotheses`, which
  drops each explicit binder and re-elaborates a scratch copy): all
  three binders come back **load-bearing**. The mechanical break for
  both `hn` and `hseed` is the entry equation's two `unorm_of_range`
  rewrites — they are exactly what makes the machine's uint64 argument
  cells equal the `Nat` casts the statement quantifies over — and `hn`
  additionally fails `omega` inside the fuel-bound discharge. Beyond
  the proof, `hn` is the statement-level Go `int` boundary (the v1
  precedent: past `2^63` a `make([]uint64, n)` length wraps negative
  and panics). `lean_verify` on `reverse_ok`: axioms
  `[propext, Classical.choice, Quot.sound]`, source scan clean.

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

### Swap 2 (minmax) — the transcription pack, measured this session

Not built, but taken from "needs probing" to "needs typing". Everything
below is measured with `.tmp/s1/mmprobe.lean`, not predicted.

**Address layout — CORRECTED.** The session-1 table above guessed the
frame contents; the real layout (probe, `n = 2`) is:

| addr | cell | | addr | cell |
|---|---|---|---|---|
| 0 | `n` | | 11 | copy `i` |
| 1 | `seed` | | 12 | copy `$forFirst` |
| 2 | `$res0` (`[8]uint64`) | | 13 | harness `lo` |
| 3 | `$res1` | | 14 | harness `hi` |
| 4 | `$res2` | | 15 | minMax's `s` param |
| 5 | `$c15` (handle) | | 16 | minMax's `$res0` |
| 6 | backing (`[n]uint64`) | | 17 | minMax's `$res1` |
| 7 | `s` | | 18 | minMax's `lo` |
| 8 | setup `i` | | 19 | minMax's `hi` |
| 9 | setup `$forFirst` | | 20 | minMax's `i` (`int`) |
| 10 | `pre` (`[8]uint64`) | | 21 | minMax's `$forFirst` |

`nextAddr = 22`. Note 13/14 are the harness's OWN `lo`/`hi` locals
(`lo, hi := minMax(s)`), not `$c`-temporaries; `enterFrame` allocates
15/16/17 in one step.

**Phase map and exact segment step counts** (every number a difference
between two probe markers):

| segment | steps | from → to |
|---|---|---|
| entry A | 10 | body start → the `$c15` makeSlice apply point |
| makeSlice apply | 1 | conditioned |
| entry B | 42 | → setup loop head (k=53) |
| setup A0 / A1 | 25 / 29 | head → exit test |
| setup body / store / drain | 18 / 1 / 5 | |
| setup exit | 39 | test false → COPY loop head (k=223). NO makeSlice — `pre` is one `.initialization` |
| copy A0 / A1 | 25 / 29 | |
| copy B1 / read / B2 / store / drain | 16 / 1 / 1 / 1 / 5 | identical shape to reverse's copy loop |
| copy exit | 15 | test false → `.retV (sliceH) (.callArgsK ⟨"minMax"⟩ …)` (k=369) |
| **enterFrame** | 1 | `StepKit.stepFn_call_enter` — the ONE program-consulting step |
| minMax prologue | 17 | → the first `s[0]` read apply point |
| read / entry C / read / entry D | 1 / 5 / 1 / 34 | → minMax loop head (k=428) |
| minMax dispA / dispB | 25 / 29 | → the `len(s)` apply point |
| len apply / lessCmp apply | 1 / 1 | conditioned |
| minMax bodyA / bodyB | 11 / 3 | |
| loT / read / loT2 — loF | 12 / 1 / 12 — 9 | the `lo` branch |
| hiB — hiT / read / hiT2 — hiF | 3 — 12 / 1 / 8 — 5 | the `hi` branch |
| exit | 71 | test false → terminal (was 62 in the two-result harness; the third result and the ARRAY copy add 9) |

Everything from `minMax dispA` down transcribes from the shipped
`minmax_harness` layer unchanged except addresses (`mh_*_raw`,
`mh_iter`, `mh_loop` in `Examples/MinMax.lean`) — same Go, same step
counts.

**THE FUEL BOUND IS NOT FREE — read this before writing the induction.**
The handoff's `234 + 186·n` is real and IS a valid uniform bound, but
the naive induction does not reach it. Measured (probe, several seeds):

| n | seed 100 | a wrapping seed |
|---|---|---|
| 4 | 978 | 962 (`2^64-2`), 946 (`2^64-1`) |
| 5 | 1164 | 1148 |
| 8 | 1722 | 1690 |

`234 + 186·n` is the MAXIMUM, hit at the non-wrapping seed; wrapping
seeds are strictly cheaper. The reason: taking either `if` branch costs
exactly 16 extra steps, and **at most ONE of the two can fire per
iteration** — `s[i] < lo` and `s[i] > hi` cannot both hold because
`lo ≤ hi` always. So the per-iteration cost is ≤ 80, not the
branch-uniform 96 that the shipped `mh_iter` bounds.

Consequence: a straight port of `mh_iter`'s `k ≤ 96` gives
`N = 202·n + 218` (verified consistent: equal to `186n + 234` at
`n = 1`, loose by exactly 16 per later iteration). To ship the measured
`186·n + 234` the loop induction must carry the invariant
`minSpec (l.take m) ≤ maxSpec (l.take m)` and use it to rule out the
both-branches-fire case. `minSpec_mem`/`maxSpec_mem` are already in
`Examples/MinMax.lean` and are the natural way to get it. **Either
bound is honest** — `202n + 218` is true and cheaper to prove; if it
ships, say in the gallery that the bound is the uniform worst case and
that the measured law is `186n + 234`, rather than quoting the measured
law as the theorem's.

**The one genuinely new below-statement fact**, probe-pinned and still
unwritten (promotion candidate, ≥2 consumers required before it moves
to `SliceMem` — this is why it was NOT written speculatively this
session): the `pre[i] = s[i]` store target is

```
.chain (.addr (.base ⟨10⟩)) [.int iv .uint64] [.index]
```

— an ADDRESS-rooted chain, so `indexTargetLoc` takes its
`.addr baseLoc` arm, loads the array, bounds-checks with
`arrayIndexNat`, and yields `Loc.index baseLoc i`; `storeLoc` at a
`.index` loc then loads the base array, `arraySet`s, and re-stores at
the base — the same `arraySet` + declared-type re-normalization tail
`storeTarget_slice_u64` already handles. The lemma is a close mirror of
that one (same `harrset`/`hnorm` shape, no `sliceIndexLoc`), and its
two consumers are minmax and wordcount.

**Statement vocabulary still owed**: `goArr8` under the §11 closure
rules (STATEMENT-level, so not a kit module), plus the readback check —
`$res0` is an `[8]uint64` cell, so `loadMany` returns a
`GoValue.array` of 8 elements and the final `with_unfolding_all rfl`
must line `goArr8 (mmFamily n seed)` up with
`mmFamily n seed ++ List.replicate (8 - n) 0`; `mmFamily_length` is
what makes `8 - (mmFamily n seed).length` reduce to `8 - n`.

---

## Proof half — session 2, part 2: swap 2 LANDED, swap 3 handed off

### Swap 2 (minmax S3) — landed

`minmax_ok` is now the relational theorem over `minmax_harness_r`
(`Examples/MinMax/HarnessR.lean`, ~1450 lines). Statement verbatim:

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

* **Fuel bound shipped: `202·n + 218`** — the branch-uniform worst case,
  per the coordinator's default. The measured `186·n + 234` is also a
  true bound (at most one `if` fires per iteration since `lo ≤ hi`) but
  needs that invariant threaded through the loop induction, which buys
  nothing under `∃N`. First attempt with the uniform bound went through
  without a fight, so the tighter one was not pursued. The gallery says
  which is shipped and which is measured.
* Axioms `[propext, Classical.choice, Quot.sound]` on `minmax_ok` and
  `minmax_readout`, `#guard_msgs`-pinned. Deletion test RUN
  (`lean_minimal_hypotheses`): all four binders load-bearing; `hcap` is
  doubly so — it breaks the fuel-bound discharge AND the `preList_full`
  readback that lines the zero padding up with `goArr8`.
* Dispositions: `minmax_ok → minmax_ok_v1`,
  `minmax_readout → minmax_readout_v1`, kept unweakened and re-pinned.
* Cost 4 s / 0.4 GiB (24G-capped single-module rebuild), same as the
  reverse swap, on a 22-cell heap with three loops.
* **New machinery, kept in-module on purpose**:
  `storeTarget_arrayLocal_u64` (the address-rooted `pre[i] = w` store —
  the scoping study's predicted "one new fact family") and
  `normalizeValueForTy_arr8_u64`. Neither is lifted: each has exactly
  ONE consumer, and §12 forbids a lift without two. The second consumer
  is wordcount, so the lift is the first thing swap 3 should do.
* **Promotion shipped**: `stepFn_makeSlice_u64_step` into `StepKit`,
  now that the reverse and minmax S-layers both need it; both
  retrofitted in the same commit as fixture witnesses.
* One shape worth remembering: the `$res0 = pre` epilogue store CANNOT
  reduce definitionally, because re-normalizing an array whose contents
  are a symbolic list is stuck. So the exit is `46 + 1 + 24` with the
  store conditioned on `storeTarget_addr` + the array-normalization
  fact, not one 71-step `rfl`. Any S3 harness returning an array will
  hit the same split.

### Swap 3 (wordcount S3) — NOT built; measured and scoped

Deliberate stop, not a grind: the wordcount subject layer is ~1800
lines across `HarnessSetup`/`HarnessSubject`/`HarnessRun` and the swap
is a full session of its own. Everything below is measured this
session so the next one starts transcription-bound.

**Address layout (probe, `n = 4`, `nextAddr = 32`):** 0 = `n`,
1 = `seed`, 2 = `$res0` (`[8]uint64`), 3 = `$res1`, 4 = `$c…` (handle),
5 = backing (`[n]uint64`), 6 = `w`, 7 = setup `i`, 8 = setup flag,
9 = `words` (`[8]uint64`), 10 = copy `i`, 11 = copy flag,
12 = the harness's `best`, 13 = `maxCount`'s `words` param,
14 = its `$res0`, 15/16 = the `counts` map handle and its `mapData`,
18 = the counting loop's `int` counter, 19 = its flag, then TWO cells
per counted word (21/23/25/27 at `n = 4`) and the range loop's cells at
28–31. The allocator GROWS during the counting loop — that is the
structural difference from reverse/minmax and the reason the subject
layer is generic in `na` to begin with.

**Phase map (probe, `n = 4`, seed 7):** entry 0→53 (identical shape to
minmax: 10 + makeSlice + 42); setup loop heads 53/106/163/220/277 —
**53 then 57 per iteration** (the `seed + i%3` formula costs 4 more
than minmax's `seed + i`); setup exit test 306 → copy loop head 345
(39 steps, same as minmax — `var words` is one `.initialization`);
copy loop heads 345/394/447/500/553 — **49 then 53, byte-identical in
shape to minmax's copy loop**, so `cp_*` transcribes directly;
copy exit → `CALL maxCount` at 593; `maxCount` counting-loop heads
647/727/811/895/979; break 1011; the map-range loop; two returns
(1094, 1123); terminal 1126.

**Step law — NOT affine, and the reason matters.** Measured at seed 7:

| n | 1 | 2 | 3 | 5 | 8 |
|---|---|---|---|---|---|
| steps | 520 | 726 | 932 | 1320 | 1902 |

First differences are 206, 206, then 194 — because the family
`w[i] = seed + i%3` stops adding NEW map entries after the third word,
so the per-element cost drops once the map stops growing. **`206·n +
314` is a valid affine upper bound** (checked at all five points) and
is the number to ship; do not quote a "measured law", because there
isn't a single one.

**The reuse plan — this is an INSTANTIATION job, not a re-derivation.**
`WordCount/CountGeneric.lean`'s `wcLoop_generic` and
`RangeGeneric.lean`'s `wcRange_generic` are already genuinely
placement-generic: parameterized over a state family
`S : List (Int × Nat) → Int → Bool → Heap → Nat → ExecState`, base
addresses (`bArr`/`bMap`/`base0`), the head/cmp/exit continuations and
the env families, with ~15 hypotheses to discharge. Those hypotheses
ARE the raw segments at the new layout. So swap 3 decomposes as:

1. lift `storeTarget_arrayLocal_u64` + `normalizeValueForTy_arr8_u64`
   into `SliceMem` (second consumer now exists — this is the promotion
   the ledger has been waiting on), retrofitting minmax in the same
   commit;
2. transcribe the harness glue at the new layout — entry (10/1/42),
   setup loop (25/29/…/53/57), copy loop (25/29/16/1/1/1/5, verbatim
   from minmax modulo addresses), the `maxCount` `enterFrame` via
   `StepKit.stepFn_call_enter`, and the epilogue with the SAME
   array-store split minmax needed;
3. discharge `wcLoop_generic`/`wcRange_generic`'s hypotheses at that
   layout — the bulk of the work, and the part that is genuinely
   mechanical because the inductions themselves are already proved;
4. post `best = maxMultiplicity words` over the RETURNED array
   (`maxMultiplicity`, then in `Pure.lean` and since the arc-end
   designation in `Examples/Targets.lean` — see the note at the end of
   this record; `Family.lean`'s
   `wcFamily_maxMult : maxMultiplicity (wcFamily n seed) = (n+2)/3` is
   the v1 closed form and is NOT needed by the S3 statement — that is
   the whole point of the swap), `goArr8`-style adapter for the
   returned words, `wordcount_ok/_readout → _v1`.

Probe left in place: `.tmp/s1/wcprobe.lean` (same `trace`/`dump`
interface as the reverse and minmax probes).

---

## Swap 3 attempt (2026-08-14, session 2 part 3): STOPPED before building

Directed to continue; I read the whole target layer, staged the two
lifts, measured the job, and then **stopped without building** because
the honest completion estimate exceeded the budget left. Nothing
half-built shipped. What the attempt bought is below — swap 3 is now
scoped to the individual theorem.

### The lift was staged and then REVERTED — read this before redoing it

`storeTarget_arrayLocal_u64` and `normalizeValueForTy_arr_u64` were
written into `SliceMem` (generalized from minmax's cap-8 form to
arbitrary `N`), minmax was retrofitted to the kit names, and both built
green. **It was then reverted**, because the §12 rule that justifies
the lift is TWO consumers, and wordcount — the second consumer — did
not land. A lift whose second consumer is hypothetical is exactly the
anti-pattern the active-abstraction loop exists to prevent, and the
justification would have been false in the tree.

The work is reproducible in minutes: hoist the two theorems verbatim
out of `Examples/MinMax/HarnessR.lean` into `SliceMem` (just before the
"Slice-value plumbing" section), generalize the array-normalization
lemma's `8` to `N`, leave a thin cap-8 alias in the minmax module, and
**land it in the same commit as the wordcount consumer.** Note
`mem_of_mem_set` is `private` in `SliceMem` — the lifted store lemma
uses it, which is fine in-file but is why the lemma cannot simply live
in an example module without also un-`private`ing that helper (minmax
uses the public `mem_set_of_mem` instead).

### `wordcount_harness_r`'s `Func` — dumped, so it need not be re-probed

`$c11` is the slice temp; results are `#[$res0 : [8]uint64, $res1 :
uint64]`; the setup body is `wordcountHarnessFunc.shBody`'s shape with
`.add (.var "seed") (.mod (.var "i") (.intLit 3 .uint64))`; the copy
store target is `.addr (.indexAddr (.ref "words") (.var "i"))` — a
`.ref`, i.e. the same ADDRESS-rooted chain minmax's `pre[i]` uses, so
`storeTarget_arrayLocal_u64` applies unchanged; the call is
`.call #[.var "best"] ⟨"maxCount"⟩ #[.var "w"]`; the epilogue is
`$res0 := words; $res1 := best; return`.

### The address remap, old harness → r-harness

`wordcount_harness`'s layer uses front cells 0–15 with the symbolic
region from 16. The r-harness uses front cells 0–19, symbolic from 20:

| old | new | cell |
|---|---|---|
| 0,1 | 0,1 | `n`, `seed` |
| — | 2 | `$res0` (`[8]uint64`) — NEW |
| 2 | 3 | the scalar result (now `$res1`) |
| 3,4,5 | 4,5,6 | handle, backing, `w` |
| 6,7 | 7,8 | setup `i`, setup flag |
| — | 9,10,11 | `words` array, copy `i`, copy flag — NEW |
| 8 | 12 | the call temp (now named `best`) |
| 9,10 | 13,14 | `maxCount`'s `words` param, its `$res0` |
| 11,12,13 | 15,16,17 | `$c0` map handle, `mapData`, `counts` |
| 14,15 | 18,19 | the counting loop's `int` counter, its flag |
| base0 16 | base0 20 | the symbolic dead region |

So the generic instantiations become
`wcLoop_generic (σR …) ws 5 16 20 …` (was `4 12 16`) and
`wcRange_generic envRBR kRR (σR …) … 20 …` (was `16`).

### The exact work list (this is the whole job)

1. The two lifts, WITH this consumer, in one commit.
2. Harness glue at the new layout — entry (10 / makeSlice / 42), the
   setup loop (25 / 29 / body / store / 5, **53 then 57 per iteration**
   because of the `%3`), the setup exit (39 → copy head), the copy loop
   (25 / 29 / 16 / 1 / 1 / 1 / 5 — transcribes from minmax's `cp_*`
   verbatim modulo addresses), the `maxCount` `enterFrame` via
   `StepKit.stepFn_call_enter`.
3. Re-state ~20 subject segments at the new front — the shapes are
   `HarnessSubject.lean`'s `wcH_segA0/A1/cmp/C1…C11/X0/X0b/X0c`, all
   one-line `with_unfolding_all rfl` except `C3`/`C6`/`X0c`, which are
   composed from `StepKit`'s `stepFn_storeK_nil`/`stepFn_seqn_splice`/
   `stepFn_seq_pop` glue.
4. Discharge the two generic layers' hypotheses. `wcLoop_generic` takes
   nine: `hIter` (the composite counting iteration — `HarnessRun`'s
   `wcH_count_iter`, the single biggest piece at ~140 lines), `hA1`,
   `hX0`, `hInitBest`, `hX0b`, `hStBest`, `hX0c`, `hSnap`,
   `countsList_norm`. `wcRange_generic` takes six: `hEnvBest` (a `rfl`),
   `hPick`, `hR4b`, `hVarC`, `hVarBest`, `hStB`. All of these exist at
   the old layout in `HarnessRun.lean` and port by address.
5. The exit phase (`frontXH`/`σXH` and `X1H`/`X2aH`/`X2bH`/`X2cH`) plus
   the array-store split for `$res0 := words` — the SAME conditioned
   step minmax needed, because a symbolic-array value cannot
   re-normalize definitionally.
6. Statement layer: post `best = maxMultiplicity words` over the
   RETURNED array (`maxMultiplicity` — `Pure.lean` when this was
   written, `Examples/Targets.lean` since the designation hoist), a
   `goArr8`-style
   adapter, `wcFamily` OUT of the statement (`Family.lean`'s
   `wcFamily_maxMult : maxMultiplicity (wcFamily n seed) = (n+2)/3` is
   the v1 closed form and is deliberately NOT needed by the S3 claim —
   that is the swap's whole point), `wordcount_ok/_readout → _v1`.
7. Bound: **`206·n + 314`**, quoted as an affine upper bound, with the
   non-affine finding stated (first differences 206, 206, 194 — the
   family stops adding map entries after the third word). Never present
   it as "the measured law".

Honest size: ~1200–1400 lines, i.e. the same order as the minmax module
built this session. It is a session's work, not a slice-of-a-session's.

### A gallery obligation to carry into swap 3

The claim will be `best = maxMultiplicity words` over RETURNED data,
and `maxMultiplicity` must be ORDER-INVARIANT for that to mean what a
reader thinks it means — the map-range loop visits entries in a
nondeterministic order, and the theorem holds at EVERY choice stream
precisely because the spec function does not depend on that order. Say
so in the entry; it is the teaching point this example exists for, and
it is the one place where the S3 "relation over returned data" framing
could mislead if left implicit.

---

## Swap 3 (wordcount S3) — LANDED; SLICE 1 CLOSED (2026-08-14, session 3)

### What landed

`wordcount_ok` is now the S3 relational theorem over
`wordcount_harness_r` (`Examples/WordCount/HarnessR.lean`, ~2240 lines).
Statement verbatim:

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

* **`wcFamily_maxMult` is not used at all** — the closed form `⌈n/3⌉`
  leaves the claim entirely, which is the swap's whole point. The
  family survives only as the existential's witness.
* **NO `1 ≤ n`.** Unlike minmax, `maxCount` of an empty slice returns 0
  rather than panicking, so the hypotheses are just the cap and the
  seed's type. Deletion test RUN (`lean_minimal_hypotheses`): both are
  load-bearing — `hcap` breaks the fuel-bound `omega` AND the
  `wcPre_length` side condition of the array store; `hseed` breaks the
  entry equation's `unorm_of_range` on the seed argument.
* Axioms `[propext, Classical.choice, Quot.sound]` on `wordcount_ok`
  and `wordcount_readout`, `#guard_msgs`-pinned in `Audit/WordCount.lean`
  (green); `lean_verify` source scan clean. No `sorry`, no
  `native_decide`, no project axioms.
* Dispositions: `wordcount_ok → wordcount_ok_v1`,
  `wordcount_readout → wordcount_readout_v1`, kept unweakened in
  `Examples/WordCount.lean` with their corpus rows, both re-pinned.
* Cost **10 s / 2.0 GiB** (48G-capped, `scripts/proof-costs`) — under
  the 2.5 GiB bar but ~5× its siblings (reverse and minmax are ~0.4
  GiB). The honest reason: this module carries ~30 `with_unfolding_all
  rfl` segments over a **20-cell front containing two 8-element ARRAY
  cells and a `mapData` cell**, where minmax's 22-cell front is almost
  all scalars. The expectation of ~0.4 GiB recorded in the handoff was
  wrong for this example; the number is recorded, not explained away.

### PROGRAM-generic throughout, as designed

Every raw segment is stated over `wSt σ H na`; the pinned program is
unfolded exactly TWICE (the lowering pin `wordcountHarnessR_pin`, and
the single `enterFrame` discharge `r_enterFrame_fact` at the
`maxCount(w)` call). This mattered more here than anywhere: the same
example's `EmptyRun` was the 50.8 GiB blocker precisely for not doing
it. The subject phase is an INSTANTIATION of `wcIter_generic` /
`wcLoop_generic` / `wcRange_generic` at `bArr = 5`, `bMap = 16`,
`base0 = 20` — the third placement those layers now serve.

### Transcription rate, and the one correction

The handoff did its job: of ~30 raw segments, **all but one closed by
`with_unfolding_all rfl` on the first attempt**. The single failure was
not a step count but an ADDRESS BINDING: `r_prologue_rawR`'s output
front ties cell 0 to `((n : Nat) : Int)` while its input `rHeapMFrame`
had a free `nv`, so the two could not be definitionally equal. Fixed by
instantiating the lemma at `nv := ((n : Nat) : Int)`, exactly as the
`wordcount_harness` layer's `σWCallg` already does. Divergence guard:
not triggered anywhere.

Two step counts differ from the minmax template and are recorded so the
next S3 harness does not copy the wrong ones:

| segment | minmax | wordcount r | why |
|---|---|---|---|
| copy exit → drained `callArgsK` | 15 | **13** | minmax declares `lo`+`hi` before its call, this declares only `best` |
| epilogue around the array store | 46 / 1 / 24 | **17 / 1 / 15** | minmax's frame exit carries two scalar results, this one |

The subject prologue (frame entry → counting head) is **1 + 51**: the
conditioned `StepKit.stepFn_call_enter` step, then 51 program-free
steps. Setup loop 53 then 57 per iteration, copy loop 49 then 53 — both
exactly as the handoff measured.

### THE FUEL BOUND — the handoff's number could NOT be shipped

The handoff said to quote `206·n + 314`. That number is real but it is
**a bound on the MEASUREMENTS, not a provable bound for this proof**,
and the two must not be conflated. What the induction actually yields is

```
53 (entry) + 25 + 57n (setup) + 39 + 25 + [53n + 65] (copy+call+prologue)
  + 27 + [84n + 23] (counting) + [24·m + 1] (range) + 44 (exit)
```

with `m = (countsList ws).length ≤ n`, i.e. **`N = 218·n + 302`** — which
is what shipped. It exceeds `206·n + 314` for `n ≥ 2`. Two sources of
slack, both branch-uniform worst cases:

* `wcRange_generic` charges **24** steps per range iteration (the `then`
  branch, where `best` is rewritten); the `else` branch costs 12. At
  `n = 2` the run takes 37 range steps where the bound charges 49 —
  exactly the 12-step gap.
* the snapshot length is bounded by the word count (`m ≤ n`), not by the
  **three** distinct values this family produces. Bounding `m ≤ 3`
  instead gives `194·n + 374`, which is tighter for `n ≥ 6` and looser
  for `n ≤ 4`; neither dominates, and neither equals `206·n + 314`.

So the record is: **shipped `218·n + 302`; measurement envelope
`206·n + 314`, tight at `1 ≤ n ≤ 3`; and there is NO measured law** —
the true counts are not affine (first differences 218, 206, 206, 194,
because the family stops adding map entries after the third word).
CORRECTED in the audit response (2026-08-15): the tight range excludes
`n = 0`, where the envelope sits 12 steps above the measurement — the
measured table above starts at `n = 1`, which is how the `n ≤ 3`
phrasing slipped in. All three
facts are stated in the theorem docstring and the gallery, and none is
presented as another. This is the same shape as swap 2's
`202n + 218` vs `186n + 234`, and the same resolution.

### Promotion (form note §12): the two staged lifts SHIPPED

Landed in the commit immediately before their second consumer, in one
series, so the §12 justification is true in the tree at every point:

* **`SliceMem.storeTarget_arrayLocal_u64`** — the ADDRESS-rooted
  `a[i] = w` store on an array-typed local, generalized from minmax's
  cap-8 form to arbitrary `N`. Consumers: minmax's `pre[i] = s[i]` and
  wordcount's `words[i] = w[i]` (the same `.indexAddr (.ref x)` chain).
* **`SliceMem.normalizeValueForTy_arr_u64`** — the array-normalization
  side condition, `8` generalized to `N`. Consumers: both S3 epilogue
  `$res0 := <array>` stores.

Minmax was retrofitted in the same commit and is the fixture witness;
its local names survive as one-liners over the kit lemmas, so its
statements and pins are untouched. The `mem_of_mem_set` privacy gotcha
the previous session flagged is a non-issue once the lemma lives IN
`SliceMem` (it uses the in-file private directly).

Also promoted earlier this slice: `StepKit.stepFn_call_enter`, now at
FOUR consumers (EmptyRun + reverse + minmax + wordcount — the count
read "three" until the 2026-08-15 audit response found MinMax/HarnessR
missing from it), and `StepKit.stepFn_makeSlice_u64_step` at three
(reverse + minmax + wordcount).

### Promotion ledger — FINAL STATE for slice 1

| candidate | consumers | disposition |
|---|---|---|
| `stepFn_call_enter` | 4 | **LIFTED** to `StepKit` (swap 1) |
| `stepFn_makeSlice_u64_step` | 3 | **LIFTED** to `StepKit` (swap 2) |
| `storeTarget_arrayLocal_u64` | 2 | **LIFTED** to `SliceMem` (swap 3) — already `N`-generic where it stood |
| `normalizeValueForTy_arr_u64` | 2 | **LIFTED** to `SliceMem` (swap 3), genuinely generalized (`arr8` → `arr`, cap 8 → `N`) |
| `goArr8` | 2 | **NOT lifted — deliberately, and permanently** |
| the copy-into-observation loop schema | 3 instances | **NOT lifted — nothing shareable left** |

The two non-lifts are decisions, not deferrals, and both are recorded
because a later session will otherwise re-propose them:

* **`goArr8` must stay duplicated.** It is STATEMENT vocabulary, and
  §11's closure rule is that a headline must be readable from the
  example's own module over base definitions. Hoisting a 3-line adapter
  into a kit module to save six lines would make both headlines read
  through a shared import — defeating the exact rule the definition
  exists to obey. Two identical copies is the correct cost.
  **SUPERSEDED IN PART by the arc-end designation (`e4202039`), noted
  here in the audit response (2026-08-15) so the ledger is not read as
  current:** both copies of `goArr8` now live in
  `Examples/Targets.lean`, because designating the two headlines forced
  their whole statement vocabulary into a def-only module the Comparator
  Challenge can import. The CONCLUSION above still stands — there are
  still two definitions, one per example namespace, not one shared
  adapter — and the §11 closure rule is still what forbids merging them;
  what changed is the file they sit in, re-justified in that commit.
* **The copy-loop schema has three instances and an EMPTY shareable
  part.** The raw segments (`cp_A0/A1/B1/B2/D/X`) are placement-concrete
  by the measured decision recorded in swap 1 (address-generic segments
  cannot close by `rfl` at all when nearly every step touches a cell —
  ~10× the source for a layer that already costs seconds). What remains
  is a ~60-line composition per example whose pure layer needed nothing
  new in any of the three cases — reverse reused `suList`, minmax
  reused `setupList`, wordcount reused `wcFamily`/`wcFamilyZ_range`. A
  generic layer here would cost more in E-form hypotheses than the three
  transcriptions it replaces. Closed.

### SLICE 1 CLOSURE

All three spec-style swaps have landed. `reverse_ok` is the S1
copy-relational headline over `reverse_harness_v`, `minmax_ok` and
`wordcount_ok` are the S3 relational headlines over `minmax_harness_r`
and `wordcount_harness_r`; in every case the postcondition now relates
RETURNED DATA and the setup family has left the statement (for
wordcount, so has the solved closed form). All three old headlines are
kept unweakened as `_v1` pairs with their corpus rows and axiom pins —
nothing was superseded, weakened, or deleted, and no corpus case was
edited or skipped. The guardrail half shipped first, as the repo's own
rule requires: every harness was real, compiled, differentially green
Go before a line of its proof existed.

Totals: three new proof modules — `Reverse/HarnessV.lean` (~1050
lines, 4 s / ≤0.4 GiB), `MinMax/HarnessR.lean` (~1490 lines, 4 s / 0.4
GiB), `WordCount/HarnessR.lean` (~2240 lines, 10 s / 2.0 GiB) — all
PROGRAM-generic, all axiom-clean at Lean's classical trio, all three
deletion-tested with every binder load-bearing, all `#guard_msgs`-pinned
in their Audit shards. Four kit lemmas promoted under §12, each with its
consumers retrofitted in the promotion commit; two promotion candidates
closed as permanent non-lifts with reasons. `scripts/ci` PASS per commit
(the corpus is untouched by the proof half, so the full 1560-case record
recorded at `cba113c` stands); `scripts/render-gallery` green, with all
three entries re-rendered — including wordcount's order-invariance
paragraph, which the swap made load-bearing for READING the claim rather
than merely for proving it. `scripts/comparator-judge` is not owed: none
of the three headlines is on the statement-TCB designated list.

The honest limits carried forward, unchanged and unhidden: the S3 cap
`n ≤ 8` is a toy bound visible in the Go; `∃ pre` / `∃ words` are still
family-DETERMINED and the statements merely avoid saying so; making the
inputs genuine ∀-data is the ghost rung-1 annotation, which remains
designed and not built. That annotation is the natural next slice — the
S3 harnesses were shaped to be exactly the form it plugs into.

### Superseded by the arc end, noted in the audit response (2026-08-15)

Two facts recorded above moved at the arc-end designation (`e4202039`),
so read them with this note attached rather than as current:

* **The statement vocabulary left the example modules.** The designation
  hoisted the transitive definition closure of the eight designated
  headlines into the def-only `proofs/GoLeanProofs/Examples/Targets.lean`
  — including `multiplicity`/`maxMultiplicity` (recorded above as
  `Pure.lean`'s), `minSpec`/`maxSpec`, both `goArr8` copies, and every
  pinned harness `Func`. Definitions are verbatim and in their original
  namespaces, so every reference in this record still resolves; only the
  file changed.
* **The hoist's size, counted rather than remembered:** the module holds
  **20** top-level definitions (19 `def` + one `abbrev`, `setupBody`).
  `e4202039`'s message says 18 — it counts the two same-named `goArr8`
  defs once, though they are two distinct definitions in two namespaces
  and deliberately stay that way (unifying them would change what the
  two statements say). Both numbers describe the same module; 20 is the
  one you get by counting the file.
