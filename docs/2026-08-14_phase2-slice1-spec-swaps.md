# Examples phase-2, slice 1 — spec-style swaps: slice record (2026-08-14)

Status: **PARTIAL — guardrail half landed, proof half NOT landed.** Read
this before continuing the slice; it is the handoff.

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
| wordcount | — | S3 relational | — (REVERTED, see below) | — |

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

Predicted address layout (probe before trusting): 0=`n`, 1=`seed`,
2=`$res0`, 3=`$c5` (s handle), 4=s backing, 5=`s`, 6=setup `i`,
7=setup flag, 8=`$c6` (t handle), 9=t backing, 10=`t`, 11=copy `i`,
12=copy flag, 13=reverse's `s` param, 14/15=reverse's `i`/`j`,
16=reverse's flag, 17=`ok`, 18=test `i`, 19=test flag.

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

Predicted layout: 0=`n`, 1=`seed`, 2=`$res0`, 3=`$res1`, 4=`$res2`,
5=`$c15` (handle), 6=backing, 7=`s`, 8=setup `i`, 9=setup flag,
10=`pre`, 11=copy `i`, 12=copy flag, 13+=minMax's frame.

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
