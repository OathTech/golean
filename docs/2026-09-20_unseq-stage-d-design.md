# Stage D of the evaluation-order model v2.1 — exploration economics: the workload ladder and route α (2026-09-20)

[AGENT] worker, lane `core/unseq-stage-d-0920` (worktree `.claude/worktrees/unseq-stage-d`, base main
`f14a05e5` → rebased onto `10d2f2dc`). Authority: `docs/2026-09-16_evaluation-order-model-v2.md` §3.5–3.6 (the
enumeration route: β = the default DFS explorer, α = certify the `unseqNext` pick in the dedup engine), §6 (what a real
cost measurement reports), §7 row D; review R1 (no ordering reduction — none is made here), R5 (one measured route;
unique states beside paths). Sequencing [USER] 2026-09-18 «(1) agreed», relayed; Stage C landed 2026-09-20 ([USER] «land
it», relayed). No new [USER] decision is needed by this stage; the one open choice it poses is §5. Numbers: the evidence
README `docs/evidence/2026-09-20_unseq-stage-d/README.md` (every figure copied from a named log; regeneration commands
there). Engine facts stated here are read from `GoLean/EnumDedup.lean` / `GoLean/GoCore/EnumDedupCheck.lean` at the
lane tip.

## 1. The ladder (D0) — what is measured, and the budgets that are the exit criterion

Rungs (v2.1 §7 row D / review R5), each measured on route β (`CLI.explore`: fuel 2 000 000, width 8, sites 64, cap
4096, work 50 000 000 — Stage B's parameters) and on route α (`CLI.runDedupObservations`: the same caps, work
50 000 000), silent AND printing variants, one process per rung under `/usr/bin/time -v`:

| rung | shape | paths (β) | budget derivation |
|---|---|---|---|
| `loop N` | N width-2 sweeps in a `for` loop (Stage B's shape), N = 1..12 (13 printing = the designed refusal) | 2^N | steps ≈ 2^N × 165 (silent); the cap 4096 is hit at N = 13 printing — REFUSED by name, never truncated (N3) |
| `wide k` | ONE sweep, k unordered invocations feeding a sink, k = 2..8 | k! | k = 8: 40 320 paths, 4.1 M steps, ~4 m 15 s on β (254–256 s in two runs) — the last rung β closes under 50 M work; k = 9 would not |
| `nest M` | a loop of M iterations, each ONE width-3 sweep, M = 1..5 | 6^M | M = 5: 7 776 paths |
| corpus: the E13 family | `builtins/e13-sibling-panic-order/*` (65), `builtins/len-vs-call-order/*` (31), `binop-order/operand-panic-vs-call/*` (3); the Stage C pilot `evalorder/unseq-pilot/*` (13), `evalorder/unseq-const-cell/*` (3); the seven lane-moved rows' packages | per row: the baseline's own enumeration | the rows' declared `width`/`sites`; α at work 20 M |
| corpus: `spec-examples-stmt/continue-label` | a 3×4 nested loop with one sweep per iteration + three `enc` reads (w = 18) | 32 805 leaves on β (39.6 M steps, just under 50 M) | the ONE corpus rung β nearly cannot close; α closes at 5 122 unique states |
| the raft twin (control) | `multipkg/mini-raft-twin/*` (5 rows) | — | 0 `unseq` nodes (Stage C census); traced anyway: 569 consumptions, all `appendSpill`, 0 `unseqNext`, observation invariant over 6 streams |

Route β's budget statement (RECORDED, the exit criterion for D0): every rung above closes within the stated caps EXCEPT
`loop 13 printing` (the cap-4096 refusal, by design) and `wide 7 printing` (5 040 members > 4 096, the same refusal);
β's cost is the path product — steps double per sweep, wall doubles per sweep (16–23 ms/path at N = 12, probes
included), RSS flat (~760–780 MB, the loaded oleans). The rungs β cannot close economically — `wide 8` (~4 m 15 s),
`loop 12` (66–94 s), `nest 5` (88 s), `continue-label` (39.6 M steps) — are route α's motivation, measured; α closes
each in ≤ 37 s (`wide 8`) and the rest in < 1 s.

## 2. Route α (D1) — the `unseqNext` pick certified in the dedup engine

**The fact the construction rests on:** the pick's bound is `|ready|`, a function of the stepping goroutine's own frame
(`unseqNextBound : Config → Nat`, Machine.lean, = `(g.ready st).length` at `.next (.unseqK g _ st _ _ .pick _)`, 0
elsewhere) — it reads NO store and NO other thread (`seqConsumption_unseqNext`: for every store σ the accountant
reports `(.unseqNext, |ready|)` iff `2 ≤ |ready|`). So the checker can enumerate the pick's branches from the
configuration alone: `innerVecs` gains the class **N-PICK** — at a `consumesUnseqNext` frame with `2 ≤ unseqNextBound c`,
one singleton vector `[p]` per `p < |ready|`; at `consumesUnseqPanic`, `[[0], [1]]` (bound 2, constant — the SAME shape:
a `stepFn`-path pick with a configuration-determined bound, so the legacy site is certified by the same lemma). A
bound-≤-1 pick pops nothing (G-U) and is now OBLIVIOUS: `poolThreadOblivious` answers `decide (unseqNextBound c ≤ 1)`
there instead of a blanket `false` (the all-forced graphs of the fmt shims and the goose `ok = ok && …` chains are
thereby certifiable too).

**The proofs (no theorem weakened; `checkCert_slowObs`'s STATEMENT is unchanged — it certifies more certificates):**
`stepThread_stepFn_path` (MultiStreams: the goroutine-step on the plain `stepFn` path IS `stepFn`'s step wrapped, as an
equation); `stepThread_pick_run` (the `stepFn` analogue of `stepThread_l4_run`: a successful explicit pick `[p]` at a
bound-`b` `stepFn`-path site determines the step under every stream whose raw pop at `b` is `p`, through
`stepFn_consumption_some`); `stepThread_oblivious` extended at the bound-≤-1 pick (through `stepFn_consumption_none`);
`stepThread_total_covered` (EnumDedupSound) gains the two N-PICK cases; `consumesUnseq{Next,Panic}_shape`,
`seqConsumption_unseq{Next,Panic}` (MachineSound). Scheduler audit: 35 required theorems, classical trio only.
The refusal texts in `EnumDedup.refusalReason` for the two sites are now unreachable and say so. The CLI's dedup seed is
factored (`CLI.dedupSeed`) so the tests certify from the CLI's own `m₀`.

**What α closes (the evidence README's tables):** on the corpus rungs 100 of 153 rows CLOSE and certify; on every one
the certified member SET equals the DFS's set exactly (`alpha-vs-beta.tsv`, 100/100 SAME) and every membership row's
certified count equals its declared `members=`. `continue-label`: 5 122 unique states / 5 145 edges / 24 merges vs β's
32 805 paths — the singleton CERTIFIED. The synthetic rungs (silent): `loop N` unique states 154 + 115·(N−1) — LINEAR — against β's 2^N paths (1 419 vs
4 096 at N = 12; 0.49 s vs 66 s); `nest M` 372 + 315·(M−1) against 6^M (1 632 vs 7 776 at M = 5); `wide k` 21 887
states against 40 320 paths at k = 8 (37 s vs ~4 m 15 s) — exponential in k (the done-set lattice) but far below k!. What α does NOT close, by name: 42 rows whose sweep PRINTS (the engine keys
nodes on state and refuses an output event — the standing G-OUT limit, not a pick limit; §5), 8 rows whose own
refusal fires at node 0 (the BUG-102/BUG-104 designed reds — the machine refuses, not the engine), 3 rows on
pre-existing refused shapes (`mapIterK` ×1, `appendSpill` ×2). BUG-065's 16 non-certifiable strict rows refuse on
BUDGET or on `appendSpill`/scheduling shapes, never on the `unseq` pick — D1 changes shape acceptance only, so none
closes; recorded, none forced.

## 3. Lane moves (each NAMED; the rules of `docs/coverage-suite-structure.md`)

- `spec-examples-stmt/continue-label` — strict `depth=128` → `lane=confluent`, `engine=dedup` (width 4, sites 64, work
  200 000; nodes + edges = 10 267 at the lane tip): the spot check becomes a certificate — |set| = 1 over ALL picks,
  theorem-backed (`checkCertM_slowObs`). The only row the rules license: the strict-lane depth guard fired there
  (w = 18 > the fixed streams), the observation is a silent singleton, and the dedup engine closes it.
- NOT moved, recorded: the 41 membership rows that certify with their declared sets could carry `engine=dedup`
  (certified membership, as `google-search` does); the rules license no such move for rows the DFS already closes in
  milliseconds, and it is not proposed. The strict E13/pilot rows that close are covered by the three fixed streams
  (no guard firing) — no move.

## 4. Accounting and representation (D2)

- Accountant: every β enumeration in the ladder and every corpus row runs under the explorer's TWO-SIDED sentinel
  (`CLI.lean`, `stepNeeds`/`stepNeedsSeq` vs the real pop) — 0 drift alarms across the ladder (β logs) and the twin
  trace's validator (569 consumptions, 0 mirror/accountant/sentinel alarms). `seqConsumption_unseqNext` is the
  accountant's exactness at the new site as a theorem (the same `|ready|` the checker enumerates).
- Scope/deallocation (for C4, NOT implemented here): the `heap` rung runs the canonical tape through `execProgLoop` and
  reads the final store: `loop N` allocates exactly 4 cells per sweep (2 binder cells `$a`,`$b` + 2 callee result cells)
  and reclaims none — heap 3 + 4N (measured N = 1..12, table in the README); the dedup engine's node states inherit the
  growth (no two iterations' states can merge — the loop counter differs anyway), so the cost is linear memory per
  sweep on every engine and a strictly larger node key. The fmt shim loops (`out += goleanShimFmt…`) carry one all-forced
  graph per iteration: 0 picks, the same per-iteration cell allocation.

## 5. Open choices ([AGENT], the alternative named) and what Stage E needs

- OUTPUT-KEYED NODES: the 42 printing rows are refused by the engine's G-OUT rule, not by the pick. Alternative (a):
  extend `DedupNode` with the output trace and `Obs` with output — a new spec (`SlowObs` has no output vocabulary), a
  changed `checkCert_slowObs` statement, a bigger slice; (b) keep printing rows on the DFS (their budgets are small: the
  E13 printing rows enumerate in < 30 ms each). [AGENT] chooses (b) here and records (a) as Stage E's option if a
  printing sweep family outgrows β. Not PENDING [USER]: no claim changes either way.
- Stage E inherits: route α is live for every `unseq` pick — a migrated family whose rows are silent can be certified
  as they land; printing families ride β with the recorded per-row budgets; `unseqPanic`'s certification retires with
  the site itself.
