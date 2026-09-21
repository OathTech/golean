# Adversarial audit of Stage D — route α (the `unseq` pick certified in the dedup engine) and the workload ladder (2026-09-20/21)

**VERDICT: MERGE-CLEAN.** No WRONG-CLAIM, no UNSOUND-PROOF/WEAKENING/COHERENCE-GAP, no UNLICENSED-OPTIMIZATION (R1), no
FAIL-OPEN. Six records-class items (F1–F6: two mislabelled numbers/attributions, one caption-precision nit on the lane
the row moved to, one inert-parameter sentence, one precedent-evidence gap that this audit supplies, one scope sentence
for the [AGENT] deferral) — none changes a claim, none blocks the merge; each can ride the train's 5a records commit or a
follow-up records edit.

[AGENT] auditor (Claude, Stage D auditor), branch `review/unseq-stage-d-0920`, worktree
`.claude/worktrees/audit-unseq-stage-d`, checked out at the candidate tip `e34fc8ec` (`core/unseq-stage-d-0920`: runtime
commit `95c6c052`, records `c253cadc`, addendum `e34fc8ec`) over main `10d2f2dc`. Ordered by [USER] Mike, 2026-09-20,
verbatim, relayed by the [AGENT] coordinator — cited as relayed, not firsthand: «Great, launch the audit». Nothing on the
candidate or on `main` was edited; nothing was merged or pushed. Evidence (small; 12 files, 67 KiB):
`docs/evidence/2026-09-20_unseq-stage-d-audit/`. Every Lean/lake command ran through `scripts/capped`; every exit code
below is the captured one; a killed run is reported as a refusal, never a result.

Setup: `scripts/setup-deps --from /home/dev/projects/golean` (EXIT 0: go, goose, raft pinned); one plain `cp -a` of the
candidate worktree's `.lake` at identical source (the only read of that worktree); `scripts/capped lake build` EXIT 0
(96 jobs, 0 warnings). The resulting `golean` is sha256 `0681abc6…` = the candidate's own runtime-commit binary (the
evidence README's "runtime commit's binary"); main's is `90024323…` (read-only, `/home/dev/projects/golean/.lake/build/bin/golean`).
The ladder, the corpus scan and the set comparison therefore ran here on the binary the GATE ran on, not on the lane's
"D1 binary" (`a5c1aca0…`, one docstring earlier) — closing that small provenance gap in the record.

## 1. Findings (by severity; there are none above RECORDS-CLAIM)

**F1 — RECORDS-CLAIM (minor): "BUG-065's 16 rows" is a misattribution.** The design note §2 («BUG-065's 16
non-certifiable strict rows refuse on BUDGET or on `appendSpill`/scheduling shapes») and the handoff §4 («BUG-065's 16
rows: none closes») attribute sixteen rows to BUG-065. `docs/BUGS.md` BUG-065 (line 3697) has ONE Cases row,
`goroutines/worker-pool/sum` — a `lane=confluent` row, not strict. The sixteen are the depth-guard "standing consequence"
`depth=N` rows of `docs/coverage-suite-structure.md` (5 scheduling: `prime-sieve/{five,eight}`, `worker-pool/shared-feed`,
`waitgroup-workers-join/workers-join`, `parallel-search-replace/search-replace`; 11 noodler), recorded there as FINDINGs,
not as BUG-065's. What I did: read both; spot-checked the negative claim on three of them with `--engine dedup` at work
20 M under the cap — `spec-examples-stmt/prime-sieve/five` KILLED by the memory cap after 224 s (a refusal by the cap);
`goroutines/worker-pool/sum` «dedup work budget exceeded (9538077 nodes, 10461924 edges, …)» after 464 s (BUG-065's
recorded shape, refused by name); `goroutines/worker-pool/shared-feed` «dedup work budget exceeded (9363137 nodes, 10636864 edges, …)» after 46 s (refused by name). The substantive claim ("none closes;
budget/shape refusals, never the pick") holds where checked; the label is wrong. Why it matters: a reader following
"BUG-065" to BUGS.md finds one row and a different lane. Disposition (PROPOSED, records-only): replace "BUG-065's 16
rows" with "the sixteen `depth=N` rows of the depth-guard standing consequence (coverage-suite-structure.md); BUG-065's own
row `worker-pool/sum` refuses on budget as recorded".

**F2 — RECORDS-CLAIM (minor): the design note's β budget derivation is mislabelled.** §1's table: «steps ≈ 2^N × 165
(silent)». The evidence README's own tables give silent `loop 12` = 585 623 steps / 4096 paths = 143.0 steps per path (I
reproduced 585 623 at N = 8 → 36 503 / 256 = 142.6); 165–167 per path is the PRINTING variant (683 903 / 4096 = 167.0).
No claim depends on the constant (the README's numbers and the exit criterion are the measured tables), but a
derivation line that names the wrong variant is exactly the "number unanchored" the handoff §8(v) asks about.
Disposition (PROPOSED): «≈ 2^N × 143 (silent) / × 167 (printing)».

**F3 — NIT (caption precision; the (f) question): the `confluent` lane's caption under-describes what the moved row
certifies.** `docs/2026-08-04_nondeterminism-doctrine.md` §"Per-lane epistemic captions": «confluent — PASS =
enumerator-certified |set| = 1 over ALL registry-point schedules»; `docs/coverage-suite-structure.md` rule 3 says the
same («the enumerator certifies |set| = 1 over all registry-point schedules»). `spec-examples-stmt/continue-label` is a
single-goroutine program: my trace shows its ONLY consumption site is `unseqNext` (18 bound-≥-2 draws on the default
stream, 10–18 on the other five; zero `l1Sched`/`postOp`/`backEdge` draws), so what `checkCertM_slowObs` certifies there
is |set| = 1 over ALL choice streams — evaluation-order picks, not schedules. The claim made is STRONGER than the caption
(streams ⊇ schedules), so nothing is over-claimed; but the lane's meaning has silently widened from "schedule-
independence" to "stream-independence". The move itself is LICENSED by rule 3 as written (the guard fired at w = 18; the
observation is a silent singleton; the engine closes it — rule 3 names `lane=confluent` as the first remedy), and it is
NAMED in the depth-guard section and the baseline header as the rules require. Disposition (PROPOSED, records-only):
one clause in the caption and in rule 3 — «over all choice streams (scheduling AND evaluation-order picks; on a
sequential row the latter alone)». The D9 lane taxonomy's caption is a doctrine text; I flag the wording for the
[USER]'s eye rather than treating it as mine to change.

**F4 — NIT: `width=4,sites=64` are inert on an `engine=dedup` row, and the row comment argues from them.** The dedup
path hands `EnumDedup.buildCert` only `cfg.workCap` (`GoLean/CLI.lean:1533`–`1540`); `maxWidth`/`maxSites` are echoed in
the stats line and otherwise unread. The moved row's comment («width 4 covers the picks' bounds (2–3)») and the design
note §3 describe a knob the engine never consults — the checker enumerates exactly |ready| branches whatever `width`
says (that is the whole point of N-PICK, and the M4/M9/M11 controls below confirm it). Every pre-existing dedup row
carries the same inert pair, so this is consistent practice, not an inconsistency. Disposition (PROPOSED): reword the
sentence («width/sites are the harness's schema fields; the dedup engine's branching is |ready| by construction»).

**F5 — RECORDS (precedent evidence): the confluent-move precedent recorded 20 gc draws; this move records none.**
The depth-guard section's earlier confluent moves each record «20 gc draws each (plain/-race alternating) inside the
singleton». The Stage D move records «gc's draw is the singleton on every run» (the gate's confluent path draws once,
then the 3-stream strict differential). Supplied here: 20 `go run` draws of the harness's generated main (GOMAXPROCS=1
×10, GOMAXPROCS=8 ×10) — 20/20 the certified singleton (`gc-replay-gomaxprocs.tsv`). Disposition (PROPOSED): cite this
count in the row comment or the design note §3.

**F6 — SCOPE (the [AGENT] open choice): output-keyed dedup nodes.** Design §5 chooses (b) keep printing rows on the DFS
and records (a) extend `DedupNode`/`Obs` with output as Stage E's option, «Not PENDING [USER]: no claim changes either
way». The deferral is correct and conservative: option (a) changes `SlowObs`'s vocabulary and therefore the STATEMENT
of `checkCert_slowObs` — trust surface #2 — and so, when it is taken up, it is a named design gate (a HARD STOP under
CLAUDE.md's autonomous-arc rule), not an engineering default. Disposition (PROPOSED): one sentence in the handoff §6/§7
naming option (a) as a future design gate. Nothing to decide now.

Not findings, recorded as observations: (i) `poolThreadOblivious` is also `true` at bound 0 (ready = [] with active
work): the consult pops nothing, the step is the named refusal «malformed graph — pending active work with no ready
occurrence», `checkEdge` returns false and the certificate is refused — fail-closed, verified (probe P8 below: β refuses
by name; α «machine step failed at node 25 under vector []: …no ready occurrence»). (ii) `EnumDedup.refusalReason`'s two
"unreachable" texts are indeed unreachable: `innerVecs` returns `some` at both sites for every bound (≤ 1 through the
oblivious arm, ≥ 2 through N-PICK), so the `none`-only `refusalReason` never reaches them.

## 2. The certifier's soundness — (a), (b), (c), (d), (g), (h)

### 2.1 (a) Completeness of the branch vectors

The chain, read end to end (`file:line` at the candidate tip):

- `innerVecs` (`GoLean/GoCore/EnumDedupCheck.lean:110`; N-PICK arms `:140` `unseqPanic → some [[0],[1]]`, `:146`
  `unseqNext → if 2 ≤ unseqNextBound c then some ((List.range (unseqNextBound c)).map ([·])) else none`). `List.range b`
  = `[0, …, b−1]`: p = 0 and p = b−1 are both present by definition; the checker's `checkStep` (`:203`) requires
  `vecs.length == succs.size` and `checkEdge` (`:187`) requires each `stepMulti ctx nd.m vec` to SUCCEED with the vector
  consumed exactly (`chRem.isEmpty`). Vectors are recomputed PER NODE from the node's own `(shared, threads, cur)`
  (`nodeVecs`, `:172`) — the bound is re-read at every node.
- The step under `[p]`: `stepMulti` (`Multi.lean`) → `stepThreadInto` → `stepThread ctx s ts i [p]` → the `stepFn` path →
  `stepUnseqNext` (`StepFn.lean:226`, the consult at `:245`): `Choices.consumeAt .unseqNext (g.ready st).length [p]` =
  `(p % max 1 |ready|, [])` = `(p, [])` for p < |ready| (`State.lean:173`), then `(g.ready st)[p]?`. So the vector's step IS
  the scheduler's pick p — the checker does not ASSUME an order, it RUNS the machine at pick p. The question "is the
  order the checker assumes the same order `stepFn` uses" has no independent content: there is one `ready` (`Unseq.lean:271`,
  `(List.range g.occs.length).filter (g.readyAt st)` — canonical rank order = index order among ready occurrences), shared
  by `stepUnseqNext`, `Step.unseqPick` (`Machine.lean:5996`) and `seqConsumption` (`:5138`).
- Coverage: `stepThread_total_covered` (`EnumDedupSound.lean:271`, statement unchanged; the two N-PICK cases at
  `:357`/`:383`): for EVERY stream `ch`, `Choices.consume ch b = (p, rest)` with `p < b` (`consume_fst_lt`), so `[p] ∈ ivs`,
  and `stepThread_pick_run` (`MultiStreams.lean:537`) turns the vector's successful step into the step under `ch` with
  tail `rest`, through `stepFn_consumption_some` (`MachineSound.lean:6097`: the step depends on the stream only through the
  one pick). Its hypotheses at the two sites are discharged by `rfl` (`arrivalCases` is `.cellPath` on every non-channel
  shape, `Multi.lean:1263`; `selectApplyPlan = none`), `trivial` (`Config.appendTargetLocal` is `True` off the append
  shape, `Machine.lean:4025`) and the shape lemmas (`MachineSound.lean:1597`–`1626`). Nothing a corpus certificate must
  supply beyond what `checkCert` already checks.

Empirical probes (`Probe.lean.txt`; each program through BOTH existing drivers — β `CLI.explore`, α
`CLI.runDedupObservations` → `buildCert` + the UNMODIFIED `checkCert`; member lines compared exactly after sorting):

| probe | ready-set shape it exercises | β members (paths) | α members (nodes/edges/hits) | sets |
|---|---|---|---|---|
| P1 rank order ≠ occurrence order: occ 0 (A) ordered after C; ready₀ = [B,C,D,T] = indices [1,2,3,5]; pick 0 must select occ 1 | bound 4 → 3 → 2 → 1 | 12 (72) | 12 (3604/3649/46) | SAME — exactly the 12 orderings with C before A (c < a in every member; none with a = 0) |
| P2 ready set GROWS then SHRINKS: [A,B] → after A [B,C,D] → after B-first [A] (bound 1, the oblivious arm) | 2 → 3 / 2 → 1 | 8 (48) | 8 (2356/2385/30) | SAME — exactly the 8 with A before C and D |
| P3 GUARD whose decision depends on the order (`$a == 0` iff A first): the region activates on some paths only; h adds 10 to the counter | per-path bounds 2–3 | 3 (61) | 3 (1443/1473/31) | SAME — {11, 111, 100} as hand-predicted |
| P4 POOL: worker goroutine with its own width-2 sweep + main's width-2 sweep, join by a buffered channel | picks in two threads + l1Sched/postOp | 4 (544) | 4 (4502/4583/82) | SAME — {101, 110, 1001, 1010} |
| P4b POOL, channel-COUPLED: main's sweep = two blocking receive invocations; worker sends 1 then 2 unbuffered | the first-picked invocation BLOCKS mid-sweep | 2 (1296) | 2 (1127/1200/74) | SAME — {12, 21} |
| P7 MERGING with picks: two stamped + two silent occurrences | 24 orderings, states merge on the silent ones | 2 (144) | 2 (3998/4076/79) | SAME — {1, 10} |
| P8 fail-closed: cyclic order edges (A after B, B after A) → a pick with ready = [] and active work (bound 0) | the bound-0 arm | REFUSED by name («stuck: unseq: malformed graph — pending active work with no ready occurrence») | REFUSED by name («machine step failed at node 25 under vector []: … no ready occurrence») | both refuse; nothing certified |

Corpus: the 100 rows α closes (§3.1) reproduce the DFS's sets 100/100 on this binary — 21 of them consume `unseqNext`
(one to eighteen wide draws) and 30 consume `unseqPanic` (from the two-binary trace's per-id census).

Mutation controls on P1's certificate (33 two-way, 9 three-way, and several four-way pick nodes; the widest branches 4
= |ready₀| because the target plan T is ready from the start): unmutated ACCEPTED; M1 dropped member, M2 hints → 0, M3
dropped node, M4 three-way last branch dropped, M5 fabricated member — the five recorded controls — REFUSED; NEW M6 two
hints of a three-way node SWAPPED, M7 all three hints pointed at the first successor, M8 two-way hints swapped, M9
four-way last branch dropped, M10 four-way hints rotated, M11 a fifth branch appended to a four-way node — all REFUSED
(`mutations.txt`). M6/M8/M10 are the controls that would catch a vector↔successor order lie; M9/M11 the ones that would
catch a bound the checker did not recompute itself. The lane's own W1 controls: `gocore-eval-tests` 274 ok, the seven
`DEDUP-α` lines present (`gates.txt`).

**Answer (a):** complete. Every `p < unseqNextBound c` gets its singleton vector, p = 0 and p = bound − 1 included, at
every node afresh; the vector's step is the machine's own `stepFn` at pick p, so no order is assumed that could differ
from `stepFn`'s; six constructed graphs (rank ≠ index, growing/shrinking bound, order-dependent guard, two pool shapes,
merging) and 100 corpus rows give α = β exactly, and eleven mutations are refused.

### 2.2 (b) The determinization reads only the frame

`unseqNextBound : Config → Nat` (`Machine.lean:5101`): `| .next (.unseqK g _ st _ _ .pick _) => (g.ready st).length | _ =>
0`. It has NO store parameter and no thread-array parameter — the question "two stores that differ only in a guard's
completion cell, same frame: do the bounds differ?" is answered by the type: the bound is the same term for every store.
Walking `ready` (`Unseq.lean:271`) → `readyAt` (`:262`): `st[i]? == some .active && g.regionOk st o && o.after.all
(g.discharged st) && (g.deps o).all (g.produced st)` — every conjunct reads the STATUS list `st` and the static graph `g`;
`regionOk` (`:255`) tests the guard's STATUS (`== some .done`), never the completion cell's VALUE. The guard's decision
does read a binder cell — in `unseqGuard`, at the `.run i` configuration (`StepFn.lean`, the `.guard` arm), which is
not a pick position; it writes the resulting `st'` into the frame, and the NEXT pick position's bound is read off that
`st'`. `seqConsumption_unseqNext` (`MachineSound.lean:1619`) states this for the accountant: for every σ the report is
`(.unseqNext, |ready|)` iff `2 ≤ |ready|`. The dedup node is the whole `DedupNode = ⟨MultiConfig, RaceState⟩`
(`EnumDedupCheck.lean:54`) with `MultiConfig = ⟨threads, shared, cur⟩` (`Multi.lean:261`); `dedupNodeEqb_sound`
(`MachineEqb.lean:886`) gives `a = b` — two states with different stores are never one node, so even if a store-dependent
readiness existed it could not merge distinct states; and it does not exist. Probe P3 is the empirical form: the guard's
decision differs by path, the bounds differ by path, α = β.

**Answer (b):** yes — `unseqNextBound` is a function of the configuration alone by its type, and `ready`'s every conjunct
reads statuses, not cells; the store is consulted by the guard STEP (a `.run` configuration), whose result is written
into the frame before the next pick. The node key is the full pool state with a proved-sound equality, so no coarser
merge is possible.

### 2.3 (c) Obliviousness — every consumer of `poolThreadOblivious`

| consumer | where | what it does with the flag | the proof it rests on | holds with `decide (unseqNextBound c ≤ 1)`? |
|---|---|---|---|---|
| `innerVecs` N-OBL arm | `EnumDedupCheck.lean:112` | emits the single empty vector `[[]]` | `stepThread_total_covered` → `stepThread_oblivious` (`MultiStreams.lean:261`; the new case: `unseqNext` at bound ≤ 1 via `stepFn_consumption_none`, `MachineSound.lean:5707`) | yes: a bound-≤-1 `consumeAt` is `(0, ch)` (`State.lean:393`, G-U) so `stepFn` is stream-oblivious there; at bound 0 the step is a refusal and `checkEdge` fails closed (P8) |
| `stepAllBranchesOk` probe guard | `MultiStreams.lean:590` (in `:587`) → `allStreamsOkPool` (`:624`) | requires the flag before probing a branch | `stepAllBranchesOk_sound` (`:694`) via `stepThread_oblivious` | yes (same lemma); NO executable consumer outside `MultiStreams.lean` — grep over `GoLean/ Tests/ Main.lean spikes/` finds only its own soundness/monotonicity theorems |
| `EnumDedup.refusalReason` | `EnumDedup.lean:131` | text only | — | — |
| CLI stream logic (`stepNeeds`/`stepNeedsSeq`) | `CLI.lean` | reads `poolConsumption`/`seqConsumption`, not the flag | — | unaffected |

Cross-thread dependence: `stepFn ctx σ c ch` has no access to the thread array (its type), so a pick in thread i cannot
read thread j; `stepThread_pick_run`'s docstring («Nothing about the rest of the pool is assumed») is the type, not a
promise. Merging across threads: the node is the whole `MultiConfig`, so two configurations differing only in another
thread's pending picks are distinct nodes (`dedupNodeEqb_sound`). Probes P4 (independent sweeps in two goroutines) and
P4b (a sweep whose invocations block on the other goroutine's sends) give α = β. `stepThread_oblivious`'s and
`stepThread_total_covered`'s STATEMENTS are unchanged (the diff touches proof bodies only; `have h₀ := h` added).

### 2.4 (d) The legacy pick reclassified

`consumesUnseqPanic c` is exactly `.panicking _ (.probeK _)` (`Machine.lean:5073`; `consumesUnseqPanic_shape`,
`MachineSound.lean:1605`). On the pool it IS on the `stepFn` path: `Config.abort?` (`Machine.lean:3817`) is `some` only at
`.panicking (_ :: _) .stop`, and `.probeK k ≠ .stop`; `isBlockedConfig`/`spawnPlan`/`arrivalCases`/`selectApplyPlan` are
all off-shape; `stepFn`'s `case6` (`MachineSound.lean:6112`, pre-existing) is the bound-2 pop `seqConsumption_unseqPanic`
(`:1626`) reports. So it is the same shape as `unseqNext` — a `stepFn`-path pick with a configuration-determined bound
(the constant 2) — and the branch vectors `[[0],[1]]` are the DEFER/RAISE pair the delivery draws. The E13 "panic
delivery, not a scheduler pick" distinction is semantic, not structural: to the checker both are one `consumeAt` inside
`stepFn`. Pre-existing `engine=dedup` rows: the 23 (every dedup row but the moved one; `dedup-rows-main-vs-candidate.tsv`)
run through BOTH binaries with their own params: 23/23 SAME printed set AND SAME `nodes/edges/dedupHits` — including the
slow-tier `google-search` (6 members; 6 193 933 nodes / 6 565 663 edges / 371 731 hits; 93 s and 92 s). Their choice
trace on the candidate binary over six streams each consumes `l1Sched` 1430, `postOp` 722, `backEdge` 438,
`l5ExitWindow` 33 and ZERO `unseqNext`/`unseqPanic` (`trace-summaries.txt`) — none of them reaches either pick, which is
also what main's refusal-only `innerVecs` implies (a reachable pick would have been a red on main). The rows that DO
consume `unseqPanic` are E13-family rows; 30 of them are among the 100 α certifies with sets = DFS.

### 2.5 (g) No ordering optimization (R1)

`git diff 10d2f2dc..95c6c052 -- GoLean/` adds branch vectors and proofs only. `EnumDedup.lean`'s engine loop is
untouched except the two refusal texts; `internNode` (`EnumDedup.lean:217`) merges on `nodeBEq` (full node equality) in a
hash bucket — and the ENGINE is untrusted anyway: the checker re-validates every hint with `dedupNodeEqb` (sound
equality). No commutation rule, no sorted-ready-set canonicalization, no POR: the only merge is equal-state merge. R1
holds. (The ladder's `wide 8` = 21 887 states vs 40 320 paths is equal-state merging on the done-set lattice, as the
design note says.)

### 2.6 (h) Coherence and totality

`checkCert_slowObs` (`EnumDedupSound.lean:1005`) and `checkCertM_slowObs` (`:1060`): statements byte-identical to main
(the diff in that file is confined to `stepThread_total_covered`'s proof, lines 353–411). New lemma hypotheses (§2.1)
are all discharged inside `stepThread_total_covered` from what `innerVecs`'s branch structure already establishes — a
corpus certificate needs nothing new. `stepThread_stepFn_path` (`MultiStreams.lean:235`) is an equation, `stepThread_pick_run`
(`:537`) an implication from the vector's successful step; neither weakens a prior statement. Escape hatches: none in
the runtime diff (`sorry`/`native_decide`/`axiom`/`admit`/`unsafe`/`implemented_by`/`extern`/`partial def`/`opaque`/
`decide +` — grep of the added lines: empty). Gates (`gates.txt`): `scripts/check-core-audit` EXIT 0 (every GoLean
module; poison controls), `scripts/check-unseq-scheduler` EXIT 0 (35 required theorems, classical trio only),
`scripts/check-mem-callsites` EXIT 0 (70 rows inventoried), `scripts/check-bugs.sh` EXIT 0 (113 bugs, pinned cases
behave as claimed), `check-evidence-size` EXIT 0, `check-agents-alias` EXIT 0. Positional tags: the runtime commit does
not touch `StepFn.lean`, `Unseq.lean`, `Syntax.lean` or `NativeToIR.lean`; `fun_cases stepFn`'s numbered cases in
`MachineSound.lean` are unchanged (the modules rebuild warning-free).

## 3. The claims — (e), (f), (i), (j), (k)

### 3.1 (e) Certified vs DFS vs gc

Reproduced on the runtime-commit binary, wires lowered here from the corpus sources
(`tools/nativefrontend`, go1.26.5):

| what | recorded | reproduced | file |
|---|---|---|---|
| α corpus scan, 153 rows of the ladder's nine packages | 100 CLOSED / 42 REFUSE:output / 8 row-refusal / 2 appendSpill / 1 mapIterK | identical, row for row (classification diff empty); the 11 non-output refusal texts read (frontend-quarantined at node 0 ×8; «append spill capacity pick» ×2; «mapIterK iteration pick» ×1) | `alpha-scan-classes.tsv` |
| α set = β set on every CLOSED row | 100/100 SAME | 100/100 SAME (sorted JSON lines, byte-equal); `continue-label` β = 39 646 083 steps / 32 805 leaves, α = 5122 nodes / 5145 edges / 24 hits | `alpha-vs-beta-sets.tsv` |
| the harness's own differential (gc oracle; DFS engine except the moved row) over the 100 CLOSED ids | — | `scripts/capped scripts/coverage run`: 97 PASS / 3 FAIL; the three FAILs are `builtins/e13-sibling-panic-order/map-compound-index-key-vs-{call,recv,method}` — baseline FAIL, BUG-104 Cases pins (gc's draw ∉ the set: the known bug; α's set = DFS's set on each, so Stage D does not move them). `continue-label` PASS on its new confluent/dedup lane | `harness-run-summary.txt` |
| gc draws under GOMAXPROCS 1 and 8, 5× each, on the 51 `ok`-status CLOSED rows (+ 10+10 on `continue-label`) | «gc's draw in the set» | 50/51 rows ALL-IN (10/10 each); `continue-label` 20/20 the singleton; the one OUTSIDE is `map-compound-index-key-vs-recv` (0/10) — the same BUG-104 pin as above. gc drew ONE distinct observation per row under every setting (sequential subjects) | `gc-replay-gomaxprocs.tsv` |
| W1 certificate + M1–M5 | eval 267 → 274 | `gocore-eval-tests` 274 ok; the seven `DEDUP-α` lines; plus M6–M11 here (§2.1) | `gates.txt`, `mutations.txt` |
| membership rows' `members=` pins | 41 rows reproduce their pin | the 41 CLOSED membership rows' α cardinalities equal the DFS's; the harness run reports each row's `enumerated=members=` (e.g. `unseq-pilot/w2` `enumerated=3 … pin members=3`) | `harness-run-summary.txt`, `alpha-vs-beta-sets.tsv` |

### 3.2 (f) The lane move's licence

Rule 3 of the strict-lane depth guard (`docs/coverage-suite-structure.md:208`ff., [USER]-ruled 2026-09-03 as relayed):
a strict row whose streams are outrun is refused «unless the row carries `lane=confluent` (the enumerator certifies
|set| = 1 …) or … `lane=membership` with `members=`; or an explicit strict-lane `depth=N`». `continue-label` was on the
third remedy (`depth=128`, Stage C) because no engine could certify the `unseqNext` pick then; Stage D makes the first
remedy available (the engine closes the row: 10 267 node+edge work under `work=200000`; the guard fired at w = 18; the
observation is a silent singleton). Moving between two licensed remedies is a lane move; the rules require it to be
NAMED — it is, in the depth-guard section, the baseline header and the row comment. Licensed. The 41 membership rows
«recorded, not moved» are consistent: nothing in the rules asks a membership row the DFS closes in milliseconds to
change engine, and the existing dedup membership rows (`google-search`, `sched-dependent`, `rwmutex-order`, `sb-chan`)
moved only because the DFS could NOT close them (BUG-065). The strict E13/pilot rows that α closes are covered by the
three fixed streams (no guard firing) — no trigger, no move. The residual is F3 (caption precision) and F4 (inert params).

### 3.3 (i) The ladder

Same binary, same drivers (`Ladder.lean.txt` copied verbatim; `/usr/bin/time -v` around `scripts/capped lake env lean
--run`), one process per rung, on the shared box while other audit jobs ran (wall is indicative, as the record says):

| rung | recorded (README) | reproduced (`ladder-audit.tsv`) | within budget? |
|---|---|---|---|
| β `loop 8` silent | 256 leaves / 36 503 steps / 2847 ms / 770 MB | 256 / 36 503 / 2852 ms / 3.22 s wall / 756 MB | yes |
| β `wide 6` silent | 720 / 71 178 / 3349 ms / 767 MB | 720 / 71 178 / 3360 ms / 3.72 s / 760 MB | yes |
| α `loop 12` silent | 1419 nodes / 1430 edges / 12 hits / 0.49 s | 1419 / 1430 / 12 / 0.48 s / 757 MB | yes (linear: 154 + 115·11 = 1419 ✓) |
| α `wide 8` silent | 21 887 / 22 655 / 769 / 37.4 s / 773 MB | 21 887 / 22 655 / 769 / 37.98 s / 767 MB | yes |
| β `wide 7` printing | REFUSED by name (cap 4096; 5040 > 4096) 31.9 s | REFUSED «observation cap N=4096 exceeded — the case is too wide for enumeration» 31.97 s | refusal by name ✓ |
| β `loop 13` printing | REFUSED by name (cap 4096) 90–96 s | REFUSED, same text, 92.2 s | refusal by name ✓ |
| α `loop 3` / `wide 4` printing | refused (output event) | REFUSED «output event at node 49/60 (a print/println step wrote 1 chunk(s)) … output is a trace» | refusal by name ✓ |
| heap `loop N`, N = 1..6, 8, 12 | 3 + 4N cells | 7, 11, 15, 19, 23, 27, 35, 51 = 3 + 4N exactly; `nextAddr` = heap size (nothing reclaimed) | ✓ |

Budget derivations checked: `wide 8` 40 320 paths / 4 145 044 steps / 254–256 s ✓; `nest 5` 7776 paths / 87.4 s ✓;
`loop 12` «66–94 s» = the D1 run's 65.9 s and the pre-D1 partial run's 93.7 s, both tracked ✓; α `nest` 372 + 315·(M−1)
= 1632 at M = 5 ✓; `continue-label` `work=200000 ≈ 20×` (10 267 × 20 = 205 340) ✓; the per-path constant — F2.

### 3.4 (j) Records

- The five gate claims vs the tracked tails (`gate-tail.txt`, `gate-records-diff-tail.txt`): the `--slow` run at the
  runtime commit EXIT 1 in 946 s with FAIL steps exactly `certificate provenance` (STALE record, `CLI.lean` changed —
  the 5a class) and `baseline diff` (DRIFT = `google-search` + `continue-label`); the records `--diff` run EXIT 1 in
  789 s with DRIFT = `google-search` only; every other step `ok`; eval 274; negatives 394; check-unseq-scheduler 35 —
  as claimed. Not re-run here (§4).
- Baseline delta: `baselines/native-full.tsv` — exactly ONE row changed (`spec-examples-stmt/continue-label` `-` →
  `confluent`, PASS → PASS) plus the header block; `baselines/certified/` untouched (correct: the train installs the 5a
  candidate, the lane does not re-pin); `docs/BUGS.md` untouched; ledger §8 arithmetic 133 + 9 + (24 + 1) + 7 + 72 = 246 ✓.
- Whole-corpus choice trace (3669 ids byte-identical): reproduced on a 421-id subset (every `builtins/`, `evalorder/`,
  `binop-order/`, `multi-assign/`, `spec-examples-stmt/`, `noodler/latitude`, `noodler/maps` id) with main's binary vs
  this one: 421/421 SAME on the sorted per-consumption records and per-stream results; identical census (`unseqNext`
  495, `unseqPanic` 270, `l1Sched` 2263, `postOp` 727, `backEdge` 973, `appendSpill` 30, `l5ExitWindow` 25); each side's
  validator 4783 consumptions, 0 violations/alarms/mismatches (`trace-summaries.txt`).
- Twin claim: the five `multipkg/mini-raft-twin` rows on the candidate binary — 569 consumptions, all `appendSpill`, 0
  `unseqNext`/`unseqPanic`, observation invariant over the six streams ✓.
- `check-bugs` ✓ (BUG-065 unchanged: one Cases row — see F1). The handoff's [AGENT] choice — F6.

### 3.5 (k) Scope

`git diff 10d2f2dc..e34fc8ec --stat`: 34 files; runtime = the thirteen listed in the commit (checker, soundness,
MultiStreams, Machine +1 def + docstrings, MachineSound shape lemmas, EnumDedup texts, CLI seed factoring, tests, one
`cases.tsv`, the baseline). Nothing in Stage E (no family migration, no legacy removal — `unseqPanic` is certified, not
retired), nothing in C4 (reclamation is MEASURED and recorded — 4 cells/sweep — not implemented), nothing in P/C3 or the
NaN lane. Execution semantics: `StepFn.lean`, `Unseq.lean`, `Syntax.lean`, `NativeToIR.lean`, `tools/` untouched; the
421-id two-binary trace is byte-identical (above), which is the executable form of "the dedup engine changes no
execution".

## 4. What I did NOT check

- `scripts/ci` / `ci --slow` were NOT re-run (the box-wide lock; no finding needed it). The tracked tails were read and
  their step summaries reconciled with the claims; the individual `ok` steps I did re-run are listed in `gates.txt`.
- The whole-corpus trace was reproduced on 421 of 3669 ids (the packages that carry `unseq` graphs and their
  neighbours), not all 3669.
- gc draws were replayed on the 51 `ok`-status CLOSED rows (and `continue-label` ×20); the 49 panic-status CLOSED rows
  were exercised through the harness's own differential (97/3 above), not through my GOMAXPROCS loop (their observation
  is assembled from stderr by the harness, which my loop does not replicate). `-race` builds were not part of my replay
  (the harness's membership path alternates them; the subjects are sequential).
- Of the "16 rows" only three were spot-checked at work 20 M (F1); the other thirteen are taken from the depth-guard
  record.
- The pre-existing proofs the new cases lean on (`stepFn_consumption_some/none`, `stepMulti_total_covered`,
  `checkCert_complete_aux`) were read at their statements, not re-audited line by line — they are unchanged since their
  own audits.
- I did not attempt a hand-built `unseqPanic` graph (the shape is produced by the legacy lowering, not by `Stmt.unseq`);
  (d) rests on the shape/abort analysis in §2.4, the 30 corpus rows that consume it and certify with sets = DFS, and the
  23 dedup rows' zero census.
- No sandbox denial, no killed command decided anything (the two cap kills in F1 are reported as refusals).

## 5. Evidence (`docs/evidence/2026-09-20_unseq-stage-d-audit/`, 12 files, 67 KiB)

`ladder-audit.tsv` (the rungs above) · `Probe.lean.txt` (P1–P8 and the mutation driver; scratch glue over the existing
drivers) · `probe-members.txt` (every certified member line per probe, β/α counts and verdict; P8's two refusal texts) ·
`mutations.txt` (M1–M11) · `alpha-scan-classes.tsv` (153 rows → class, identical to the record) · `alpha-vs-beta-sets.tsv`
(100 SAME) · `dedup-rows-main-vs-candidate.tsv` (23 rows × both binaries, sets + stats) · `gc-replay-gomaxprocs.tsv` ·
`harness-run-summary.txt` · `trace-summaries.txt` (421-id two-binary trace; the 23 dedup rows' census; the twin) ·
`gates.txt` (exit codes, eval 274, binaries) · `sixteen-spot.tsv` (F1's three spot checks).

Regeneration (from this worktree, after the bootstrap in §0): `.tmp/ladder-audit.sh`, `.tmp/Probe.lean` (`lake env lean
--run .tmp/Probe.lean [mut]`), the lane's own `alpha-scan.sh`/`alpha-vs-beta.sh` (evidence README) with `ROOT` set here,
`scripts/choice-trace-corpus --dump --golean <bin> <ids>` + the lane's `trace-compare.py`, `scripts/capped scripts/coverage
run <ids>`, and the harness's generated `go-run/<id>` mains under `GOMAXPROCS=1|8 go run .`.
