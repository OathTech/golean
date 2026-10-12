# Scheduling boundaries at the observable operations — design note (2026-10-12)

Lane `core/sched-boundary-1012` (worktree `.claude/worktrees/sched-boundary-1012`, off `main`
@ `d92b95fd`). Authority: [USER] Mike 2026-10-12 «manage some agents working through the
backlog, starting with the ones that require no input from me» (the release punch list
`docs/2026-10-12_release-readiness.md`, items 23 and 24); the Codex release-trust review
`docs/2026-10-12_release-trust-review.md` §F1 and §R2, relayed by the [USER] the same day;
the standing rule [USER] 2026-10-07 «Yeah, the semantic widenings should only be allowed if
they match real Go» (`docs/2026-08-31_qrow-rulings.md`, relayed). Every decision below is
[AGENT] unless marked.

## 1. The defect, reproduced at the base tip

`Config.atBoundary` (`GoLean/GoCore/Multi.lean`) is the predicate the pool's scheduler
consults: a context switch happens ONLY at a registry boundary (channel/select/sync/atomic
apply positions, spawn positions, exit, the parked shapes, the post-op flag) or a loop
back-edge; between boundaries the running goroutine's steps are "private to it". Two
operations are NOT private and have no boundary:

- the channel arm of `lengthOf` (`Machine.lean`, `len(ch)`): it reads the channel cell's
  buffer count — shared state a peer's send or receive changes — and emits NO access footprint
  (latitude inventory U2: `len`/`cap` on channels are uninstrumented on gc too, so the race
  detector is silent BY DESIGN; `NPDRF.lean` obstruction 5 names exactly this hazard: «a step
  reading a shared cell with an empty recorded footprint would be treated as a both-mover it
  is not»);
- the `print`/`println` apply (`stmtOpK (.print _)`): it writes fd 2 — the program's
  observable output — and gc's `printlock` makes one STATEMENT atomic, not a run of them
  (ledger FR-30, recorded 2026-09-05 as a silently admitted class).

So two `len(c)` reads, or two prints, in one registry-free segment of a goroutine cannot be
separated by a peer's send or print on the machine, while real Go separates them.

Measured on this lane at the base tip (`.lake/build/bin/golean` built from `d92b95fd`;
pinned gc `go1.26.5 linux/amd64`, `GOMAXPROCS=2`; the review's two witnesses rebuilt
verbatim under `.tmp/witness/`, lowered by `tools/nativefrontend`):

| witness | machine (base tip) | gc plain | gc `-race` |
|---|---|---|---|
| `len(c)` after a spawned send, a pure `delay(100)` recursion between two reads; returns `10*a+b` | DFS `{0, 11}` (18,368 steps, 34 leaves); dedup `{0, 11}` (18,121 nodes, `certified=checkCert`); no refusal | 10,000 calls: `0` 9,999, **`1` 1**, `11` 0 | 10,000 calls: `0` 9,861, **`1` 72**, **`11` 67**; no race diagnostic |
| parent prints `A`, `delay(100)`, prints `C`; child prints `B` then sends on the join channel | DFS `{ACB, BAC}` (13,641 steps, 27 leaves); dedup refuses printing rows by name | 1,000 calls: `ACB` 993, **`ABC` 7** | 1,000 calls: `ACB` 891, **`ABC` 107**, `BAC` 2; no race diagnostic |

«observed ∈ modeled» FAILS on two race-free programs with no refusal: a wrong answer, class
MODEL TOO NARROW (the machine's scheduling relation admits fewer runs than gc realizes). The
checker's certificate is correct about the modeled machine; the modeled machine is wrong.

## 2. The change — which configurations gain a boundary, and why each matches real Go

| configuration | boundary | reason |
|---|---|---|
| `.retV (.chan _) (.strictK (.lengthOf _) _ [] _ _)` — the `len` apply on a CHANNEL operand | **gained** | the read observes the buffer count, which a peer's send/receive changes with no synchronization required: spec#Channel_types («…may be used by any number of goroutines without further synchronization»), spec#Length_and_capacity (`len(ch)` = «number of elements queued in channel buffer»); the memory model orders a send before the completion of the corresponding RECEIVE only, never before a `len`; gc witnesses the switch (table above: `1` and `11`). |
| `.retV _ (.stmtOpK (.print _) _ _ [] _ _)` — the `print`/`println` apply | **gained** | the apply writes fd 2, the observable; gc serializes one statement (`runtime/print.go` `printlock`) and lets any goroutine write between statements (dossier §1.1: scheduling is unspecified); gc witnesses the switch (`ABC` above; FR-30's own 1/300 report). |
| `cap(ch)` | **not gained** | a channel's capacity is fixed at `make` for its whole life (spec#Length_and_capacity: «channel buffer capacity»); no execution can observe a peer through it, so a boundary there would multiply enumeration for nothing. |
| `len(m)` (maps) | **not gained** | a real instrumented read (`Mem.mapRead`, S3 audit): a concurrent map write is a data race the detector refuses; under the DRF premise every peer write is ordered through a registry op, which IS a boundary. |
| `len`/`cap` of a slice, array, string, pointer-to-array | **not gained** | they read the operand VALUE (a header or a type-static count), private to the goroutine. |
| channel send/recv/close, select, sync, atomics, spawn, exit, the parked shapes, the post-op flag, loop back-edges | unchanged (already boundaries) | — |
| pure computation, calls, returns, recursion (the witnesses' `delay`), stores and loads of ordinary cells | unchanged (no boundary) | ordinary memory stays under the race detector + DRF premise; this lane does not touch access granularity. |

Mechanics. Both new arms are SHAPE arms of `Config.atBoundary`, nothing else: the site a new
boundary consults is `Config.boundarySite`'s default `.l1Sched` (goroutine-order menu, slot 0
= lowest-index runnable; consumed only at ≥ 2 runnable — the uniform rule, so a sole runnable
goroutine consults at bound 1 and pops nothing: sequential conservation untouched). The
post-op FLAG is not set by either (`Config.registryCommits` is unchanged: neither completes a
registry op). A PRE-boundary at every observable operation is sufficient: for any
cross-goroutine order of observable events there is a schedule that switches exactly before
each event, so every order gc can realize is a run of the widened machine — and no new
choice site exists: the members added are the scheduler's existing L1 envelope at two more
positions, which is exactly what gc exhibits (the standing rule: every added member is
witnessed in §1's table; nothing wider).

Canonical-stream consequence (recorded, not hidden): on the empty/default stream the L1
slot 0 is the lowest-index runnable goroutine, so a CHILD goroutine at a `len(ch)` or a print
while main is runnable now yields to main where it used to continue. Strict-lane RESULTS do
not depend on this (a strict row's observation is stream-invariant by the lane's own
three-stream check); membership/confluent rows compare sets. The alternative — a dedicated
site with issuer-first slot 0, the `backEdge` precedent, so the default stream reproduces the
old trajectory literally — is a census change (`ChoiceSite` constructor + `canonicalSlot0`
row + `schedSlots` arm + the consumption projections) and is NOT taken: the brief asks for
the minimal change, and `.l1Sched`'s own canonical-slot-0 sentence («lowest-index runnable
goroutine») already describes the new consults. Recorded as an option for the coordinator
if a consumer's default trajectories matter.

## 3. Proof impact — every theorem whose proof mentions `atBoundary`

Pinned text first. `GoLean/GoCore/BridgeSet.lean` names `t.atBoundary` in exactly one
statement, #530 `stepML_switch_boundary` («a switch happens only at a boundary») — BY NAME, so
its text is unchanged. The frozen surface `scripts/check-pool-spec` hashes
(`PoolStep.lean`, `PoolStatement.lean`) does not define `Config.atBoundary` (it lives in
`Multi.lean`); `MultiConfig.schedMenu?`, `SchedSlot`, `schedRecord` consult
`Thread.atBoundary` by name. **No pinned statement's text changes, no re-pin, no STOP.** What
changes is the MEANING of the named definition — the relation `StepML` admits the new
switch points — which is the intended, customer-visible widening (the pool statements
remain true at the widened definition; the build proves it).

Proofs that UNFOLD or compute `Config.atBoundary` (the only ones a new arm can touch):

| theorem | file | proof shape | expected |
|---|---|---|---|
| `threadDone_atBoundary` | `NPDRF.lean` | `unfold Config.atBoundary; rw [h]; rfl` — `true \|\| _` | unchanged (short-circuits on `isTerminal`) |
| `isBlockedConfig_atBoundary` | `NPDRF.lean` | `rfl` on the four parked shapes | unchanged |
| `atBoundary_of_abort` | `MultiSound.lean` | `rfl` on `.panicking _ .stop` | unchanged |
| `wakeReady_of_schedPick` (inner `hat`) | `PoolErrorFacts.lean` | `cases c <;> simp_all [isBlockedConfig, Thread.atBoundary, Config.atBoundary]` | unchanged (every non-parked case closes by the `isBlockedConfig` contradiction) |

Every other mention is `by_cases hb : t.atBoundary = true` or a `split` on the executable's
`if t.atBoundary` — generic over WHICH configurations are boundaries: `schedPick_le_fine`
(`NPDRF.lean`), `stepMulti_*` / `execProg_*` in `MultiSound.lean` (lines 425, 851, 912, 1200,
1254), `MultiStreams.lean` (637, 815, 1353), `MultiWfSound.lean` (1238), `PoolSound.lean` (82,
118, 338, 396, 605, 837, 851, 920), `PoolProjection.lean` (226), `PoolSingletonFacts.lean`
(80), `EnumDedupSound.lean` (512). The enumerators and checkers (`EnumDedup.nodeRefusal`,
`EnumDedupCheck.nodeVecs`, `ChoiceTrace.poolTarget`, `poolConsumption`, `CLI.stepNeeds`) read
`Thread.atBoundary`/`schedSlots` through the machine's own functions; the dedup certificate
re-runs `stepMulti` per edge, so it follows the definition. The semantic equations
(`scripts/check-equations`) are per-arm `stepFn` lemmas; `atBoundary` is pool-side and not
enrolled. Verified by the rebuild (§7).

## 4. Cost

Each observable operation executed while ≥ 2 goroutines are runnable is one more L1 consult
of bound |runnable|: enumeration trees multiply per such operation on the membership /
confluent rows. Rows expected to move: those mixing prints or `len(ch)` with live peers —
`builtins/print/goroutine-interleaving` (two one-print children), `goroutines/sched-
dependent/len-handoff` (one `len`), the strict rows under `panic-recover/panic-preprint`,
`race/gomem-only`, `sync/trylock` (three streams each, linear — no tree). No `engine=dedup`
row prints (the engine refuses output by name); `imported-goose/channel/google-search` (the
former slow row) has no print and no `len(ch)` in its subject (grep of its `main.go`); the
other dedup packages' `len(ch)` reads (`goroutines/buffered-wake`, `noodler/select`) sit in
subjects outside their dedup rows. Measured in §7: the two witnesses before/after, and
the `--diff` wall (the last records: 534–913 s) with every `engine=dedup` row's time against
the 300 s `LEAN_ENUM_TIMEOUT_SECONDS` budget.

## 5. Evidence to land with the change

- Two membership rows, born from the review's witnesses, pinned to what the widened machine
  certifies and sampled under gc plain/`-race` (the lane rules: `nondet` tag, `why`, `width=`,
  `members=`, the two-draw floor): `goroutines/sched-dependent/len-peer-send` (set
  `{0, 1, 11}`, members=3) and `builtins/print/goroutine-gap` (set `{ABC, ACB, BAC}`,
  members=3). The `delay(100)` recursion is kept: it is what makes gc exhibit the extra
  members at a useful rate; the machine opens no boundary inside it.
- `docs/BUGS.md`: BUG-123 (model too narrow; fixed here; both rows on its Cases line).
- `docs/language-coverage-ledger.md` FR-30: CLOSED by the print boundary, the row pinning it.
- `GoLean/GoCore/NPDRF.lean` obstruction 5 and the latitude inventory's U2 sentence: one
  sentence each pointing at this note (the detector-side record stays as written; the
  scheduling-side hole is the one closed here).
- `baselines/native-full.tsv`: the two new PASS rows, and every row whose result or stage
  moved, with the written reason; a PASS→non-PASS flip must be on a `- Cases:` line.

## 6. What this lane does NOT do

- No change to access granularity, the race detector, the NPDRF draft statement, the
  `cap(ch)` arm, the map/slice/string `len` arms, the abort window (B3), or the
  init-phase print refusal (the sequential driver has no scheduler).
- No new choice site; no change to `schedSlots`, `Config.boundarySite`, the post-op flag
  rule, or any pinned statement's text.

## 7. Results

**Rebuild** (`capped lake build`, the box under a load average of ~90 from other agents'
builds): every module rebuilt with NO proof change — `PoolErrorFacts` 142 s, `PoolSound` 31 s,
`BridgeSet` 11 s (the pinned `example` statements elaborate unchanged); `golean:exe` linked.
`python3 scripts/check-pool-spec`: `ok [frozen] both files and 48 statements match`;
`git diff main -- GoLean/GoCore/BridgeSet.lean GoLean/GoCore/PoolStep.lean
GoLean/GoCore/PoolStatement.lean docs/specs/pool-relation/` is EMPTY. The §3 prediction held:
four shape-insensitive proofs, nothing to re-prove.

**The two witnesses, same binary before/after** (`coverage-observations`, width 2, sites 32,
`--expect-status ok`):

| witness | engine | base tip `d92b95fd` | lane tip |
|---|---|---|---|
| `len(c)` | DFS | `{0, 11}` — 18,368 steps, 99 probes, 34 leaves, depth 8 | `{0, 1, 11}` — 46,192 steps, 282 probes, 95 leaves, depth 10 (×2.5 steps) |
| `len(c)` | dedup | `{0, 11}` — 18,121 nodes / 18,129 edges, `certified=checkCert` | `{0, 1, 11}` — 31,756 nodes / 31,779 edges, 24 dedup hits, `certified=checkCert` (×1.75 nodes) |
| prints | DFS | `{ACB, BAC}` — 13,641 steps, 78 probes, 27 leaves, depth 7 | `{ABC, ACB, BAC}` — 46,040 steps, 462 probes, 155 leaves, depth 10 (×3.4 steps) |

Every member gc exhibited in §1 is now certified, and nothing else is: the sets are exactly
`{0, 1, 11}` and `{ABC, ACB, BAC}` — the three placements of the peer's one observable
event relative to the two observed ones. Dedup's certificate (`checkCert`) covers the
widened graph: the checker re-runs `stepMulti` per edge through the widened predicate.

**Static checks at the working tree**: `scripts/coverage-manifest` accepts both rows;
`scripts/check-bugs.sh` ok (123 bugs; BUG-123's two Cases PASS in the edited baseline;
backlog unchanged: coverage 10/10, latitude 4/4, wrong-answer 0/0).

**The gate** (`capped scripts/ci`, then `capped scripts/ci --diff` under the box lock at the
final tip): recorded in the lane's final commit message and report — the `--diff` summary
line, the wall, the per-row movement (captions of the membership rows that gained consults),
and the `engine=dedup` rows' times against the 300 s budget.
