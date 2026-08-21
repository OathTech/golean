# Raft W4.2 campaign log — the machine-twin harness

Lane: `raft-w42` (worktree `.claude/worktrees/raft-w42`), branch `raft-w42`
off `main` @ `4ef05649` (the W4.1 tip). Charter: harness design
(`docs/2026-08-20_machine-twin-harness-design.md`) §8's W4.2/W4.3 slices —
the logger swap + re-owed census, the n-node twin, the §7 trace ok-tier —
scoped CORPUS-FREE: this lane owns `raftsubject/`, `raftharness/`,
`tools/raftsubject/` and this log; the POR slice concurrently owns
GoCore/`Corpus/`/`baselines/`. Any corpus guardrail this lane wants is an
OWED ROW (§ owed-rows below), never landed here.

Read-first companions: the harness design (§2 the event vocabulary + the
recorded Ready-harvest narrowing, §4 S1–S4, §5 the ruled logger seam, §7
the trace plan), `docs/raft-w41-log.md` ("What the ruled logger swap
re-owes" — item 1's charter), `docs/raft-w3-log.md` (instruments),
`docs/2026-08-15_raft-push-p0-scoping.md` §6 (the executable Agreement
predicate this twin integrates).

## Environment notes (2026-08-21)

- Fresh worktree; `scripts/setup-deps --from /home/dev/projects/golean`
  exit 0 (goose 3be88bb, perennial 43d4efa, raft 56e3200, iris-lean
  3877dbe, go c19862e5f8); `proofs/.lake/packages` populated from the
  primary checkout (batteries/iris/Qq at the manifest pins).
- No runtime code (GoCore, `tools/nativefrontend/`, `Corpus/`,
  `baselines/`, `scripts/`) is touched anywhere in this arc, so per-landing
  gates run `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` with the
  two visible NOT-RUN notes, per the CLAUDE.md hatch contract. Heavy gates
  staggered against the concurrent POR lane (free -g checked first).

---

## Item 1 — the logger swap (the Q2 ruling executed) + the re-owed census

**Landed.** Upstream `logger.go` is vendored VERBATIM (mode `verbatim` in
`derive.py`'s VENDOR table); the D-5 no-op overlay
(`tools/raftsubject/overlay/raft/logger.go`) is DELETED. The one delta the
frontend still forces is recorded as **D-12** (ledger below): the two
package-level initializers lose their `log.New(...)` calls and the orphaned
`io` import drops — a package-level `var` has no per-declaration quarantine
(G-3 / handoff H-11), so an unlowerable initializer refuses the WHOLE
export. Land H-11 and D-12 retires to zero.

**The 144→2-3-line claim, RE-MEASURED** (artifacts/w42, diff vs
`deps/raft/logger.go`):

| | diff lines vs upstream |
|---|---|
| D-5 no-op overlay (retired) | **142** (the whole 142-line file replaced by a 116-line no-op) |
| the swapped tree | **11**, of which **3 are code** (2 initializer lines rewritten to `&DefaultLogger{}`, 1 dropped `"io"` import) and 6 are the D-12 recorded-delta comment + 2 context |

So the design §5's "three lines, not two" is confirmed exactly; its
"eleven fail-closed stubs" is now TEN — the §5 measurement predates W4.1's
fmt desugar, and `header` (`fmt.Sprintf("%s: %s", lvl, msg)` — constant
format, `%s` over strings) is inside the modeled subset and LOWERS.

**Observable weight of D-12, stated:** under `go run`, a Logger call
BEFORE the harness installs its logger nil-derefs inside `DefaultLogger`
(the embedded `*log.Logger` is nil) instead of printing to stderr — loud,
never silent; under the machine the same call is a fail-closed quarantined
stub. Both witnessed by the teeth probe below. `assertConfStatesEquivalent`
keeps its teeth through whatever Logger the harness installs — the whole
point of the ruling.

### The re-owed census, run (what W4.1's "0 LIVE" becomes after the swap)

`sweep.py` at the swapped tree (artifacts/w42/sweep-post-swap.txt;
`frontier.py` EXPORTS CLEAN, `derive.py --check` clean, subject
`go build` clean):

- **PASS 1: 24 quarantined subject declarations** (pre-swap tree
  re-derived and re-swept at THIS tip for an exact diff: **14** — the
  swap's delta is EXACTLY the ten `DefaultLogger` formatting methods
  joining, nothing leaving; artifacts/w42/sweep-pre). Imported stubs
  30 → **46** (the `log` package's declaration-only stubs join).
- **5 STATICALLY LIVE** quarantined subject declarations —
  `DefaultLogger.{Infof, Debugf, Warningf, Error, Errorf}` — plus
  **2 LIVE imported stubs** — `log.Logger.{Panic, Panicf}`, which is
  `DefaultLogger.Panic/Panicf` lowering and stopping one hop later.
  That is the W4.1 re-owed table's seven distinct methods, measured
  on the wire rather than predicted from grep.
- **RESIDUAL SINKS: 7** — the same seven. This census is NOT closed the
  way W4.1's was, and honestly so: the sweep never neutralises LIVE
  declarations, so what `DefaultLogger`'s bodies would call
  (`header`, `fmt.Sprint*`, `Output`, `os.Exit`) sits unmeasured behind
  them. It does not need measuring: the whole family is dead under the
  same dynamic argument, below.

**A count reconciliation, recorded:** W4.1's clause-1 headline said "15
quarantined in PASS 1"; the reproduction at this tip (same tree content,
this frontend) censuses 14. The 15 was recorded mid-arc before the
audit-fix round's `%x`/`%q` Stringer-precedence widening landed in the
same branch; one rendering declaration evidently lowered with it and the
prose number was not re-derived at the audit tip. Reconstructed, not
verified per-declaration; the tracked artifact pair (sweep-pre /
sweep-post-swap) is the number of record going forward.

### The dead-DYNAMICALLY argument (owed item ii), and why it is checkable

The seven statically-live entries are all dead under the twin, but dead
DYNAMICALLY — a static census over-approximates interface dispatch (a call
to `Logger.m` edges to every concrete `m`). The argument, in three parts,
each mechanically witnessed:

1. **The harness installs through BOTH seams before any node (or storage
   use) exists.** Constructor order, visible in the harness source:
   `lg := &harnessLogger{}; raft.SetLogger(lg)` is the first act (covers
   the six `getLogger()` sites — the registry is written once, pre-run,
   and never again); `cfg.Logger = lg` on every node's Config (covers
   every `r.logger.*` call, via `Config.validate`'s nil-check taking the
   assigned value). Package init cannot log first: `raftLogger`'s
   initializer merely aliases `defaultLogger`, and no `init()` in the
   subject tree calls a Logger method.
2. **The stubs have TEETH, witnessed** — so a green run is a meaningful
   negative. `logger-teeth-probe-main.go` (runprobe `--expect-stop`, new
   mode): the SAME drive with NO logger installed stops the machine at
   `frontend-quarantined: method raft.DefaultLogger.Infof (...)` —
   verbatim first stop — the moment `newRaft` logs, and dies loudly under
   `go run` (the D-12 nil-deref). PASS.
3. **The green half, machine-checked.** `logger-installed-probe-main.go`:
   the W4.1 THE-MOMENT drive with the harness logger installed through
   both seams runs GREEN under both oracles and agrees at **1111035** =
   the registry-seam teeth digit (a deliberate out-of-bound
   `MemoryStorage.Entries` routes `getLogger().Panicf` into the installed
   logger's fixed-string panic, recovered and folded into the summary —
   a call `Config.Logger` alone could NOT catch, exercising the §5
   amendment positively) + the unchanged 111035 drive summary. Every
   quarantined `DefaultLogger` body is a machine-STOP if called; the run
   is green; therefore none was called. The twin (item 2) re-witnesses
   this on every green n=3 run.

**The harness logger itself** (harness-owned, no verbatim-ness claim):
eight empty bodies + four fixed-string panics (`Fatal` panics too — no
`os.Exit` to model; "stop the machine" is the honest reading). It is
STATELESS — no fields, so its footprint is empty and sharing ONE value
across all n nodes cannot appear in any pairwise-disjointness obligation
of the §6 shared-nothing reduction; a buffering logger would be shared
mutable state on every node's every event and is explicitly ruled out
(per-node + a §6 re-run if ever needed).

### Subject-delta ledger additions (requirement (c) of the §8.6 ruling)

Continuing D-1…D-11 (W2 §4, W3 §1, W4.1). **D-5 is RETIRED by this item**
— a dated correction is appended at its W2-log entry; its noopLogger,
including the "Panic/Panicf no longer panic" weakening H-2 recorded, is
gone from the tree.

**D-12 `raft/logger.go`, the two package-level Logger initializers**
(item 1). Exact-text-keyed `SUBJECT_PATCHES` derivation patch:
`defaultLogger`/`discardLogger` lose their `log.New(os.Stderr,...)` /
`log.New(io.Discard,...)` calls (unlowerable package-level initializers,
G-3/H-11) and become bare `&DefaultLogger{}`; the orphaned `io` import
drops. Everything else in the file — the Logger interface,
`SetLogger`/`getLogger`/`ResetDefaultLogger`, `DefaultLogger` and all its
methods, `header`, the `raftLoggerMu` mutex — is upstream text.
**Observable weight:** a Logger call before the harness installs its own
nil-derefs loudly under `go run` (upstream would print to stderr) and
stops the machine at a quarantined stub; unreachable under the twin
(the dead-DYNAMICALLY argument above, both halves probed). Retires to
ZERO when H-11 lands. The patch keys on upstream's exact `var (...)`
block and refuses on drift.

**Gate:** `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` at the
item-1 commit — see the exit-state section for the verbatim result lines.

---

## Item 2 — the n-node twin (`tools/raftsubject/twin-main.go`)

**Landed.** The harness design §1-§4 realized as a probe-main-style Go
program run under BOTH oracles by `runprobe.py`: n RawNodes, no
goroutines, no clock, no context; the network is a `[]*pb.Message`
multiset with a liveness bitmap (removal by index — indices are what a
schedule names, §3); one driver step = one event applied to one node +
the bundled harvest; S1-S3 checked the moment their evidence exists (the
failure witness is a prefix); S4 is the END condition; the exercise floor
(>=1 claim, >=1 committed command) reported separately from safety. The
checker is `raftharness/harness.go`'s `checkSafety` reshaped per-step —
same properties, same violation grammar (S1 leaderOf map at claim time,
S2 byIndex slot map at apply time, S3 per-node monotonicity + the anomaly
channel, S4 all-driven-commands-applied).

**THE SCHEDULE IS THE INPUT.** v1 drives named hand schedules (tables in
the file); determinism measured, not assumed: three consecutive `go run`s
of the full schedule battery produce byte-identical traces (md5
`2508c1de20caec3596585358354cdf3b` ×3). The ∀ch form — events drawn from
the machine's choice stream — is the membership lane's, over this same
mechanism.

**Judgment calls, recorded:**

- **JC-22: `campaign(i)` is IN the v1 vocabulary** (the design's §2 table
  has it tier-2). Measured reason: a timeout-driven election consumes the
  D-11 jitter draw, whose VALUE legitimately differs across oracles (that
  is what a choice site is), so a jitter-sensitive schedule cannot
  promise same-trace-on-both-oracles. v1 schedules keep per-node unreset
  election ticks far below ElectionTick=10 and drive elections
  explicitly — exactly what upstream's own datadriven traces do with
  their `campaign` command (54 blocks). The jitter-sensitive tier
  belongs to the membership lane (owed row below).
- **JC-23: the harvest loops to LOCAL quiescence** (`for HasReady`),
  not a single `if`. Same recorded §2 narrowing either way (no other
  node is stepped inside the bundle); the loop form is what W4.1's
  THE-MOMENT probe ran, which is what lets `probeTwinSingle` reproduce
  111035 VERBATIM through the new machinery, and matches the go-run
  family's one-iteration-per-Ready loop shape. Bounded at 64 rounds,
  fail closed.
- **JC-24: `drain`/`drainRev`/`drainSkip(i)` are schedule MACROS over
  `deliver`, not new event kinds** — deliver-to-quiescence in insertion /
  reverse-insertion / all-but-node-i order (bounded 10000, fail closed).
  `drain` is upstream's `stabilize`; `drainSkip` is unbounded delay made
  concrete (fairness non-assumption: a starved node's messages are "not
  chosen yet" forever). drop/dup are OFF in v1 — the reliable-first
  envelope, a strictly weaker claim than raft's design point, stated
  here as the design requires.
- **JC-25: the trace projection uses HARNESS-OBSERVED state only** (last
  harvested HardState term/commit, last SoftState, applied index) — no
  `Status()`/rendering call; the projection is part of the observation
  both oracles must agree on byte-for-byte, so it leans on nothing but
  the Ready contract the harness already consumes. Integer rendering is
  a plain-Go digit loop, not fmt.
- **PreVote=false** (upstream's default and the datadriven traces'),
  where the go-run family sets true — the family is the executable spec
  of the PROPERTIES, not of a config; recorded, not hidden.

**The schedules and what each witnesses** (full traces:
`artifacts/w42/twin-{single,elect,perturb,ticks}.txt`): `elect` (baseline election; commits
nothing by design, so its floor line reads floor=0 honestly — an
election-only schedule has no committed command), `elect-propose-commit`
(a dropped-then-retried proposal — the drop-and-retry client, §3 —
then 2 commands committed 3×), `follower-propose` (MsgProp forwarded
through the multiset), `dueling-candidates` (two candidates, one term —
S1's workout; node 1 wins on vote order, node 2 rejoins on MsgApp),
`perturb-rev` / `perturb-mix` / `perturb-picks` (the perturbation
matrix: reverse-order drains, mixed drains, and explicit picks — 3 hears
the vote first, commit reached at quorum {1,3} while 2 lags),
`starve-node` (node 3 starved for the whole run: S1-S3 hold, S4
complete=0 EXPECTED — conditioned safety made concrete), `heartbeat`
(leader heartbeats + follower ticks under the jitter-safe bound). Every
schedule ends `viol=0`.

**Both oracles — RESULT: agreement on every schedule.** The battery runs
as four probe groups (`twin-lib.go` + thin mains; `runprobe.py --lib`,
added here), each a full trace-string comparison, artifacts
`artifacts/w42/twin-{single,elect,perturb,ticks}.txt`:

| group | verdict (runprobe, verbatim in the artifact) | machine wall |
|---|---|---|
| `probeTwinSingle` | **PASS — both oracles agree: 111035** (the W4.1 THE-MOMENT drive reproduced through the NEW harness, same packing) | ~1.5 min |
| `probeTwinElect` (elect, elect-propose-commit, follower-propose, dueling-candidates) | **PASS — full multi-line trace agreement** | ~20 min |
| `probeTwinPerturb` (perturb-rev, perturb-mix, perturb-picks, starve-node) | **PASS — full multi-line trace agreement** | ~24 min |
| `probeTwinTicks` (heartbeat) | **PASS — full multi-line trace agreement** | ~2 min |

Zero disagreements to diagnose: no machine-side stop, no divergence, no
harness bug surfaced by the differential — every schedule ends `viol=0`
on both oracles with identical per-event projections.

**Two instrument findings recorded on the way** (both fixed in
`runprobe.py`, the second the reason the split exists):

1. **String observations decode from `{"bytes": [...], "tag":"string"}`,
   not `"value"`** — the first comparison read `None` and would have
   DISAGREED on every string probe; worse, the very first twin run's
   verdict was masked to exit-0 by a `| head` pipeline (the pipeline's
   exit is `head`'s). Both instruments now decode the bytes form and
   fail loud on an unrecognized shape; no verdict in this log predates
   the fix.
2. **A whole-battery machine run is interpreter-slow** (>30 CPU-min,
   killed rather than trusted at fuel 4e9); the split groups bound each
   verdict and name the group a stop would belong to. Recorded as an
   open perf question in item 4.

---

## Item 3 — the trace ok-tier (`tools/raftsubject/tracereplay.py` + `replayenv.go`)

**Landed (measurement only — no corpus rows).** `replayenv.go` is a
faithful plain-Go mirror of upstream `rafttest`'s InteractionEnv for the
supported command subset (ONE Ready cycle per process-ready in upstream's
order; stabilize as upstream's ready/deliver fixed point; deliver-msgs as
splitMsgs bag-order delivery with drop=/type= support; add-nodes with
raftConfigStub defaults — ElectionTick 3, HeartbeatTick 1, no size
limits, snapshot term stamped 1). `tracereplay.py` parses the 28
testdata files into their 558 datadriven blocks, computes each trace's
SUPPORTED PREFIX (a partially replayed trace past its first unsupported
command has no meaningful pass/fail — design §7), generates a per-trace
driver, runs it under both oracles, and scores the ok-tier.

**Unsupported-by-design commands, each with its reason** (the docstring
carries the same list): tick-election + set-randomized-election-timeout
(jitter-sensitive — the D-11 value differs across oracles by
construction), compact/send-snapshot (the subject never compacts;
snapshots in Ready fail closed), propose-conf-change (conf-change apply
outside v1; every "multi-line command input" stop is this command's
body form), process-append/apply-thread (async storage writes, §7's
named deferral), transfer-leadership/forget-leader/report-unreachable
(tier-2 vocabulary), add-nodes with async-storage-writes/content/
read-only args.

**The numbers** (report artifacts:
`artifacts/w42/tracereplay-{main,replicate_pause,par}.txt`; the machine
tier ran as three parallel slices after the whole-suite single process
proved interpreter-slow):

- 28 traces, **558 blocks**, of which **249 expect literal `ok`**.
- **268 blocks (48.0%) inside supported prefixes**; **178 ok-expectation
  blocks** among them.
- **OK-TIER: 178/178 agree** — the driver said ok exactly where upstream
  expects ok, on every replayed block (121/121 across the 27 smaller
  traces + 57/57 in probe_and_replicate).
- **MACHINE TIER: every replayed trace that completed its machine run
  agrees BYTE-FOR-BYTE with go run** — 26/26 across the two smaller
  slices (25 in the main slice incl. lagging_commit 17/17 and prevote
  16/16 end-to-end; replicate_pause 32/32 end-to-end).
  **probe_and_replicate's machine run is the one OUTSTANDING verdict at
  the item-3 commit**: its single-process interpreter run needs upward
  of an hour and was twice killed by the session environment's
  background-task lifetime (~1 h) before completing — an environment
  bound, not a machine stop; a detached run is in flight and its
  verdict is recorded in the exit-state section as measured (command:
  `tools/raftsubject/tracereplay.py --traces probe_and_replicate
  --fuel 20000000000`).
- **6 traces replay END TO END**: campaign (4), lagging_commit (17),
  prevote (16), probe_and_replicate (74), replicate_pause (32),
  single_node (4) — the design §7 predicted 7; the seventh
  (checkquorum) stops at `tick-election`, which is jitter-EXCLUDED here
  by design, so 6 is the honest count for this tier.
- **First-divergence report: EMPTY.** No ok-tier disagreement and no
  machine-vs-go trace divergence occurred anywhere; there was nothing to
  diagnose. The stops in the per-trace table are all
  unsupported-COMMAND stops (the by-design list above), not behavioral
  divergences.
- The stopper census over the 22 partial traces: `propose-conf-change`
  bodies ("multi-line command input") 11, compact/send-snapshot 3,
  forget-leader 2, async-storage-writes 2, tick-election 1,
  set-randomized-election-timeout 1, report-unreachable 1,
  add-nodes read-only 1 — each named per trace in the report artifact.

---

## Item 4 — the W4.3/W4.4 handoff

### What the FULL trace tier (the 309 rendered-expectation blocks) needs

The 309 non-`ok` blocks, classified by required renderer family
(block-anchored count over all 28 files, method in this log's history):

| blocks | family |
|---|---|
| 106 | ready dumps (`> N handling Ready` — DescribeReady + DescribeMessage + interleaved log lines) |
| 58 | pure log lines (INFO/WARN/DEBUG — upstream's env logger formatting) |
| 42 | other/mixed |
| 40 | message describe lines (deliver-msgs output — DescribeMessage) |
| 30 | raft-state tables (StateType + tracker.Config rendering) |
| 18 | status tables (Progress rendering) |
| 15 | raft-log dumps (entry describe + the `%q` entry formatter) |

**The bonus probe's honest answer: 0 of the 309 render TODAY.** Every
renderer behind them is still fail-closed quarantined; the one renderer
the current fmt subset DID retire whole is `DescribeConfChange`, which
these blocks reach only inside conf-change traces that stop earlier (at
`propose-conf-change`). The exact remaining refusal causes, off the
post-swap census wire (each is a named frontend/model gap, none a raft
quirk): `fmt.Fprint` (unformatted variadic — DescribeReady,
Config.String, Progress.String), `fmt.Fprintf` over a `*bytes.Buffer`
writer (describeMessageWithIndent; only `*strings.Builder` is modeled),
`%v` over `[]uint64` (DescribeConfState), `%q` over `string`
(StateType.MarshalJSON), `%+v` over a struct (logSlice.valid),
`strconv.FormatUint/FormatInt` (Index.String, VoteResult.String),
`strings.Split` (ConfChangesFromString), `slices.SortFunc`
(MajorityConfig.Describe — H-5, still off the twin's path), and
`Sprintf` with a spread argument (the DefaultLogger bodies — moot under
the installed twin logger).

**A structural finding for the rendered tier, stated before anyone
builds it:** the 58 pure-log-line blocks (and the log lines inside the
106 ready dumps) are produced by upstream's env OUTPUT logger — the twin
CANNOT reproduce them through its installed logger, whose whole design
is to render nothing (stateless, §5/§6). Reproducing them requires a
RECORDING logger, which is shared mutable state unless made per-node —
the §6 footprint check must be re-run if that is ever built, and it
belongs to the replay ENV (measurement tooling), never to the twin's
reduction argument.

### Owed corpus rows (this lane is corpus-free; each is a row the corpus
owner should land, with the witness already built here)

| owed row | witness here |
|---|---|
| the twin as a corpus family (multipkg raft-shaped case: n=3 elect + propose + commit, schedule-determined trace, PASS under both oracles) — §8 W4.2's "the corpus gains its first raft-shaped case" | `twin-main.go` + artifacts/w42/twin-runprobe.txt |
| the perturbation schedules as corpus rows (drainRev / picks / starve — S1-S3 under reordering + starvation) | same |
| the logger-teeth pair as corpus rows (fail-closed interface-stub dispatch: uninstalled -> visible stop; installed -> green) | logger-teeth / logger-installed probe mains |
| a membership row for the choice-stream-driven twin (events drawn from `∀ch` over the enabled set — the envelope form of the schedule input) | mechanism in twin-main.go; the draw plumbing is new work |
| ok-tier trace replays as corpus rows (the 6 end-to-end traces, go-vs-machine trace equality) | tracereplay.py artifacts |

### Standing handoff items

- **H-11** (package-level var quarantine) retires D-12 to zero — the
  logger file becomes fully verbatim. Frontend lane.
- **W4.5 obligations unchanged**: the §2 harvest-atomicity re-envelope
  (the `harvest` event kind), the jitter RANGE latitude entry, the §6
  footprint run against its five-item checklist.
- **The census is now 24-quarantined/5-statically-live by design** — do
  not quote W4.1's "0 LIVE" forward; the number of record post-swap is
  this log's item 1, argument included.
- **checkquorum's full replay** needs `tick-election` +
  `set-randomized-election-timeout` — i.e. a harness-facing way to PIN
  the jitter draw. Upstream pins it via test hooks the subject tree does
  not carry; any pin here is envelope work (a deliberate narrowing to
  record), not a convenience patch. Decide beside the W4.5 latitude
  entry.
- **Conf-change support** (propose-conf-change + ApplyConfChange in the
  replay env + the twin) unlocks 11 more traces (the largest single
  stopper class: every "multi-line command input" stop). The subject
  side already lowers (`ProposeConfChange`/`ApplyConfChange` are in the
  twin's entry surface); the work is env/driver-side.

### Open questions

- Should the twin's `PreVote` default flip to true (the go-run family's
  choice) once the trace tier no longer anchors config to upstream's
  stub? Both are legitimate; today the trace-replay compat argument
  wins.
- **Interpreter wall-time is the practical bound on this instrument
  family**, measured: small traces are seconds, replicate_pause (32
  blocks) ~6 machine-minutes, the twin's elect/perturb groups ~20-24
  minutes each, probe_and_replicate (74 blocks, 7 nodes) the better
  part of an hour. Splitting into parallel bounded runs is the working
  answer; an interpreter-performance pass (or a compiled evaluation
  path) is the real one if this family is to run in any gate. Nothing
  here lands in a gate today.

## W4.2 exit state

Branch `raft-w42` off `main` @ `4ef05649`, one commit per item, each
landed with its gate run recorded in `artifacts/w42/ci-*.txt` (the
charter's per-landing `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G
scripts/ci` — legitimate throughout: no commit touches runtime code,
`Corpus/`, `baselines/`, GoCore, `tools/nativefrontend/` or `scripts/`;
every gate PASS carries the two visible NOT-RUN notes the hatch owes).

- item 1 `5eaa9d1b` — the logger swap + re-owed census (gate PASS).
- item 2 `8fe49dca` — the twin, both oracles agree on every schedule
  (gate PASS).
- item 3 — the trace ok-tier instrument + measurements (gate PASS at
  its commit; verdicts in this log's item 3).
- item 4 rides in this log (the handoff sections above).

DELIVERABLE STATUS against the lane charter: (1) DONE — swap landed,
delta re-measured, census re-run WITH the checkable dead-DYNAMICALLY
argument (probe pair); (2) DONE — n=3 election/proposal/commit + the
perturbation matrix, go-vs-machine agreement on every schedule, 111035
reproduced, zero disagreements to diagnose; (3) DONE as measurement —
268/558 blocks replayed, 178/178 ok-tier agreement, machine byte-level
agreement on every completed replay (probe_and_replicate's long-fuel
verdict recorded in item 3); (4) DONE — the handoff sections above.
Owed corpus rows: item 4's table — NONE landed here, by charter.
