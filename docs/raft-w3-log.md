# Raft W2.2 campaign log — the raft.go frontier sweep

Lane: `raft-w3` (worktree `.claude/worktrees/raft-w3`), supervised arc under the
standing merge/audit protocol. Charter: master plan
(`docs/2026-08-15_raft-master-plan.md`) §W1.3 and §W2.2/§W2.3 — the raft.go
sweep the roadmap has never had a number for, and the machine-twin harness
DESIGN (`docs/2026-08-20_machine-twin-harness-design.md`). Owns
`raftsubject/` additions, `tools/raftsubject/` extensions, and these two docs.
Does NOT touch `Corpus/`, `baselines/`, GoCore, `tools/nativefrontend/` or
`scripts/`; every need found there is a handoff row, not a change.

Base: `main` @ `7ca8908e` (rebased 2026-08-20; the bug-fix arc is merged, so
what this log called "the post-merge frontend" is simply the frontend now).
`deps/raft` @ `56e32004b1af3a4cb625fbfe5dbca24fb6023d09` (unchanged from W2.1).
Predecessor: `docs/raft-w2-log.md`.

**The measurement in one line.** With the raft ROOT package vendored, the
frontend needs **2 fixes to export the subject tree** and **9 more causes
cleared for a RawNode-driven twin to RUN** — measured export-blockers plus
measured live run-blockers, from a census whose masking limits are documented
in §2.5. Of the run-blockers two were already open tickets (the protobuf
codec, the fmt story). Before the merge the same tree needed **35 further
declaration-level neutralisations**, all of them methods, all retired by H-3
(`c7938b25`).

> **Re-measured 2026-08-20 (audit fix round).** Every number below is from a
> re-run against the merged frontend, through the tracked instruments. Four
> claims moved and each is marked in place: the export-blocker count 3 → **2**
> (G-3 is an ALTERNATIVE route past G-2, not an independent blocker), the gap
> list 8 → **11 rows** (G-1 splits, and `strings.Join` and `strings.Builder`
> join it), the live-declaration census 25 → **26** (the previously-MASKED
> election-jitter draw), and the sweep is now reproducible from tracked
> material (`tools/raftsubject/sweep.py`).

---

## §1 What was vendored, and how (the derivation extension)

`tools/raftsubject/derive.py` gains the raft root package. Fourteen new
upstream files (plus one generated), all digest-pinned like the rest:

| out path | upstream | mode |
|---|---|---|
| `raft/{raft,rawnode,log,log_unstable,storage,status,read_only,util,types,bootstrap,state_trace_nop}.go` | the same names | verbatim |
| `raft/node_decls.go` | `node.go` | **select** (new mode) |
| `confchange/{confchange,restore}.go` | the same names | verbatim |
| `proto/proto.go` | — | **generated** (new) |

Three things are worth stating rather than assuming.

**(a) `node.go` is not vendored; eleven of its declarations are.** RawNode does
not compile without `Ready`, `SoftState`, `Peer`, `IsEmptySnap`,
`IsEmptyHardState`, `isHardStateEqual`, `SnapshotStatus`, `emptyState` and
`confChangeToMsg` — they live in `node.go` beside the `node` goroutine loop the
plan of record excludes (master plan §W2.2: "RawNode-driven node loops (no
node.go / context / time)"). The new `select` mode keeps exactly those
declarations BYTE-VERBATIM and drops the other 26, dropping the `context`
import with them. It fails closed in both directions: a named declaration that
is not found refuses the derivation (upstream moved it — re-read the subset),
and so does a dropped import whose package name still appears in the kept text.
The dropped set is D-8 in the ledger below.

**`ErrStopped` is the eleventh, and NOT for the reason the first draft gave**
(corrected 2026-08-20, audit). It is not needed for RawNode to compile: grep
over the whole subject tree finds it referenced nowhere but its own declaration
(`node_decls.go:19-20`). It is in the tree because of **CHUNK GRANULARITY** —
`select` mode keeps whole `var (…)` blocks, and `ErrStopped` shares one with
`emptyState`, which IS needed (`IsEmptyHardState`, `bootstrap.go:48`). That is
a real cost and not a free ride: `ErrStopped = errors.New("raft: stopped")` is
one of the NINE package-level `errors.New` initializers the walk has to rewrite
(§2.2, G-2), so a granularity convenience buys an export-blocker row. Splitting
the block — keeping `emptyState`, dropping `ErrStopped` — would retire that row
at the cost of a sub-declaration delta in the ledger; deferred, recorded, and
the trade is now visible rather than implied.

**`emptyState` is an ALIASED POINTER, and the footprint check owes it a line.**
`emptyState = &pb.HardState{}` is package-level and `bootstrap.go:48` assigns it
straight into a RawNode (`rn.prevHardSt = emptyState`), so two nodes that both
went through `Bootstrap` would hold the SAME `*pb.HardState`. Under the twin
this is currently harmless — `Bootstrap` is measured dead (§2.3) and
`IsEmptyHardState` only reads through it — but "harmless today" is exactly the
kind of claim the shared-nothing side condition (harness design §6) exists to
mechanize rather than assert. Recorded there as a checklist item.

**(b) The protobuf runtime import is rewritten, and the target is a
fail-closed package we emit.** `google.golang.org/protobuf/proto` becomes the
subject-local `proto`, and `derive.py` generates `raftsubject/proto/proto.go`
declaring exactly the four functions the vendored tree calls — `Clone`,
`Marshal`, `Unmarshal`, `Size` — each an explicit panic. The census is taken
from CODE (comments stripped first: the confstate overlay's header names
`proto.Clone`/`proto.Equal` while describing what it replaced them with), and a
call to any function not in the table REFUSES the derivation. This is handoff
H-1 given a home, not a discharge: nothing is silently approximated, every call
site stops the machine loudly, and W4 replaces the four bodies with derived
plain Go. Ledger D-9.

**(c) `state_trace.go` is not vendored; `state_trace_nop.go` is.** Upstream
selects between them with `//go:build with_tla`, and `go/parser` does not apply
build constraints — vendoring both would redeclare every trace function. The
default build's file is the one in the tree. Ledger D-10.

**The tree compiles.** `go build` over `quorum raftpb tracker proto confchange
raft` in a GOPATH scratch: clean. `derive.py --check`: clean — the whole tree,
including the 15 new files, is the derivation's output. `difftest.py`: PASS,
unchanged (nothing in this arc touched raftpb).

### Subject-delta ledger additions (requirement (c) of the §8.6 ruling)

Continuing `docs/raft-w2-log.md` §4, whose D-1…D-6 are unchanged.

**D-7 the raft root package — verbatim, import paths only.** Eleven files plus
the two `confchange` files carry NO change but the import rewrite (2–5 paths
each, counted in the derivation's own report). Every construct the frontend
cannot lower stays exactly as etcd writes it — the `fmt.Sprintf`s, the
`errors.New`s, the promoted mutex calls — so §2's census is a measurement of
raft, not of our editing.

**D-8 `raft/node_decls.go` — a declaration subset of `node.go`.** Kept: the
eleven declarations named above, byte-verbatim. Dropped: 26 declarations — the
`Node` interface, `node`, `msgWithResult`, `setupNode`, `StartNode`,
`RestartNode`, `newNode`, `confChangeToMsg`'s siblings and all 20 `node`
methods — plus the `context` import. **Observable weight:** the subject loses
the `Node` API entirely. Nothing in the RawNode path calls it (RawNode is the
layer BELOW `node`; `node` is a goroutine loop wrapped around it), and the
machine twin supplies that loop itself. The file name differs from upstream's
deliberately: `node_decls.go` should not read as "node.go, vendored".

**D-9 `raft/../proto/proto.go` — generated, no upstream counterpart.** Four
fail-closed stubs standing in for the protobuf runtime. **Observable weight:**
`Clone`, `Size` and `Unmarshal` are all LIVE under a RawNode harness (§2.3), so
this delta is the reason the twin cannot run yet, stated as loudly as possible.
`Marshal` is reached only from `Bootstrap`, which the harness declines.

**D-10 `state_trace.go` is not vendored.** The `with_tla` build variant is
absent; the default build's `state_trace_nop.go` (empty trace bodies) is in the
tree. **Observable weight:** nil for the default build — that IS the default
build. Vendoring the other variant would be a deliberate decision with a TLA+
trace consumer behind it.

---

## §2 The refusal inventory (the measurement)

Instruments, all tracked and re-runnable — **and that is now literally true**
(2026-08-20, audit): the headline used to rest on two untracked scratch scripts
in `artifacts/`, so no reader could reproduce it. They are replaced by
`sweep.py` below, which runs the whole measurement end to end from tracked
inputs and prints the headline number itself.

- `tools/raftsubject/frontier.py` — the walk, extended with three PROBE-DELTA
  actions (`$drop-import`, `$rewrite`, `$add`) because the raft root package
  refuses in places a body replacement cannot reach: an import refuses before
  any declaration is read, and a package-level `var` has no body to replace.
- `tools/raftsubject/frontier-plan.tsv` — THE plan, re-pinned against the
  merged frontend: 14 action rows + terminal. It was two files (a pre-merge
  plan of 71 rows and a post-merge plan of 14); H-3 landed as `c7938b25`, so
  the pre-merge plan is retired per H-16 and its content survives as the
  difference measurement in §2.2.
- `tools/raftsubject/reachability.py` — Answers the question H-3
  moves us to: since a refusal no longer blocks the export but lands as a
  signature-carrying stub that refuses WHEN CALLED, a quarantined declaration
  on a dead path costs nothing and one on a live path is a run-time stop. It
  walks the call graph OF THE EXPORTED WIRE (the frontend's own resolved
  callees, including `func-value` references) from a named entry set and prints
  each verdict with the path that witnesses it.
- `tools/raftsubject/sweep.py` — **the headline instrument.** `reachability.py`
  alone under-reports, because a quarantined declaration is a SINK on the wire
  and this tree has sinks high on every path. `sweep.py` therefore runs the walk,
  censuses it, then re-exports a probe tree with the sinks OPENED (dead
  declarations neutralised, live causes flattened) and re-censuses — **to a
  fixpoint**, because neutralising a declaration cuts its own edges and one
  round's dead set is the next round's blind spot. It ends with a RESIDUAL-SINK
  report, which is what turns "behind the sinks there is nothing new" from an
  assertion into a check, and with the G-1 probe of §2.5.

Emitters: `main` @ `7ca8908e` (the merged frontend — the only one that matters
now). The pre-merge comparison in §2.1 was run against `main` @ `ee1e5628` and
the then-unmerged bug-fix arc, whose commits have since landed (H-3 as
`c7938b25`, the statement-position `copy` fix as `f495724e`).

### 2.1 What the bug-fix arc's merge did to this tree

Measured while that arc was still unmerged: the W2.1 inventory was re-run under
both emitters on the UNCHANGED W2.1 tree (quorum + tracker + raftpb + logger):

| frontend | result |
|---|---|
| pre-merge (`main` @ `ee1e5628`) | the 10-row walk reproduces exactly, `EXPORTS CLEAN`, exit 0 |
| the bug-fix arc, now merged (H-3 = `c7938b25`) | **all 10 rows retire**: the tree exports clean with ZERO neutralisations |

So every one of W2.1's F-1…F-10 was a pre-merge artefact. Nine of them retire
because H-3 quarantines methods per declaration; F-6 (`copy` in statement
position, handoff H-4) retires because the bug-fix arc FIXED it — `copy` and
`recover` are legal expression statements (spec#Expression_statements), and the
raft path was named in that commit's message (`f495724e`). **H-4 is discharged; H-3 is
discharged as far as declared methods go** (its own residual scope — method
STENCILS of generic types — is recorded in `mono.go`).

### 2.2 The gap inventory over the full tree

Method: derive the tree, walk it with the tracked plan (which applies the
export-blocking probe deltas), export, and census every declaration the wire
marks `unsupported`. **53 subject declarations are quarantined**, which
includes the three promoted `MemoryStorage.{Lock, TryLock, Unlock}` stubs (the
first draft said 50, folding those three into G-6 rather than counting them;
they are counted here and the double-count is avoided by grouping, below).
A further **36** quarantined entries are imported stdlib stubs
(`bytes.Buffer` ×24, `strings.Builder` ×9, `sync.Mutex` ×3), which is the
pre-existing declaration-only-stub contract, not a raft gap — with **one
exception that is now measured rather than assumed**, G-10.

Grouped by CAUSE, which is what a work item is:

| # | gap | where it bites | live? | status |
|---|---|---|---|---|
| **H-9** | **the inittask double-escape** — a FRONTEND DEFECT, and not about raft: any multi-package program whose stdlib closure reaches `crypto/internal/entropy/v1.0.0` refuses (detail below). raft reaches it through `crypto/rand`, imported for the jitter draw. | export-BLOCKING | — | **new (defect)** |
| **G-1** | **the election-jitter draw itself** — `raft.go:2054` `globalRand.Intn(...)`, whose one implementation `(*lockedRand).Intn` (`raft.go:97`) calls `crypto/rand.Int` + `math/big`. Refusal, measured: `package-selector call rand.Int (package "crypto/rand" surface not modeled)`. | run-blocking | **LIVE** — `Intn ← resetRandomizedElectionTimeout ← becomeFollower ← (*raft).Step` | **new**; fix direction is the CHOICE SITE, W4.1 |
| **G-2** | **`errors.New` is not modeled.** 26 call sites; 9 of them are package-level `var Err… = errors.New(…)`. | export-BLOCKING at the 9 globals; the census cause of 5 more declarations at the in-body sites (a 6th, `Changer.apply`, carries one behind its `Errorf`) | all 5 live | **new** |
| **G-3** | **a package-level variable has no per-declaration quarantine** — the structural half of G-2. A method with an unlowerable body becomes a refusing stub (H-3); a `var` with an unlowerable initializer still refuses the WHOLE export. | an ALTERNATIVE route past G-2's globals, not an independent blocker | — | **new** |
| **G-4** | **the protobuf codec** — `proto.Clone` / `proto.Size` / `proto.Unmarshal`. Not quarantined: the generated stand-ins are explicit panics, so they lower and fail closed at RUN time. | run-blocking | all three LIVE | **known: H-1** |
| **G-5** | **`fmt` on live paths** — `Sprintf` ×6, `Errorf` ×11, `Fprintf` ×3, in 10 live declarations (§2.4). | run-blocking | LIVE | **known: H-6** |
| **G-6** | **promoted / embedded `sync.Mutex` operations.** `MemoryStorage` embeds `sync.Mutex` and calls `ms.Lock()` / `defer ms.Unlock()`; only DIRECT statement/defer-position sync ops on a named field are modeled. | run-blocking | 8 methods LIVE (the 3 promoted stubs are the same cause seen from the method-set side, and are dead once the ops lower) | **new** |
| **G-7** | **`bytes.Equal`** — `raft.go:1102`, inside `(*raft).Step`. | run-blocking | LIVE (the step function) | **new** |
| **G-8** | **a selector call on an imported package-level variable of an UNEXPORTED type** — `binary.LittleEndian` (`var LittleEndian littleEndian`, `encoding/binary`), at `read_only.go`'s `recvAck` and `heartbeatCtx`. The frontend renders it `field selector on anonymous struct type invalid type`, i.e. it never resolved the type. 12-line repro below. | run-blocking | both LIVE | **new** |
| **G-9** | **`strings.Join`** — `raft.go:496`, inside `newRaft`, which `NewRawNode` calls. It was invisible in the first draft because a census names ONE cause per declaration and `newRaft`'s first refusal is `fmt.Sprintf` five lines earlier. **H-6's discharge therefore does not unblock `newRaft` on its own.** | run-blocking | LIVE | **new** |
| **G-10** | **`strings.Builder.String`** — an imported declaration-only stub, live via `DescribeConfChange` (§2.3's rendering exception). Bounded and measured: **1 of the 10 `strings.Builder` users in the tree is live**, and it is the only imported stdlib stub reachable at all. | run-blocking | LIVE | **new** |
| — | `slices.SortFunc` (H-5) | quarantines `MajorityConfig.Describe` | **dead** under the harness | known: H-5, and NOT on the twin's path |

**THE NUMBER THE ROADMAP ASKED FOR** (re-measured 2026-08-20). Between the
frontend and "RawNode-driven raft.go exports clean" stand **2 measured
export-blockers**: H-9's inittask defect and G-2's `errors.New`. **Not three** —
G-3 is an alternative route past G-2's nine globals, not an independent
blocker: fix either one and those nine rows go away. Between the frontend and
"the twin RUNS" stand **9 measured live run-blocker causes** (G-1, G-2, G-4…G-10),
covering **26 live quarantined subject declarations** (§2.3), the 3 live
fail-closed codec stubs, and 1 live imported stdlib stub. Of the eleven rows,
**2 are the known tickets** (G-4 = H-1's codec, G-5 = H-6's fmt story) and nine
are new — and of those, four are one-line-to-one-function frontend items
(`errors.New`, `bytes.Equal`, `strings.Join`, and the inittask defect).

Against the PRE-merge frontend, add **35 declaration-level blockers** on top
(34 quarantined methods + `Inflights.grow`): each must be neutralised for the
export to proceed at all. That is the whole content of the difference between
the two plans that existed before the merge — 71 action rows vs 14, i.e. 35
further body replacements and **22** further import drops (the plan's other 3
import drops are shared with the surviving plan).

**H-9's refusal, and it is not about raft.**
The message is `package "crypto/internal/entropy/v1%2e0%2e0" is not in the
stdlib inittask table`. The table HAS that row (`inittask-std.tsv` line 64,
with the unescaped name in its 4th column). The bug is a DOUBLE ESCAPE:
`buildInitGraph` (`load.go:475-478`) pushes `entry.deps` — which are already
linker symbol PREFIXES — back onto its worklist as import PATHS, and
`pathToPrefix` then escapes the `%` again, so the lookup asks for
`crypto/internal/entropy/v1%252e0%252e0`. Minimised to a **6-line, 2-package
program** that imports `crypto/rand` and does nothing else; it refuses on both
emitters. Single-package programs are unaffected because `specInitOrder`
returns early below two units (`load.go:360`) — which is why nothing in the
corpus has ever hit it. Handoff **H-9**.

That early return is not just trivia: it is what makes G-1 measurable at all.
`sweep.py`'s G-1 probe puts `(*lockedRand).Intn` verbatim in a SINGLE-package
program, where H-9 does not fire, and the frontend gets far enough to say what
the draw itself costs. It exports clean (exit 0) with exactly one subject
declaration quarantined, and the refusal is the one recorded in G-1's row.

**G-8's repro, and a methodological warning that cost this lane an hour.**

```go
// helper/helper.go
package helper
import "encoding/binary"
type T struct{ acks map[uint64]uint64 }
func (t *T) Recv(from uint64, ctx []byte) {
	if len(ctx) != 0 {
		t.acks[from] = max(t.acks[from], binary.LittleEndian.Uint64(ctx))
	}
}
```
lands as `method helper.T.Recv (field selector on anonymous struct type invalid
type; …)`. **The export still EXITS 0** — that is the warning: after H-3, a
zero exit status no longer means "nothing refused", it means "nothing refused
in a position that blocks". Post-merge, the exit code is not the measurement;
the census is. Every liveness and gap number in this log is taken from the
wire, never from an exit status.

### 2.3 Liveness: which of the 53 must lower before the twin runs

`sweep.py`, entries = the RawNode-driven twin's API surface
(`NewRawNode`, `Tick`, `Step`, `HasReady`, `Ready`, `Advance`, `Propose`,
`Campaign`, `ApplyConfChange`, `ProposeConfChange`, `NewMemoryStorage`,
`SetHardState`, `Append`, `CreateSnapshot`, `IsEmptyHardState`, `IsEmptySnap`).

**26 are LIVE.** The instrument reaches that number in three parts, and prints
all three, because the parts have different strengths:

| part | count | what it is |
|---|---|---|
| PASS 1, first order | 19 | reachable on the walk's own exported wire |
| PASS 2, behind the sinks | 6 | revealed once the sinks above them are opened (2 rounds to fixpoint) |
| the G-1 probe | 1 | `(*lockedRand).Intn`, MASKED in both passes by the walk's own probe delta (§2.5) |

The live set partitioned by CENSUS CAUSE — the first refusal the emitter met in
that declaration. This is an exact partition: 8 + 10 + 5 + 2 + 1 = 26.

- **G-6 (8)** `MemoryStorage.{Append, CreateSnapshot, Entries, FirstIndex,
  LastIndex, SetHardState, Snapshot, Term}` — the Storage the twin runs on.
  `ApplySnapshot` and `Compact` are dead only because the twin as designed
  never compacts; the moment it does, they join. (The three promoted
  `MemoryStorage.{Lock, TryLock, Unlock}` stubs are the same cause seen from
  the method-set side, and are dead once the ops themselves lower.)
- **G-5 (10)** — `Sprintf` ×6: `raft.newRaft`, `raft.stepLeader`,
  `(*raft).restore`, `voteRespMsgType`, `(*ConfChangeV2).EnterJoint`,
  `Progress.SentEntries`; `Errorf` ×3: `confchange.Changer.apply`,
  `confchange.checkInvariants`, `(*raftLog).scan`; `Fprintf` ×1:
  `raft.DescribeConfChange`.
- **G-2 (5)** `Changer.{EnterJoint, LeaveJoint, Simple}`, `Config.validate`,
  `(*raft).Step`.
- **G-8 (2)** `readOnly.recvAck`, `readOnly.heartbeatCtx`.
- **G-1 (1)** `(*lockedRand).Intn`.

**A declaration has ONE census cause and may have SEVERAL gaps**, which is why
the eleven gap rows of §2.2 do not add up to twenty-six. Each declaration below
is counted once above, under the first cause, and carries a second that only a
per-site reading finds — this is exactly how G-9 stayed invisible:

| declaration | census cause | also carries |
|---|---|---|
| `raft.newRaft` | `fmt.Sprintf` (`raft.go:491`) | **`strings.Join` (`raft.go:496`, G-9)** |
| `(*raft).Step` | `errors.New` (`raft.go:1092`) | `bytes.Equal` (`raft.go:1102`, G-7) |
| `confchange.Changer.apply` | `fmt.Errorf` (`confchange.go:167`) | `errors.New` (`confchange.go:171`, G-2) |
| `raft.DescribeConfChange` | `fmt.Fprintf` (`util.go:250`) | `strings.Builder` (`util.go:249`, G-10) |

The exact per-declaration, per-site list is §2.4.

**THE SINK PROBLEM, and why the fixpoint matters.** A quarantined declaration
has no body on the wire, so the reachability walk STOPS there. This tree has
sinks high on every path — `newRaft`, `stepLeader`, `(*raft).Step` — so a
first-order census under-reports by a third. The six revealed behind them:

```
confchange.Changer.apply      <- Changer.EnterJoint <- applyConfChange <- RawNode.ApplyConfChange
confchange.checkInvariants    <- checkAndReturn <- Changer.EnterJoint <- ...
raft.Config.validate          <- newRaft <- NewRawNode
raft.DescribeConfChange       <- stepLeader <- ... <- (*raft).Step <- RawNode.Step
raft.readOnly.heartbeatCtx    <- bcastHeartbeat <- stepLeader <- ...
raft.readOnly.recvAck         <- stepLeader <- ...
```

Opening the sinks is itself iterative: neutralising a declaration to walk past
it CUTS ITS OWN EDGES, so one round's dead set is the next round's blind spot.
Run to a fixpoint (2 rounds here) it is stable; run once, `Changer.apply` and
`checkInvariants` stay hidden behind `Changer.EnterJoint`, which is exactly the
error a hand-curated dead list would have preserved.

**THE CLOSURE CHECK — now a check, not a claim.** "Behind the sinks there is
nothing new" is only meaningful if no sinks are LEFT. `sweep.py` therefore ends
by asking the final probe wire which declarations are still quarantined AND
reachable. The answer here is **none**: every reachable declaration in that wire
has a body, so the gap list is CLOSED over this subject tree. The first draft
asserted this from a probe that still had 11 residual sinks in it.

**`raft.DescribeConfChange` is LIVE, and it is a correction to W2.1.**
`stepLeader` passes `DescribeConfChange(cc)` as an ARGUMENT to `r.logger.Infof`
(`raft.go:1340`). W2.1 §6(a) argued that a no-op logger makes rendering
runtime-dead because "Go evaluates the argument (a field read) but only `fmt`
calls `String`". That is right for a `%s` over a value and WRONG when the
argument is itself a call to a rendering function: Go evaluates it before the
call, no-op body or not. Exactly one such site exists in the root package
(measured by grep over every `logger.*f` call), and it is this one. The
conclusion "rendering is quarantine-dead" survives for every rendering
declaration but this one — and it drags G-10 in with it, since
`DescribeConfChange` builds its result in a `strings.Builder`.

**The dead 27, in full:** `confchange.Describe`, `DescribeConfState`,
`DescribeEntry`, `DescribeHardState`, `DescribeReady`, `DescribeSnapshot`,
`DescribeSoftState`, `describeMessageWithIndent`, `describeTarget`,
`ConfChangesFromString`, `ConfChangesToString`, `quorum.Index.String`,
`MajorityConfig.Describe`, `MajorityConfig.String`, `VoteResult.String`,
`MemoryStorage.ApplySnapshot`, `MemoryStorage.Compact`,
`MemoryStorage.{Lock, TryLock, Unlock}`, `RawNode.Bootstrap`,
`StateType.MarshalJSON`, `Status.MarshalJSON`, `logSlice.valid`,
`raftLog.String`, `tracker.Config.String`, `Progress.String`,
`ProgressMap.String`.

**Two honest limits on the liveness verdicts, both in the instrument's
docstring.** (i) Interface dispatch is over-approximated — a call to
`Logger.Infof` marks every concrete `Infof`; so LIVE is a candidate that the
path witness lets you check, while `dead` is the sound direction. (ii) The sink
effect above, which the fixpoint removes for every cause the sweep flattens and
the residual-sink report accounts for otherwise.


### 2.4 The fmt site census (input to the H-6 ruling — §7 of the W2 log)

Every LIVE `fmt` site in the vendored tree, with what the result is USED for.
This is the input the fmt ruling was missing; the ruling is recorded in §5.
**Re-measured 2026-08-20 over the corrected 26-declaration live set** — the
`DescribeConfChange` row is new (three `Fprintf` sites that the first draft's
liveness census could not see, because `DescribeConfChange` was hiding behind
`stepLeader`'s sink), and `checkInvariants` is `Errorf` ×9, not ×10.

| site | call | argument kinds | the result is… |
|---|---|---|---|
| `raft.go:1332` | `Sprintf("possible unapplied conf change at index %d (applied to %d)", …)` | `uint64`, `uint64` | **a live value on a decision path**: assigned to `failedCheck`, and `failedCheck != ""` is what makes `stepLeader` rewrite a proposed conf change to a no-op |
| `raft.go:491` | `Sprintf("%x", n)` in a loop, then `strings.Join` (`raft.go:496`, G-9) | `uint64` | a logger ARGUMENT — but computed unconditionally on `newRaft`'s path, no-op logger or not |
| `raft.go:1340` | `logger.Infof("%x … %s … %s: %s", …, DescribeConfChange(cc), r.trk.Config, failedCheck)` | `uint64`, rendered strings, `tracker.Config` | the argument evaluation is live (see §2.3); the formatting is not |
| **`util.go:250,252,255`** | **`Fprintf(&b, "transition:%v")`, `Fprintf(&b, " changes:{type:%v node_id:%d}")`, `Fprintf(&b, " context:%q")` — `DescribeConfChange`, into a `strings.Builder`** | `ConfChangeTransition`, `ConfChangeType`, `uint64`, `[]byte` | **a live string**: the value `raft.go:1340` evaluates. Also the sole live use of `strings.Builder` (G-10) |
| `raft.go:1933` | `panic(Sprintf("unable to restore config %+v: %s", cs, err))` | `*pb.ConfState`, `error` | a panic message |
| `util.go:79` | `panic(Sprintf("not a vote message: %s", msgt))` | `pb.MessageType` (a plainpb enum with a fail-closed `String`) | a panic message |
| `progress.go:183` | `panic(Sprintf("sending append in unhandled state %s", pr.State))` | `tracker.StateType` | a panic message |
| `raftpb/confchange.go:109` | `panic(Sprintf("unknown transition: %+v", c))` | `*ConfChangeV2` (fail-closed `String`) | a panic message |
| `log.go:488` | `Errorf("got 0 entries in [%d, %d)", lo, hi)` | `uint64`×2 | an error VALUE returned to a caller that branches on `err != nil` |
| `confchange.go:167` | `Errorf("unexpected conf type %d", cc.GetType())` | enum | ditto |
| `confchange.go:290…327` | `Errorf` **×9**, mostly `"%d …"` | `uint64` | ditto (`checkInvariants`) |

Totals over the live set: **`Sprintf` ×6, `Errorf` ×11, `Fprintf` ×3** — 20
calls in 10 declarations, which is G-5's whole live footprint. Verb set: **`%d` ×12, `%s` ×3, `%v` ×2, `%+v` ×2, `%x` ×1,
`%q` ×1** — `%v` and `%q` are new, and both arrive with `DescribeConfChange`.

**What this does to §7's three options.** The verb set on live paths is small
and closed — `%d`, `%x`, `%s`, `%v`, `%+v`, `%q` — over `uint64`, `string`,
`[]byte`, five enum types and two pointer-to-struct types. But **option 2 (the
panic-message seam) covers only 4 of the 11 rows**: `raft.go:1332` is a live
string on a decision path, `raft.go:491` and `util.go:250-255` are live
strings, and the six `Errorf` rows are error VALUES.
An `Errorf` seam is nearly free, but for a sharper reason than "nobody reads
the text", and the sharper reason has a condition attached. Reading every
consumer: `raft.go:1017` branches on `err != nil && err != errBreak` — an
IDENTITY comparison against a sentinel; `confchange.go:73`/`:137`/`:352`
propagate; and the terminus is `raft.go:1967`'s `panic(err)` (plus
`logger.Panicf` for the scan). So what raft observes of an error is its
NIL-NESS and its IDENTITY, never its text — which is exactly why a seam is
defensible AND why the constructor behind it must preserve pointer identity
(`errors.New` returns a pointer; two errors with equal text are distinct). The
probe file does; a seam that returned a shared value would silently make
`err == errBreak` true everywhere. That is G-2 again, from the other side. `raft.go:1332` is the site that decides the ruling: the
only thing anyone reads off it is EMPTINESS, so a seam is defensible, but it
must be argued about a value the algorithm branches on — not waved through as
a message.

### 2.5 The probe-delta ledger (what the walk touches, and nothing else)

Probe deltas live in the walk's work copy and in `tools/raftsubject/probe/`;
`raftsubject/` never sees them. Each one stands in for a gap above.

| probe delta | stands in for | rows |
|---|---|---|
| `(*lockedRand).Intn` body replaced; `crypto/rand`, `math/big` imports DELETED (not blanked — a blank import is still a node of the initialization schedule, so blanking does not get past H-9's refusal) | H-9 | 1 |
| `probe/errors_new.go` injected + 9 package-level `errors.New(` call sites rewritten to it (Go's own implementation, pointer identity preserved so `err == ErrCompacted` still discriminates) | G-2, G-3 | 10 |
| 3 `$drop-import:errors` rows for the files where those were the only uses | walk artefact | 3 |

The retired pre-merge plan added 35 further body replacements (the `Intn` seam
above is its 36th) and **22** further import drops — all artefacts of the
missing method quarantine, not gaps.

**THE MASKING LIMIT, and the row it costs.** The first delta above is not free
and the first draft treated it as if it were. Replacing `(*lockedRand).Intn`'s
body is FORCED — the body cannot type-check once the imports H-9 refuses on are
dropped — but the consequence is that **the draw's own refusal never reaches
the wire the census reads**, so `Intn` appeared in no gap row and in no liveness
verdict, and G-1 read as a pure export-blocker. It is neither: the
export-blocker is H-9 (a frontend defect, in its own row now), and the draw is
a LIVE RUN-BLOCKER —
`Intn ← resetRandomizedElectionTimeout ← becomeFollower ← (*raft).Step`.

`sweep.py` un-masks it the only way the frontend allows: a SINGLE-package probe
carrying the method verbatim, where H-9's early return (`load.go:360`) means the
init graph is never built and the emitter reaches the body. It exports clean and
quarantines exactly `lockedRand.Intn`, with
`package-selector call rand.Int (package "crypto/rand" surface not modeled)`.
That is G-1's row, and it is a measured refusal, not a reconstructed one. The
instrument fails closed in the useful direction too: if a later frontend models
`crypto/rand`, the probe stops finding `Intn` quarantined and `sweep.py` exits
telling you to retire the row.

**The general rule this establishes: any probe delta that replaces a BODY masks
whatever that body would have refused, and owes a separate census.** Only this
one does today. `$drop-import` and `$rewrite` deltas do not mask (they change a
declaration's initializer or its imports, not the bodies the census reads).

---

## §3 Judgement calls

- **JC-7: the root package is vendored even though the tree cannot run yet.**
  The alternative was to keep the sweep in scratch and leave `raftsubject/` at
  W2.1's shape. Vendoring makes the derivation, the digests and the ledger
  carry the root package now, and makes every gap above reproducible by
  `frontier.py` rather than by a description of a scratch tree. The cost is
  real and is stated in §1: the tree exports only with the recorded probe
  deltas, so W2.1's end-to-end `probe-main.go` demonstration (§5 of that log)
  no longer runs over the whole tree — it runs over the packages it always
  covered, and `raft` now needs H-9 and G-2 (or G-3) before it joins.
- **JC-8: the `proto` stand-in is fail-closed in ALL FOUR functions, including
  `Clone`.** A working `Clone` was within reach (`plain_clone.go` already
  generates the per-type half; the stand-in would be a type switch). It was
  deliberately not written: `Clone` is W4's H-1 work with a differential
  obligation attached, and a shim that half-works is exactly the thing the
  ruling's requirement (b) exists to prevent. The tree type-checks and lowers;
  it stops loudly the first time it needs a codec.
- **JC-9: a walk plan's expectations are "what the frontend said at that
  step", not per-declaration causes.** The frontend reports one refusal at a
  time and does not name the declaration carrying it, so a walk cannot
  attribute causes; the CENSUS can, because every declaration reports its own.
  The plan header says so, and §2.2 is the inventory.
- **JC-10: `bootstrap.go` is vendored although `Bootstrap` is dead.** Dropping
  a whole upstream file is a bigger delta than keeping dead code, and its
  deadness is now a MEASURED fact (§2.3) rather than a scoping assumption — it
  is what retires H-1's `proto.Marshal` item.

---

## §4 Handoff items

W2.1's H-1…H-8 stand except where noted. New and updated:

| id | item | owner |
|---|---|---|
| H-3 | **DISCHARGED** for declared methods by `c7938b25` (merged to `main`); all 10 W2.1 frontier rows retire. Residual: method STENCILS of generic types still fail the whole export (`mono.go:495`, `flushTypeInsts`). | closed / frontend lane |
| H-4 | **DISCHARGED** — statement-position `copy` fixed by `f495724e` (merged to `main`). | closed |
| H-5 | `slices.SortFunc` — still open, but MEASURED OFF the twin's path: its only consumer (`MajorityConfig.Describe`) is dead under a RawNode harness. Priority drops. | W1 |
| H-6 | **RULED 2026-08-20 (§5, Q3): OPTION 1** — a modeled `Sprintf` subset over the measured verb/kind set, differential-pinned per verb. Site census and argument kinds: §2.4 (`Sprintf` ×6, `Errorf` ×11, `Fprintf` ×3; verbs `%d %s %v %+v %x %q`). Note the finding that a panic-message seam would have covered only 4 of 11 live rows — and that discharging H-6 does NOT unblock `newRaft`, which also needs G-9's `strings.Join`. | W4.1 |
| **H-9** | **The inittask double-escape defect** (§2.2): `buildInitGraph` re-escapes an already-escaped dependency prefix, so ANY multi-package program whose stdlib closure reaches `crypto/internal/entropy/v1.0.0` refuses. 6-line repro in this log. Blocks the raft export today, independent of the jitter design. | frontend lane |
| **H-10** | **`errors.New` is unmodeled** (G-2). 26 raft call sites. The E5 shim shape is Go's own implementation (a 3-line struct + method); the probe file `tools/raftsubject/probe/errors_new.go` is that body, written to be liftable. | frontend lane |
| **H-11** | **Package-level variables have no per-declaration quarantine** (G-3) — the H-3 analogue for `var`. Needs a decision about what a quarantined global's READ does (fail closed on use, presumably), which is why it is a ticket and not a patch. | frontend lane |
| **H-12** | **Promoted / embedded `sync.Mutex` operations** (G-6). `MemoryStorage` is the raft-path instance; the general shape is "an embedded sync primitive's promoted method in statement/defer position". 8 live declarations. | semantics / frontend lane |
| **H-13** | **`bytes.Equal`** (G-7) — one live site, in `(*raft).Step`. Shim-shaped, like `errors.New`. | frontend lane |
| **H-14** | **Selector call on an imported package-level variable of an unexported type** (G-8) — `binary.LittleEndian`; 2 live declarations in `read_only.go`. A language/imports gap, not a raft quirk: 12-line repro in §2.2. | frontend lane |
| **H-15** | **The jitter seam decision** (G-1, master plan §W3.1). Now a LIVE RUN-BLOCKER with a measured refusal, not a design question deferred behind an export blocker (§2.5). The fix direction is the election-jitter CHOICE SITE: jitter is nondeterminism and belongs to the envelope, so the range `[electionTimeout, 2*electionTimeout)` is what gets a latitude entry — never a modeled `crypto/rand` + `math/big`. Evidence that this is faithful rather than convenient: upstream itself treats the value as injectable (`rafttest`'s `set-randomized-election-timeout`), and the whole draw is one method body. Scheduled in **W4.1**. | W3.1 / W4.1 |
| **H-16** | **DISCHARGED 2026-08-20.** H-3 landed (`c7938b25`), the pre-merge plan is deleted, and `frontier-plan.tsv` now holds the merged-frontend walk with its ten `errors.New` expectations re-pinned onto the refusal string `0bfb8edd` introduced (`package-selector call errors.New (package "errors" surface not modeled)`). Its content survives as §2.2's difference measurement. | closed |
| **H-17** | **`strings.Join`** (G-9) — one live site, `raft.go:496` in `newRaft`. Shim-shaped, like `errors.New`. Listed separately because it was MASKED behind `newRaft`'s `fmt.Sprintf` and is the reason H-6 alone does not unblock `NewRawNode`. | frontend lane |
| **H-18** | **`strings.Builder`** (G-10) — the declaration-only stub is live through `DescribeConfChange` only; 1 of the tree's 10 `Builder` users. Retires for free if the H-6 ruling's modeled subset covers `Fprintf` into a `Builder`, so it is a rider on H-6 rather than its own arc. | frontend lane |
| **H-19** | **`node_decls.go` keeps `ErrStopped` for chunk granularity, and it costs an `errors.New` row** (§1(a)). Splitting the `var (…)` block would retire one of G-2's nine globals at the cost of a sub-declaration delta. Decide when `select` mode next changes. | subject lane |

---

## §5 The rulings (user, 2026-08-20)

Two open questions this lane raised were ruled by the user on 2026-08-20. Both
are recorded here and in the harness design note; neither is this lane's to
re-open.

**Q2 — the H-2 logger seam. The revised recommendation is ADOPTED:** keep
upstream `logger.go` VERBATIM and let the HARNESS supply the `Logger`, rather
than putting a fixed-string `Panic`/`Panicf` seam in the subject. The teeth stay
where they belong (`assertConfStatesEquivalent` still panics, because the
harness's `Panic` panics) without a growing delta on upstream text.

**With one amendment the audit forced, and it is load-bearing.** The
recommendation as first written rested on "raft reaches for the package default
at exactly one place, `Config.validate`". That is false: `getLogger()` has
**six call sites**, and four of them are in `MemoryStorage`
(`storage.go:154, 252, 276, 322` — `Entries`, `CreateSnapshot`, `Compact`,
`Append`), of which **three are live** under the twin. Those paths never consult
`Config.Logger`; they read the package-level registry. So the harness supplies
**BOTH**: it sets `Config.Logger` AND calls `raft.SetLogger(...)`, with the same
logger value. Details and the shared-nothing side condition: harness design §5.

**Q3 — the fmt story. OPTION 1 is ruled:** model a `Sprintf` SUBSET over the
measured verb/kind set, differential-pinned per verb — not a panic-message seam,
not a whole-`fmt` model. The census that the ruling ranges over is §2.4, and the
audit's correction to it is part of the ruling's input: the live surface is
`Sprintf` ×6, `Errorf` ×11 and `Fprintf` ×3 (the three `Fprintf`s are
`DescribeConfChange`'s, which the first liveness census could not see), and the
verb set is `%d %s %v %+v %x %q` — `%v` and `%q` arriving with those same three
sites. Option 2 would have covered 4 of the 11 rows.

---

## §6 The gate

`GOLEAN_MEM_MAX=24G GOLEAN_ALLOW_NO_DIFF=1 scripts/ci` → **PASS**, with the two
visible notes the escape hatch owes:

```
note negative baseline diff NOT RUN (no record; explicitly allowed here)
note differential baseline diff NOT RUN (no record; explicitly allowed here)
```

The hatch is used as the contract intends: this is a fresh lane worktree on a
docs-and-subject-tree arc. **No runtime code was touched** — `Corpus/`,
`baselines/`, GoCore, `tools/nativefrontend/` and `scripts/` are all untouched
(the diff is `raftsubject/**`, `tools/raftsubject/**` and two docs) — so no
differential is owed, and the notes say so where a reader will see them.

Re-run at the audit-fix tip (2026-08-20), after rebasing onto `main` @
`7ca8908e`: **PASS**, same two notes, and the scope argument is unchanged —
that round's diff is two docs, `tools/raftsubject/README.md`, the re-pinned
`frontier-plan.tsv`, the deleted `frontier-plan-postmerge.tsv` and the new
`sweep.py`. The rebase was zero-overlap: `main`'s delta over the merge base
touches no path this lane owns.

The lane's own instruments are the real check on this arc's claims, and all
five are green at the tip (re-run 2026-08-20 against the merged frontend, built
`GO111MODULE=off go build -o artifacts/nativefrontend ./tools/nativefrontend`):

| instrument | result |
|---|---|
| `derive.py --check` | clean — the whole tree, 15 new files included, is the derivation's output |
| `difftest.py` | PASS (unchanged; raftpb untouched) |
| `frontier.py` (default plan, merged frontend) | 15 rows, 0 mismatches, `EXPORTS CLEAN`, exit 0 |
| `sweep.py` | 53 quarantined / **26 LIVE** (19 + 6 + 1), fixpoint in 2 rounds, **residual sinks: none** |
| `go build` over the subject tree (GOPATH scratch) | clean |

`sweep.py` is the one to re-run after any frontend change: it is the only
instrument that prints the headline, and it fails closed in three places — a
stale plan (PASS 1 does not export), a flattening that stops type-checking
(PASS 2 does not export), and a `crypto/rand` that has become modeled (the G-1
probe stops finding `Intn` quarantined).
