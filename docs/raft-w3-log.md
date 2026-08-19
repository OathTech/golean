# Raft W2.2 campaign log — the raft.go frontier sweep

Lane: `raft-w3` (worktree `.claude/worktrees/raft-w3`), supervised arc under the
standing merge/audit protocol. Charter: master plan
(`docs/2026-08-15_raft-master-plan.md`) §W1.3 and §W2.2/§W2.3 — the raft.go
sweep the roadmap has never had a number for, and the machine-twin harness
DESIGN (`docs/2026-08-20_machine-twin-harness-design.md`). Owns
`raftsubject/` additions, `tools/raftsubject/` extensions, and these two docs.
Does NOT touch `Corpus/`, `baselines/`, GoCore, `tools/nativefrontend/` or
`scripts/`; every need found there is a handoff row, not a change.

Base: `main` @ `ee1e5628`. `deps/raft` @ `56e32004b1af3a4cb625fbfe5dbca24fb6023d09`
(unchanged from W2.1). Predecessor: `docs/raft-w2-log.md`.

**The measurement in one line.** With the raft ROOT package vendored, the
post-merge frontend needs **3 fixes to export the subject tree** and **5 more
for a RawNode-driven twin to RUN** — eight items, of which two (the protobuf
codec, the fmt story) were already open tickets. The pre-merge frontend needs
**35 more declaration-level neutralisations on top of those**, all of them
methods, all retired by the pending H-3 merge.

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
`IsEmptyHardState`, `isHardStateEqual`, `SnapshotStatus`, `emptyState`,
`ErrStopped` and `confChangeToMsg` — they live in `node.go` beside the `node`
goroutine loop the plan of record excludes (master plan §W2.2: "RawNode-driven
node loops (no node.go / context / time)"). The new `select` mode keeps exactly
those declarations BYTE-VERBATIM and drops the other 26, dropping the `context`
import with them. It fails closed in both directions: a named declaration that
is not found refuses the derivation (upstream moved it — re-read the subset),
and so does a dropped import whose package name still appears in the kept text.
The dropped set is D-8 in the ledger below.

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

Instruments, all tracked and re-runnable:

- `tools/raftsubject/frontier.py` — the walk, extended with three PROBE-DELTA
  actions (`$drop-import`, `$rewrite`, `$add`) because the raft root package
  refuses in places a body replacement cannot reach: an import refuses before
  any declaration is read, and a package-level `var` has no body to replace.
- `tools/raftsubject/frontier-plan.tsv` — the PRE-merge plan (the frontend on
  `main` today), 71 action rows + terminal.
- `tools/raftsubject/frontier-plan-postmerge.tsv` — the POST-merge plan (a
  frontend carrying H-3), 14 action rows + terminal.
- `tools/raftsubject/reachability.py` — **new.** Answers the question H-3
  moves us to: since a refusal no longer blocks the export but lands as a
  signature-carrying stub that refuses WHEN CALLED, a quarantined declaration
  on a dead path costs nothing and one on a live path is a run-time stop. It
  walks the call graph OF THE EXPORTED WIRE (the frontend's own resolved
  callees, including `func-value` references) from a named entry set and prints
  each verdict with the path that witnesses it.

Both emitters were built and run: `main` @ `ee1e5628` and the unmerged
`bugfix-arc` @ `529bab12` (built read-only into this lane's `artifacts/`).

### 2.1 The headline: what the pending merge does to this tree

Before anything else, the W2.1 inventory was re-run under both emitters on the
UNCHANGED W2.1 tree (quorum + tracker + raftpb + logger):

| frontend | result |
|---|---|
| `main` | the 10-row walk reproduces exactly, `EXPORTS CLEAN`, exit 0 |
| `bugfix-arc` | **all 10 rows retire**: the tree exports clean with ZERO neutralisations |

So every one of W2.1's F-1…F-10 is a pre-merge artefact. Nine of them retire
because H-3 quarantines methods per declaration; F-6 (`copy` in statement
position, handoff H-4) retires because the bug-fix arc FIXED it — `copy` and
`recover` are legal expression statements (spec#Expression_statements), and the
raft path was named in that commit's message. **H-4 is discharged; H-3 is
discharged as far as declared methods go** (its own residual scope — method
STENCILS of generic types — is recorded in `mono.go`).

### 2.2 The gap inventory over the full tree, post-merge

Method: derive the tree, walk it with the post-merge plan (which applies the 3
export-blocking probe deltas), export, and census every declaration the wire
marks `unsupported`. **50 subject declarations are quarantined** (16 plain
functions, 34 methods) — plus the three promoted `MemoryStorage.{Lock, TryLock,
Unlock}` stubs, which are the G-6 cause seen from the method-set side and are
counted with it rather than twice. The other 36 quarantined entries are
imported stdlib stubs (`bytes.Buffer` ×24, `strings.Builder` ×9, `sync.Mutex`
×3), which is the pre-existing declaration-only-stub contract, not a raft gap.

Grouped by CAUSE, which is what a work item is:

| # | gap | where it bites | live? | status |
|---|---|---|---|---|
| **G-1** | **the election-jitter draw** — `raft.go:2054` `globalRand.Intn(...)`, whose one implementation (`(*lockedRand).Intn`, `raft.go:96`) calls `crypto/rand.Int` + `math/big`. What actually refuses is not the draw: it is a **frontend defect** (below). | export-BLOCKING | — | new (defect) + W3.1 (design) |
| **G-2** | **`errors.New` is not modeled.** 26 call sites; 9 of them are package-level `var Err… = errors.New(…)`. | export-BLOCKING at the 9 globals; quarantines 6 more declarations at the others | 5 of the 6 live | **new** |
| **G-3** | **a package-level variable has no per-declaration quarantine** — the structural half of G-2. A method with an unlowerable body becomes a refusing stub (H-3); a `var` with an unlowerable initializer still refuses the WHOLE export. | export-BLOCKING | — | **new** |
| **G-4** | **the protobuf codec** — `proto.Clone` / `proto.Size` / `proto.Unmarshal`. | run-blocking (the stand-in panics) | all three LIVE | **known: H-1** |
| **G-5** | **`fmt` on live paths** — `Sprintf`/`Errorf` in 9 live declarations (§2.4). | run-blocking | LIVE | **known: H-6** |
| **G-6** | **promoted / embedded `sync.Mutex` operations.** `MemoryStorage` embeds `sync.Mutex` and calls `ms.Lock()` / `defer ms.Unlock()`; only DIRECT statement/defer-position sync ops on a named field are modeled. | run-blocking | 8 methods LIVE (+3 promoted stubs) | **new** |
| **G-7** | **`bytes.Equal`** — `raft.go:1097`, inside `(*raft).Step`. | run-blocking | LIVE (the step function) | **new** |
| **G-8** | **a selector call on an imported package-level variable of an UNEXPORTED type** — `binary.LittleEndian` (`var LittleEndian littleEndian`, `encoding/binary`), at `read_only.go`'s `recvAck` and `heartbeatCtx`. The frontend renders it `field selector on anonymous struct type invalid type`, i.e. it never resolved the type. 12-line repro below. | run-blocking | both LIVE | **new** |
| — | `slices.SortFunc` (H-5) | quarantines `MajorityConfig.Describe` | **dead** under the harness | known: H-5, and NOT on the twin's path |

**THE NUMBER THE ROADMAP ASKED FOR.** Between the post-merge frontend and
"RawNode-driven raft.go exports clean" stand **3 gaps** (G-1, G-2, G-3).
Between it and "the twin RUNS" stand **5 more** (G-4…G-8). Total **8**, of
which **2 are the known tickets** (G-4 = H-1's codec, G-5 = H-6's fmt story)
and **6 are new** — and of those six, three are one-line-to-one-function
frontend items (`errors.New`, `bytes.Equal`, and the inittask defect below).

Against the PRE-merge frontend, add **35 declaration-level blockers** on top
(34 quarantined methods + `Inflights.grow`): each must be neutralised for the
export to proceed at all. That is the whole content of the difference between
the two tracked plans — 71 action rows vs 14.

**G-1's actual refusal is a frontend defect, and it is not about raft.**
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

### 2.3 Liveness: which of the 50 must lower before the twin runs

`reachability.py`, entries = the RawNode-driven twin's API surface
(`NewRawNode`, `Tick`, `Step`, `HasReady`, `Ready`, `Advance`, `Propose`,
`Campaign`, `ApplyConfChange`, `ProposeConfChange`, `NewMemoryStorage`,
`SetHardState`, `Append`, `CreateSnapshot`, `IsEmptyHardState`, `IsEmptySnap`).

**25 of the 50 are LIVE; 25 are dead** (the split is exact, and the two sets
are listed in full below). The live set, by cause:

- **G-6 (8)** `MemoryStorage.{Append, CreateSnapshot, Entries, FirstIndex,
  LastIndex, SetHardState, Snapshot, Term}` — the Storage the twin runs on.
  `ApplySnapshot` and `Compact` are dead only because the twin as designed
  never compacts; the moment it does, they join. (The three promoted
  `MemoryStorage.{Lock, TryLock, Unlock}` stubs are the same cause seen from
  the method-set side and are not counted again.)
- **G-5 (9)** `raft.newRaft`, `raft.stepLeader`, `(*raft).restore`,
  `voteRespMsgType`, `(*raftLog).scan`, `confchange.Changer.apply`,
  `confchange.checkInvariants`, `(*ConfChangeV2).EnterJoint`,
  `Progress.SentEntries`.
- **G-2 (5)** `Changer.{EnterJoint, LeaveJoint, Simple}`, `Config.validate`,
  `(*raft).Step`.
- **G-8 (2)** `readOnly.recvAck`, `readOnly.heartbeatCtx`.
- **the rendering exception (1)** `raft.DescribeConfChange` — see below.
- **G-7 shares a declaration rather than adding one:** `(*raft).Step`'s FIRST
  refusal is `errors.New` and `bytes.Equal` is behind it. A census names ONE
  cause per declaration — the first the emitter meets — so the cause list is
  longer than the declaration list, and the second-order probe below is how the
  hidden ones were found. 8+9+5+2+1 = 25 distinct declarations.

**The dead 25, in full:** `confchange.Describe`, `DescribeConfState`,
`DescribeEntry`, `DescribeHardState`, `DescribeReady`, `DescribeSnapshot`,
`DescribeSoftState`, `describeMessageWithIndent`, `describeTarget`,
`ConfChangesFromString`, `ConfChangesToString`, `quorum.Index.String`,
`MajorityConfig.Describe`, `MajorityConfig.String`, `VoteResult.String`,
`MemoryStorage.ApplySnapshot`, `MemoryStorage.Compact`, `RawNode.Bootstrap`,
`StateType.MarshalJSON`, `Status.MarshalJSON`, `logSlice.valid`,
`raftLog.String`, `tracker.Config.String`, `Progress.String`,
`ProgressMap.String`. Twenty of them are the rendering family — **with one
exception, and it is a correction to W2.1.** `raft.DescribeConfChange` is **LIVE**: `stepLeader` passes
`DescribeConfChange(cc)` as an ARGUMENT to `r.logger.Infof` (`raft.go:1339`).
W2.1 §6(a) argued that a no-op logger makes rendering runtime-dead because "Go
evaluates the argument (a field read) but only `fmt` calls `String`". That is
right for a `%s` over a value and WRONG when the argument is itself a call to a
rendering function: Go evaluates it before the call, no-op body or not. Exactly
one such site exists in the root package (measured by grep over every
`logger.*f` call), and it is this one. The conclusion "rendering is
quarantine-dead" survives for every rendering declaration but this one, and it
is now a measurement with a named exception rather than a categorical claim.

**Two honest limits on the liveness verdicts, both in the instrument's
docstring.** (i) Interface dispatch is over-approximated — a call to
`Logger.Infof` marks every concrete `Infof`; so LIVE is a candidate that the
path witness lets you check, while `dead` is the sound direction. (ii) A
quarantined declaration is a SINK (no body on the wire), so the walk stops
there. Both were exercised: the sink effect initially hid `proto.Unmarshal`,
`readOnly.recvAck` and `readOnly.heartbeatCtx` behind `stepLeader`.

**The second-order probe.** To see behind the sinks, a scratch tree was built
with every DEAD quarantined declaration neutralised and the three live causes
(fmt, `bytes.Equal`, the promoted mutex ops) flattened, then re-exported and
re-walked. Result, and it is the reassuring half of this report: **behind the
sinks there is nothing new.** The only declarations still quarantined in that
tree are the ones the flattening deliberately left (and, in one variant,
upstream's `DefaultLogger`). The gap list above is therefore CLOSED over this
subject tree — the census covers every declaration, live or dead, because the
frontend lowers every declaration regardless of reachability.

That probe is also what promoted `proto.Unmarshal` to LIVE (`<- stepLeader <-
becomeLeader <- … <- RawNode.Step`), confirming W2.1's audit-widened H-1
ranking: the DECODE side is on a decision path, `Marshal` is not on any path
the twin takes, and `Bootstrap`/`RawNode.Bootstrap` are dead — so H-1's item 3
retires for free, exactly as W2.1 predicted.

### 2.4 The fmt site census (input to the H-6 ruling — §7 of the W2 log)

Every LIVE `fmt` site in the vendored tree, with what the result is USED for.
This is the input the fmt ruling was missing; the ruling itself is W2.3's.

| site | call | argument kinds | the result is… |
|---|---|---|---|
| `raft.go:1332` | `Sprintf("possible unapplied conf change at index %d (applied to %d)", …)` | `uint64`, `uint64` | **a live value on a decision path**: assigned to `failedCheck`, and `failedCheck != ""` is what makes `stepLeader` rewrite a proposed conf change to a no-op |
| `raft.go:491` | `Sprintf("%x", n)` in a loop, then `strings.Join` | `uint64` | a logger ARGUMENT — but computed unconditionally on `newRaft`'s path, no-op logger or not |
| `raft.go:1339` | `logger.Infof("%x … %s … %s: %s", …, DescribeConfChange(cc), r.trk.Config, failedCheck)` | `uint64`, rendered strings, `tracker.Config` | the argument evaluation is live (see §2.3); the formatting is not |
| `raft.go:1933` | `panic(Sprintf("unable to restore config %+v: %s", cs, err))` | `*pb.ConfState`, `error` | a panic message |
| `util.go:79` | `panic(Sprintf("not a vote message: %s", msgt))` | `pb.MessageType` (a plainpb enum with a fail-closed `String`) | a panic message |
| `progress.go:183` | `panic(Sprintf("sending append in unhandled state %s", pr.State))` | `tracker.StateType` | a panic message |
| `raftpb/confchange.go:109` | `panic(Sprintf("unknown transition: %+v", c))` | `*ConfChangeV2` (fail-closed `String`) | a panic message |
| `log.go:488` | `Errorf("got 0 entries in [%d, %d)", lo, hi)` | `uint64`×2 | an error VALUE returned to a caller that branches on `err != nil` |
| `confchange.go:167` | `Errorf("unexpected conf type %d", cc.GetType())` | enum | ditto |
| `confchange.go:290…327` | `Errorf` ×10, mostly `"%d …"` | `uint64` | ditto (`checkInvariants`) |

**What this does to §7's three options.** The verb set on live paths is small
and closed — `%d`, `%x`, `%s`, `%+v` — over `uint64`, `string`, four enum
types and two pointer-to-struct types. But **option 2 (the panic-message seam)
covers only 4 of the 10 rows**: `raft.go:1332` is a live string on a decision
path, `raft.go:491` is a live string, and the six `Errorf`s are error VALUES.
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
| `(*lockedRand).Intn` body replaced; `crypto/rand`, `math/big` imports DELETED (not blanked — a blank import is still a node of the initialization schedule, so blanking does not get past H-9's refusal) | G-1 | 1 |
| `probe/errors_new.go` injected + 9 package-level `errors.New(` call sites rewritten to it (Go's own implementation, pointer identity preserved so `err == ErrCompacted` still discriminates) | G-2, G-3 | 10 |
| 3 `$drop-import:errors` rows for the files where those were the only uses | walk artefact | 3 |

The pre-merge plan adds 35 further body replacements (the `Intn` seam above is
its 36th) and 25 further import drops — all artefacts of the missing method
quarantine, not gaps.

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
  covered, and `raft` now needs G-1…G-3 before it joins.
- **JC-8: the `proto` stand-in is fail-closed in ALL FOUR functions, including
  `Clone`.** A working `Clone` was within reach (`plain_clone.go` already
  generates the per-type half; the stand-in would be a type switch). It was
  deliberately not written: `Clone` is W4's H-1 work with a differential
  obligation attached, and a shim that half-works is exactly the thing the
  ruling's requirement (b) exists to prevent. The tree type-checks and lowers;
  it stops loudly the first time it needs a codec.
- **JC-9: the pre-merge plan's expectations are "what the frontend said at that
  step", not per-declaration causes.** The frontend reports one refusal at a
  time and does not name the declaration carrying it, so a walk cannot
  attribute causes; the post-merge census can, because every declaration
  reports its own. The plan header says so, and §2.2 is the inventory.
- **JC-10: `bootstrap.go` is vendored although `Bootstrap` is dead.** Dropping
  a whole upstream file is a bigger delta than keeping dead code, and its
  deadness is now a MEASURED fact (§2.3) rather than a scoping assumption — it
  is what retires H-1's `proto.Marshal` item.

---

## §4 Handoff items

W2.1's H-1…H-8 stand except where noted. New and updated:

| id | item | owner |
|---|---|---|
| H-3 | **DISCHARGED** for declared methods by `bugfix-arc` @ `f1cf7edc`; all 10 W2.1 frontier rows retire. Residual: method STENCILS of generic types still fail the whole export (`mono.go:495`, `flushTypeInsts`). | closed / frontend lane |
| H-4 | **DISCHARGED** — statement-position `copy` fixed by `bugfix-arc` @ `1ca434b2`. | closed |
| H-5 | `slices.SortFunc` — still open, but MEASURED OFF the twin's path: its only consumer (`MajorityConfig.Describe`) is dead under a RawNode harness. Priority drops. | W1 |
| H-6 | The fmt ruling — now has its site census and argument-kind list (§2.4), and the finding that a panic-message seam covers 4 of 10 live rows. | W2.3 |
| **H-9** | **The inittask double-escape defect** (§2.2): `buildInitGraph` re-escapes an already-escaped dependency prefix, so ANY multi-package program whose stdlib closure reaches `crypto/internal/entropy/v1.0.0` refuses. 6-line repro in this log. Blocks the raft export today, independent of the jitter design. | frontend lane |
| **H-10** | **`errors.New` is unmodeled** (G-2). 26 raft call sites. The E5 shim shape is Go's own implementation (a 3-line struct + method); the probe file `tools/raftsubject/probe/errors_new.go` is that body, written to be liftable. | frontend lane |
| **H-11** | **Package-level variables have no per-declaration quarantine** (G-3) — the H-3 analogue for `var`. Needs a decision about what a quarantined global's READ does (fail closed on use, presumably), which is why it is a ticket and not a patch. | frontend lane |
| **H-12** | **Promoted / embedded `sync.Mutex` operations** (G-6). `MemoryStorage` is the raft-path instance; the general shape is "an embedded sync primitive's promoted method in statement/defer position". 8 live declarations. | semantics / frontend lane |
| **H-13** | **`bytes.Equal`** (G-7) — one live site, in `(*raft).Step`. Shim-shaped, like `errors.New`. | frontend lane |
| **H-14** | **Selector call on an imported package-level variable of an unexported type** (G-8) — `binary.LittleEndian`; 2 live declarations in `read_only.go`. A language/imports gap, not a raft quirk: 12-line repro in §2.2. | frontend lane |
| **H-15** | **The jitter seam decision** (G-1, master plan §W3.1): model `crypto/rand.Int` as a choice site, or seam `(*lockedRand).Intn` as a recorded subject delta. Evidence for the seam: upstream itself treats the value as injectable (`rafttest`'s `set-randomized-election-timeout`), and the whole draw is one method body. | W3.1 / W2.3 |
| **H-16** | **The tracked default frontier plan flips at the merge.** `frontier-plan.tsv` is the pre-merge walk and goes red once H-3 lands; `frontier-plan-postmerge.tsv` becomes the default then, and the pre-merge plan is retired (its content is §2.2's difference measurement, already recorded here). | operator, at merge time |

---

## §5 The gate

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

The lane's own instruments are the real check on this arc's claims, and all
four are green at the tip:

| instrument | result |
|---|---|
| `derive.py --check` | clean — the whole tree, 15 new files included, is the derivation's output |
| `difftest.py` | PASS (unchanged; raftpb untouched) |
| `frontier.py` (default, pre-merge plan, `main` frontend) | 72 rows, 0 mismatches, `EXPORTS CLEAN`, exit 0 |
| `frontier.py --plan …-postmerge.tsv` (bug-fix-arc frontend) | 15 rows, 0 mismatches, `EXPORTS CLEAN`, exit 0 |
| `go build` over the subject tree (GOPATH scratch) | clean |
