# W3.1 reachability census (2026-08-27)

Provenance: [AGENT] instrument — produced by a read-only census agent
from the driver/harness/subject sources; every claim file:line-
anchored. STATUS: a costing and case-analysis INPUT, not a proof
artifact — Wave 3.1 workers re-verify the arms they build on (the
charter's standing rule), and the UNDECIDED items U1-U5 are handled
as §4.3 states (U1 costed reachable; U3 = safety obligations, never
pruned). The census text follows verbatim.

---

# REACHABLE-HANDLER CENSUS — GoLean raft campaign, Wave 3.1 (fragment T1)

Subject: `/home/dev/projects/golean/raftsubject/` (packages `raft`, `tracker`, `quorum`, `confchange`, `raftpb`, `proto`)
Harness: `/home/dev/projects/golean/tools/raftsubject/twin-lib.go`
Driver: `/home/dev/projects/golean/tools/raftsubject/twin-chdriver.go` (`runTwinChoice`, T1 fragment)

Fragment as verified from the driver: `installLogger()` (chdriver:39) → `newTwin(3,2)` (chdriver:40) → one `op{opCampaign,node:1}` (chdriver:44) → per round either `deliverIdx(picked)` (chdriver:67) or, at quiescence with pending commands, `op{opPropose,node:1}` (chdriver:78); fuel 400; **no `opTick`, no `opDeliver`/`opDrain*` kinds, no second campaign, no conf-change proposal.**

---

## 0. CONFIGURATION FACTS THAT DRIVE EVERY PRUNE

All from the `raft.Config` literal at **twin-lib.go:207-215** (fields not named take their zero value):

| Field | Value | Consequence (with site) |
|---|---|---|
| `AsyncStorageWrites` | **false** (absent) | `rawnode.go:56` sets `rn.asyncStorageWrites=false` → `readyWithoutAccept` takes the **else** at `rawnode.go:174-184`; `acceptReady` takes the `!async` branch at `rawnode.go:410-427`; `Advance`'s panic `rawnode.go:481-483` never fires; `applyUnstableEntries` returns **true** (`rawnode.go:444`) → `nextCommittedEnts(allowUnstable=true)`. **The MsgStorageAppend/MsgStorageApply *messages* are dead; their *Resp* twins are live** (see §2.1). |
| `PreVote` | **false** | `raft.go:1210` `if r.preVote` false → `hup(campaignElection)`; `campaign` always takes the else at `raft.go:1057`. Kills MsgPreVote/MsgPreVoteResp, `becomePreCandidate` (`raft.go:936`), `StatePreCandidate`. |
| `CheckQuorum` | **false** | `raft.go:1122` `inLease` always false; `raft.go:1153` lower-term MsgApp/MsgHeartbeat special-case disabled; `tickHeartbeat`'s MsgCheckQuorum (`raft.go:887`) dead. |
| `ReadOnlyOption` | `ReadOnlySafe` (0) | irrelevant — no MsgReadIndex ever created. |
| `MaxUncommittedEntriesSize` | 0 → `noLimit` (`raft.go:332-334`) | `increaseUncommittedSize` (`raft.go:2117`) **never returns false** → `appendEntry`'s drop (`raft.go:847`), `becomeLeader`'s `Panic("empty entry was dropped")` (`raft.go:983`), and `stepLeader`'s `return ErrProposalDropped` (`raft.go:1369`) are unreachable. |
| `MaxInflightMsgs` 256, `MaxInflightBytes` 0→`noLimit` | | `Inflights.Full()` never true → `maybeSendAppend`'s throttled-empty-MsgApp branch (`raft.go:658-660`, the `Full()` disjunct) never suppresses the `entries()` read. |
| `MaxSizePerMsg` 1<<20; `MaxCommittedSizePerReady` 0→1<<20 (`raft.go:338-340`) | | `applyingEntsPaused` never set → early returns at `log.go:221-223` / `log.go:249-251` dead. |
| `Logger` = `twinLogger` (non-nil) | | `validate`'s `c.Logger = getLogger()` (`raft.go:352`) not taken → **`getLogger()` (`logger.go:54`) is unreachable in T1**; only `SetLogger` (`logger.go:44`) runs. |
| `Storage` = fresh `MemoryStorage` + `ApplySnapshot{Index:1,Term:1,Voters:{1,2,3}}` (twin-lib.go:197-202) | | `InitialState` returns `hardState == nil` → `IsEmptyHardState(nil)` true → **`raft.loadState` (`raft.go:2056`) never called**; `raftLog` starts `committed=applying=applied=1`, `unstable.offset=2`. `Config.Applied`=0 → `raftlog.appliedTo` at `raft.go:504` not called. |
| Harness never compacts | `MemoryStorage.Compact`/`CreateSnapshot` never called by twin-lib | first index stays 2 forever → the snapshot family is dead (§2.4). |

---

## 1. HARNESS → LIBRARY ENTRY POINTS

Every direct call from harness code that executes in T1. (`opTick` is listed for completeness and marked NOT-IN-T1.)

| # | Harness site | Call | Callee (raftsubject file:line) |
|---|---|---|---|
| E1 | twin-lib.go:130 (`installLogger`) | `raft.SetLogger(twinLogger)` | `raft/logger.go:44` |
| E2 | twin-lib.go:197 (`newTwin`) | `raft.NewMemoryStorage()` | `raft/storage.go:119` |
| E3 | twin-lib.go:198 (`newTwin`) | `nd.st.ApplySnapshot(...)` | `raft/storage.go:218` |
| E4 | twin-lib.go:216 (`newTwin`) | `raft.NewRawNode(cfg)` | `raft/rawnode.go:51` |
| E5 | twin-lib.go:232 (`harvest`) | `nd.rn.HasReady()` | `raft/rawnode.go:448` |
| E6 | twin-lib.go:239 (`harvest`) | `nd.rn.Ready()` | `raft/rawnode.go:131` (→ `readyWithoutAccept` :139, `acceptReady` :400) |
| E7 | twin-lib.go:242 (`harvest`) | `raft.IsEmptyHardState(rd.HardState)` | `raft/node_decls.go:101` |
| E8 | twin-lib.go:243 (`harvest`) | `nd.st.SetHardState(...)` | `raft/storage.go:137` |
| E9 | twin-lib.go:248,249 | `rd.HardState.GetTerm()/GetCommit()` | `raftpb/raft.pb.go:570,584` |
| E10 | twin-lib.go:252 (`harvest`) | `nd.st.Append(rd.Entries)` | `raft/storage.go:293` |
| E11 | twin-lib.go:258 (`harvest`) | `raft.IsEmptySnap(rd.Snapshot)` | `raft/node_decls.go:105` |
| E12 | twin-lib.go:268-270 | reads `rd.SoftState.RaftState`, cmp `raft.StateLeader` | `raft/node_decls.go:23-26`, `raft/raft.go:48-54` (data, not code) |
| E13 | twin-lib.go:293 (`harvest`) | `nd.rn.Advance(rd)` | `raft/rawnode.go:477` |
| E14 | twin-lib.go:299,300,313,319,322 (`apply`) | `e.GetIndex/GetTerm/GetType/GetData`, `pb.EntryNormal` | `raftpb/raft.pb.go:304,297,311,318`; `raftpb/alias.go:18` |
| E15 | twin-lib.go:351 (`pickFor`) — *not used by the T1 driver* | `t.net[i].GetTo()` | `raftpb/raft.pb.go:459` |
| E16 | twin-lib.go:365 (`deliverIdx`) | `to.rn.Step(m)` | `raft/rawnode.go:116` |
| E17 | twin-lib.go:401 (`step`/`opTick`) | `nd.rn.Tick()` | `raft/rawnode.go:64` — **NOT IN T1** (driver never emits `opTick`) |
| E18 | twin-lib.go:406 (`step`/`opCampaign`) | `nd.rn.Campaign()` | `raft/rawnode.go:83` |
| E19 | twin-lib.go:422 (`step`/`opPropose`) | `nd.rn.Propose([]byte(cmd))` | `raft/rawnode.go:90` |
| E20 | twin-lib.go:493-504 (`stateChar`) | `raft.StateFollower/Candidate/Leader/PreCandidate` | `raft/raft.go:49-52` (constants) |
| E21 | twin-chdriver.go:64-66 | `m.GetType()`, `m.GetTo()` | `raftpb/raft.pb.go:452,459` |

**Callback direction (library → harness):** `raft` calls `Logger` methods on `twinLogger`. Only **`Infof` (twin-lib.go:112)** and **`Debugf` (twin-lib.go:110)** are actually invoked in T1 (e.g. `raft.go:1143`, `raft.go:1260`, `raft.go:1430`, `raft.go:1823`); `Warningf/Error/Errorf/Panic/Panicf/Fatal/Fatalf/Info/Debug/Warning` are never reached. **NB: argument expressions are evaluated even though the bodies are empty** — this is why `raftLog.zeroTermOnOutOfBounds` (`log.go:567`) is reachable, via the argument at `raft.go:1824` and `log.go:161`.

**Never called by the harness** (hence whole subtrees dead): `RawNode.TickQuiesced` (:78), `ProposeConfChange` (:100), `ApplyConfChange` (:111), `Status` (:493), `BasicStatus` (:500), `WithProgress` (:516), `ReportUnreachable` (:529), `ReportSnapshot` (:534), `TransferLeader` (:541), `ForgetLeader` (:547), `ReadIndex` (:555), `Bootstrap` (`bootstrap.go:32`), `MemoryStorage.Compact/CreateSnapshot/Snapshot` (`storage.go:268/243/208`), `raft.ResetDefaultLogger` (`logger.go:50`).

---

## 2. THE REACHABLE CLOSURE

Notation for "reached by": **H**=harness entry, **local**=self-directed message stepped in `Advance`, wire types by name.

### 2.1 `raft/rawnode.go` — 16 reachable

| Fn | file:line | Role | Reached by |
|---|---|---|---|
| `NewRawNode` | rawnode.go:51 | construct raft + prev{Soft,Hard}State | H(E4) |
| `RawNode.Campaign` | rawnode.go:83 | synthesizes **MsgHup** (local, `Term`=0) and steps it | H(E18) |
| `RawNode.Propose` | rawnode.go:90 | synthesizes **MsgProp** (local, `From`=self, one entry) and steps it | H(E19) |
| `RawNode.Step` | rawnode.go:116 | wire-message guard: `IsLocalMsg`+`IsResponseMsg`/`trk.Progress` checks, then `raft.Step` | H(E16); MsgVote, MsgVoteResp, MsgApp, MsgAppResp |
| `RawNode.Ready` | rawnode.go:131 | `readyWithoutAccept` + `acceptReady` | H(E6) |
| `readyWithoutAccept` | rawnode.go:139 | builds `Ready`; **takes the sync branch at :174-184**, appending only `msgsAfterAppend` entries with `To != r.id` | H |
| `MustSync` | rawnode.go:191 | sets `rd.MustSync` | `readyWithoutAccept:161` |
| `needStorageAppendRespMsg` | rawnode.go:210 | "does raft need a stability ack?" | `acceptReady:419` |
| `newStorageAppendRespMsg` | rawnode.go:266 | builds the **self-directed MsgStorageAppendResp** (To=self, From=`LocalAppendThread`, Term=`r.Term`, Index/LogTerm=`lastEntryID`) | `acceptReady:420` |
| `needStorageApplyMsg` | rawnode.go:365 | `len(CommittedEntries)>0` | via :366 |
| `needStorageApplyRespMsg` | rawnode.go:366 | ditto | `acceptReady:423` |
| `newStorageApplyRespMsg` | rawnode.go:387 | builds the **self-directed MsgStorageApplyResp** (Term=0) | `acceptReady:424` |
| `acceptReady` | rawnode.go:400 | advances prev states, **fills `stepsOnAdvance`** (:414-426), clears `msgs`/`msgsAfterAppend`, `acceptUnstable`, `acceptApplying` | `Ready:133` |
| `applyUnstableEntries` | rawnode.go:443 | returns `true` here | `readyWithoutAccept:144`, `HasReady:463`, `acceptReady:434` |
| `HasReady` | rawnode.go:448 | harvest loop condition | H(E5) |
| `Advance` | rawnode.go:477 | **replays `stepsOnAdvance` through `raft.Step` (:485)** — the only route by which self-directed and storage-resp messages enter the state machine | H(E13) |

**MsgStorageAppend/AsyncStorageWrites verdict: the async path is NOT live.** Evidence chain: twin-lib.go:207-215 omits `AsyncStorageWrites` → `rawnode.go:56` → `rn.asyncStorageWrites == false` → the `if rn.asyncStorageWrites` at **rawnode.go:163** is never entered, so `needStorageAppendMsg` (**rawnode.go:200 — UNREACHABLE**), `newStorageAppendMsg` (**:223 — UNREACHABLE**) and `newStorageApplyMsg` (**:372 — UNREACHABLE**) never run and **`MsgStorageAppend`(19)/`MsgStorageApply`(21) never exist**. The *response* messages are a different story: `acceptReady:419-426` builds `MsgStorageAppendResp`(20) and `MsgStorageApplyResp`(22) **unconditionally in the sync path** and `Advance:485` steps them locally. They never touch `r.msgs`, never reach `Ready.Messages`, and never enter the harness net.

### 2.2 `raft/raft.go` — 33 reachable

| Fn | file:line | Role | Reached by / with |
|---|---|---|---|
| `lockedRand.Intn` | raft.go:105 | **D-11 jitter choice site** (map-range draw) | `resetRandomizedElectionTimeout` ← `reset` ← every become*. **Live but unobserved**: `pastElectionTimeout` is never called, so the drawn value cannot affect the trace. |
| `Config.validate` | raft.go:312 | config check + defaults (`MaxUncommittedEntriesSize`→noLimit, `MaxCommittedSizePerReady`→1MB, `MaxInflightBytes`→noLimit) | `newRaft:459` |
| `newRaft` | raft.go:458 | build `raft`; `confchange.Restore`, `switchToConfig`, `assertConfStatesEquivalent`, `becomeFollower(0,None)`; `fmt.Sprintf("%x")` at :510 | H(E4) |
| `softState` | raft.go:521 | `{lead,state}` | `HasReady:451`, `readyWithoutAccept:147`, `NewRawNode:57` |
| `hardState` | raft.go:523 | `{Term,Vote,Commit}` | `HasReady:454`, `readyWithoutAccept:152,161`, `NewRawNode:59` |
| `send` | raft.go:533 | term stamping + **the msgs / msgsAfterAppend split (:565-619)**; panics on self-addressed non-resp (:615) | all emitters |
| `sendAppend` | raft.go:624 | `maybeSendAppend(to,true)` | `bcastAppend:738`, `stepLeader:1535` (reject), `stepLeader:1579` (CanBumpCommit) |
| `maybeSendAppend` | raft.go:637 | build **MsgApp**; `IsPaused` gate, `raftLog.term(prev)`, `raftLog.entries`, `SentEntries`/`SentCommit` | as above + `stepLeader:1588` (`sendIfEmpty=false` loop) |
| `bcastAppend` | raft.go:733 | fan-out over `trk.Visit` | `becomeLeader`'s caller `stepCandidate:1724`, `stepLeader:1371` (MsgProp), `stepLeader:1573` (post-commit) |
| `raft.appliedTo` | raft.go:756 | bump applied; AutoLeave check (**false forever** → `confChangeToMsg` at :767 unreachable) | `Step:1227` (MsgStorageApplyResp) |
| `maybeCommit` | raft.go:794 | `raftLog.maybeCommit(entryID{r.Term, trk.Committed()})` | `stepLeader:1569`, `switchToConfig:2033` |
| `reset` | raft.go:800 | term/vote/lead reset, `ResetVotes`, rebuild every `Progress`, new `readOnly` | `becomeFollower/Candidate/Leader` |
| `appendEntry` | raft.go:831 | clone+stamp entries, `increaseUncommittedSize`, `raftLog.append`, **self-MsgAppResp (:864)** | `becomeLeader:981` (the noop entry), `stepLeader:1368` (client proposal) |
| `becomeFollower` | raft.go:910 | → `stepFollower` | `newRaft:506`; `Step:1146` (**MsgApp at higher term → lead=From**, see §2.7-R2); `Step:1148` (**MsgVote at higher term → lead=None**) |
| `becomeCandidate` | raft.go:921 | Term+1, self-vote | `campaign:1058` |
| `becomeLeader` | raft.go:952 | `step=stepLeader`, `reset(Term)`, self `BecomeReplicate`, `pendingConfIndex=lastIndex`, **`appendEntry(emptyEnt)` at :981** | `stepCandidate:1723` |
| `hup` | raft.go:992 | leader/promotable/unapplied-cc guards, then `campaign` | `Step:1213` (MsgHup) |
| `hasUnappliedConfChanges` | raft.go:1014 | **returns at :1016** (`applied==committed==1` at the single hup) → `raftLog.scan` and `errBreak` never run | `hup:1002` |
| `campaign` | raft.go:1044 | `becomeCandidate`; sorted `Voters.IDs()`; **self-MsgVoteResp (:1078)** + **MsgVote to 2,3 (:1090)** | `hup:1008` |
| `poll` | raft.go:1094 | `RecordVote` + `TallyVotes` | `stepCandidate:1716` (MsgVoteResp). *Sub-branch:* the `else` at :1097 (rejection log) is unreachable — see §2.7-R3. |
| **`raft.Step`** | raft.go:1108 | term prelude + type switch | everything |
| **`stepLeader`** | raft.go:1294 | leader handler | MsgProp(local), MsgAppResp(wire+local), MsgVoteResp(late, no-op) |
| `stepCandidate` | raft.go:1692 | candidate handler | MsgVoteResp (self-directed and wire) |
| `stepFollower` | raft.go:1737 | follower handler | MsgApp |
| `logSliceFromMsgApp` | raft.go:1801 | MsgApp → `logSlice` | `handleAppendEntries:1813` |
| `handleAppendEntries` | raft.go:1810 | follower append; **all three exits reachable** (§2.7-R1) | MsgApp |
| `promotable` | raft.go:1965 | `Progress[self]` + no pending snapshot | `hup:998`, `campaign:1045` |
| `switchToConfig` | raft.go:1998 | install cfg/progress, `ConfState()`; here always with `r.state==StateFollower` → **returns at :2029** | `newRaft:498` |
| `resetRandomizedElectionTimeout` | raft.go:2072 | jitter draw | `reset:809` |
| `abortLeaderTransfer` | raft.go:2080 | `leadTransferee=None` | `reset:811` |
| `increaseUncommittedSize` | raft.go:2117 | size accounting (never refuses) | `appendEntry:841` |
| `reduceUncommittedSize` | raft.go:2135 | size accounting | `Step:1228` |
| `releasePendingReadIndexMessages` | raft.go:2146 | **fast-path return at :2150** (list always empty) → `committedEntryInCurrentTerm` / `sendMsgReadIndexResponse` never run | `stepLeader:1572` |

#### 2.2.1 `raft.Step`'s term prelude — branch by branch

* **`m.Term == 0` (raft.go:1117, "local message")** — REACHABLE: `MsgHup` (rawnode.go:85), `MsgProp` (rawnode.go:92), and **`MsgStorageApplyResp`** (`Term` set to 0 at rawnode.go:392).
* **`m.Term > r.Term` (raft.go:1119)** — REACHABLE, entered by nodes 2/3 at Term 0 receiving Term-1 traffic. Inside:
  * `:1120` `MsgVote||MsgPreVote` → REACHABLE for MsgVote; `force := bytes.Equal(m.GetContext(), campaignTransfer)` is **evaluated** (always false: `campaign` only attaches Context for `campaignTransfer`, `raft.go:1087-1089`); `inLease` false because `checkQuorum` false → the early `return nil` at :1130 is **UNREACHABLE**.
  * inner switch `:1134` MsgPreVote — UNREACHABLE (PreVote off). `:1136` MsgPreVoteResp — UNREACHABLE.
  * `:1142` default → `:1145` **both arms reachable**: `becomeFollower(m.Term, m.From)` when the first Term-1 message a node sees is a **MsgApp** (possible: the leader can win on {1,2} while node 3's MsgVote is still in the multiset — this is exactly the reordering latitude the driver quantifies over); `becomeFollower(m.Term, None)` on **MsgVote**.
* **`m.Term < r.Term` (raft.go:1152-1205)** — **ENTIRE BLOCK UNREACHABLE.** Proof: every message that can be in the net carries `Term = r.Term` of its sender at send time (`send:562`), and the only terms ever occupied in T1 are 0 (initial) and 1 (after the single campaign) — no node ever advances past 1 because no second campaign, no tick, and no MsgTimeoutNow exist. A message with `Term==0` on the wire would have to be MsgProp/MsgReadIndex (`send:561`), and MsgProp never reaches the wire (§3). Local `MsgStorageAppendResp` carries `r.Term` and is stepped in the same `Advance` (no interleaved term change); local `MsgStorageApplyResp` carries 0 and is caught by the **first** case. Consequently dead: the "force step-down" `MsgAppResp` send at **:1175**, the low-term `MsgPreVoteResp` reject at **:1184**, and the low-term `MsgStorageAppendResp`/`appliedSnap` handling at **:1185-1199**.
* Type switch: `MsgHup:1209` ✓ (once), `MsgStorageAppendResp:1216` ✓ (→ `raftLog.stableTo`; the `m.GetSnapshot()` arm at :1220 dead), `MsgStorageApplyResp:1224` ✓, `MsgVote/MsgPreVote:1231` ✓ (**both arms**: grant at :1271 and **reject at :1280** — see §2.7-R3), `default → r.step:1284` ✓.

#### 2.2.2 `stepLeader` — which arms are live

* `MsgBeat:1297` ✗ (no ticks) · `MsgCheckQuorum:1300` ✗ · `MsgReadIndex:1373` ✗ · `MsgForgetLeader:1392` ✗.
* **`MsgProp:1313`** ✓ — `len(entries)==0` panic ✗; `Progress[self]==nil` ✗; `leadTransferee` ✗; the per-entry loop at :1328-1366 **runs** and evaluates `e.GetType()` (:1331), but `cc` is always nil (harness data entries are `EntryNormal`), so the whole conf-change validation block :1344-1365 is ✗; `appendEntry` ✓; `bcastAppend` ✓.
* `pr := r.trk.Progress[m.From]` (:1397) ✓ — the `pr == nil` arm ✗ (all senders are voters).
* **`MsgAppResp:1403`** ✓ — the driver's core loop.
  * **reject arm (:1409-1536) REACHABLE.** It requires two MsgApps in flight to the same follower delivered out of order, which the map-pick admits once that follower is in `StateReplicate`: leader emits `MsgApp(prev=k,[e_{k+1}])` on a proposal, then, after the *other* follower's ack advances commit, `bcastAppend` emits `MsgApp(prev=k+1,∅,commit=k+1)` to the same follower; picking the second first makes `raftLog.maybeAppend` fail `matchTerm`. Live inside: `raftLog.findConflictByTerm` (follower **and** leader, :1528), `Progress.MaybeDecrTo`, `Progress.BecomeProbe`, `sendAppend`. The `m.GetLogTerm() > 0` guard at :1433 is **true** in T1 (the follower's hint term is always 1).
  * **accept arm (:1537-1596)** ✓: `Progress.MaybeUpdate` → `StateProbe→BecomeReplicate` (:1549) ✓; `StateSnapshot` arm (:1550-1564) ✗; `Inflights.FreeLE` (:1566) ✓; **`maybeCommit` → `releasePendingReadIndexMessages` → `bcastAppend`** (:1569-1573) ✓; **`CanBumpCommit` → `sendAppend`** (:1574-1580) ✓ (fires on the lagging follower's ack after commit already advanced); the `for maybeSendAppend(from,false)` loop (:1588) ✓ (evaluates, returns false); leadTransferee arm (:1592-1595) ✗.
* `MsgHeartbeatResp:1598` ✗ · `MsgSnapStatus:1630` ✗ · `MsgUnreachable:1648` ✗ · `MsgTransferLeader:1655` ✗.

#### 2.2.3 `stepCandidate` / `stepFollower`

* `stepCandidate` (raft.go:1692): only **`myVoteRespType` = MsgVoteResp (:1715)** is live → `poll` → `quorum.VoteWon` → `becomeLeader` + `bcastAppend` (:1723-1724). `VotePending` falls through. `MsgProp:1703` ✗ (the driver proposes only at quiescence, and quiescence after the single campaign implies node 1 is already leader — this is also why the harness's `" dropped"`/`" steperr"` traces never appear). `MsgApp/MsgHeartbeat/MsgSnap` (:1706-1714) ✗ (no competing leader). `VoteLost` (:1726) ✗. `MsgTimeoutNow` ✗. The pre-candidate arm (:1720-1721) ✗.
* `stepFollower` (raft.go:1737): only **`MsgApp:1749`** is live (`electionElapsed=0`, `lead=m.From`, `handleAppendEntries`). `MsgProp:1739` ✗ (node 1 never becomes a follower; nodes 2/3 are never asked to propose) → **the proposal-forwarding `send(m)` at :1748 never runs**, which is why MsgProp never reaches the wire. `MsgHeartbeat/MsgSnap/MsgTransferLeader/MsgForgetLeader/MsgTimeoutNow/MsgReadIndex/MsgReadIndexResp` ✗.

### 2.3 `raft/log.go` (29) and `raft/log_unstable.go` (11)

`log.go`: `newLogWithSize:75` (H via newRaft) · `maybeAppend:109` (MsgApp) · `append:133` (MsgApp, appendEntry) · `findConflict:154` (MsgApp; its `Infof` argument at :161 forces `zeroTermOnOutOfBounds`) · `findConflictByTerm:182` (MsgApp reject on the follower, MsgAppResp reject on the leader) · `nextUnstableEnts:198` / `hasNextUnstableEnts:204` / `hasNextOrInProgressUnstableEnts:211` · `nextCommittedEnts:220` / `hasNextCommittedEnts:248` / `maxAppliableIndex:267` · `hasNextUnstableSnapshot:283` (always false, but **executed** at `HasReady:457`/`readyWithoutAccept:155`) · `hasNextOrInProgressSnapshot:289` (`promotable`, `nextCommittedEnts:225`) · `firstIndex:300` · `lastIndex:311` · `commitTo:322` (MsgApp; `maybeCommit`) · `appliedTo:332` (MsgStorageApplyResp) · `acceptApplying:347` (`acceptReady:434`) · `stableTo:367` (MsgStorageAppendResp) · `acceptUnstable:375` (`acceptReady:430`) · `lastEntryID:378` · `term:387` · `entries:415` (`maybeSendAppend`) · `isUpToDate:442` (MsgVote) · `matchTerm:447` · `maybeCommit:455` · `slice:499` · `mustCheckOutOfBounds:551` · `zeroTermOnOutOfBounds:567`.

**Unreachable in log.go:** `newLog:69` (no callers anywhere in the tree), `String:102` (formatting only — the harness logger never formats), `nextUnstableSnapshot:277` (guarded by a false `hasNextUnstableSnapshot` at rawnode.go:155), `snapshot:293` (only `maybeSendSnapshot`), `restore:466`, `scan:482`, `allEntries:423` (no caller but itself).

`log_unstable.go`: `maybeFirstIndex:58` · `maybeLastIndex:67` · `maybeTerm:79` · `nextEntries:100` · `nextSnapshot:110` (called, returns nil) · `acceptInProgress:122` · `stableTo:138` · `shrinkEntriesArray:170` · `truncateAndAppend:191` (**only the `fromIndex == offset+len` arm at :194**; the `fromIndex <= offset` replace arm :197 and the truncate arm :204 need a divergent log, impossible with a single term-1 leader) · `slice:223` · `mustCheckOutOfBounds:232`.
**Unreachable:** `stableSnapTo:176`, `restore:183`.

### 2.4 The snapshot family — PRUNED, with the argument

`maybeSendSnapshot` (`raft.go:685`), `MsgSnap` emission (:708), `handleSnapshot` (:1859), `raft.restore` (:1879), `raftLog.restore`, `unstable.restore`, `unstable.stableSnapTo`, `raftLog.stableSnapTo`, `raft.appliedSnap` (:785), `raftLog.snapshot`, `MemoryStorage.Snapshot`, and the harness's own "unexpected snapshot" halt (twin-lib.go:258-264) are all **unreachable**. Reasons, chained:

1. `maybeSendSnapshot` is called only from `maybeSendAppend:648` (when `raftLog.term(pr.Next-1)` errors) and `:666` (when `raftLog.entries` errors).
2. Storage is never compacted (no `Compact`/`CreateSnapshot` call in twin-lib.go), so `firstIndex()` is fixed at **2** and the term of index 1 is always retrievable from the bootstrap dummy entry (`storage.go:235`, `storage.go:169-181`).
3. `pr.Next ≥ 2` always: `reset:817` sets `Next = lastIndex+1 ≥ 2`; `MaybeUpdate` only raises it; `MaybeDecrTo` floors it at `Match+1` and, in the probe arm, at `min(rejected, matchHint+1)` where **`matchHint ≥ 1`** — the leader's `findConflictByTerm` cannot return 0 because every term in T1 is 1 and `term(1)=1 ≤ hintTerm`. Hence `prevIndex = Next-1 ≥ 1` → `term()` never returns `ErrCompacted`, and `entries(lo≥2)` never trips `mustCheckOutOfBounds`'s `lo < firstIndex`.
4. `MsgSnap` therefore never exists → `handleSnapshot`/`restore` unreachable; `unstable.snapshot` stays nil → `hasNextUnstableSnapshot` is constant-false and `Ready.Snapshot` is always empty.

### 2.5 Config-change paths — PRUNED, with the argument

The harness `apply` (twin-lib.go:298-335) never calls `ApplyConfChange`; it *flags* a non-`EntryNormal` entry as an S3 anomaly (twin-lib.go:313-317). Nothing in T1 can produce such an entry: `RawNode.ProposeConfChange` is never called, `confChangeToMsg` (`node_decls.go:114`) has exactly two callers — `ProposeConfChange` (dead) and `raft.appliedTo:767`, guarded by `r.trk.Config.AutoLeave`, which is false because the only configuration ever installed comes from `confchange.Restore` on a non-joint `ConfState` (`restore.go:124-131` → `Simple`, never `EnterJoint`). Therefore **unreachable:** `raft.applyConfChange:1970`, `Changer.EnterJoint:51`, `Changer.LeaveJoint:94`, `Changer.makeLearner:204`, `Changer.remove:231`, `nilAwareAdd:364`, `nilAwareDelete:372`, `outgoingPtr:406`, `Describe:410`, `raftpb.MarshalConfChange`, all `ConfChangeI` methods, `traceChangeConfEvent`, `hasUnappliedConfChanges`'s scan body, and `stepLeader:1331-1365`'s validation block.

**Reachable confchange (14 named + 1 closure), all from `newRaft:491` only:** `Restore:119`, `toConfChangeSingle:26`, the per-`cc` closure `restore.go:128`, `chain:99`, `Changer.Simple:128`, `checkAndCopy:337`, `checkAndReturn:351`, `checkInvariants:276`, `Changer.apply:150`, `makeVoter:178` (always via the `pr == nil` early return at :181), `initProgress:247`, `symdiff:384`, `joint:400`, `incoming:404`, `outgoing:405`.

### 2.6 `tracker` (25) and `quorum` (6)

**tracker/tracker.go:** `MakeProgressTracker:129` · `ConfState:148` (from `switchToConfig:2005`) · `matchAckIndexer.AckedIndex:169` · `Committed:179` · `Visit:184` (`reset:814`, `bcastAppend:734`) · `VoterNodes:221` (`newRaft:509`) · `ResetVotes:245` · `RecordVote:251` · `TallyVotes:260` · `Config.Clone:96` (`checkAndCopy:338`).
**tracker/progress.go:** `ResetState:121` · `BecomeProbe:130` · `BecomeReplicate:146` · `SentEntries:165` (both `StateReplicate` and `StateProbe` arms live; the `default` panic ✗) · `CanBumpCommit:189` · `SentCommit:198` · `MaybeUpdate:205` · `MaybeDecrTo:226` (both arms live) · `IsPaused:262` (`StateProbe`/`StateReplicate` arms; `StateSnapshot` ✗).
**tracker/inflights.go:** `NewInflights:46` · `Add:65` · `grow:85` (first `Add`) · `FreeLE:98` · `Full:131` · `reset:139`.
**Unreachable tracker:** `Config.String:80`, `IsSingleton:160`, `QuorumActive:208`, `LearnerNodes:232`, `Progress.BecomeSnapshot:153`, `Progress.String:275`, `ProgressMap.String:303`, `StateType.String:42`, `Inflights.Clone:55`, `Inflights.Count:136`.
**quorum:** `MajorityConfig.Slice:109` (via `ConfState()`), `MajorityConfig.CommittedIndex:120`, `MajorityConfig.VoteResult:169`, `JointConfig.IDs:30`, `JointConfig.CommittedIndex:49`, `JointConfig.VoteResult:61`. **Unreachable:** `MajorityConfig.String:28`, `Describe:48`, `JointConfig.String:21`, `JointConfig.Describe:42`, `Index.String:25`, `mapAckIndexer.AckedIndex:40`, `VoteResult.String` (`voteresult_string.go`).

### 2.7 Three reachability results worth recording (all driven by the map-pick, i.e. genuinely in T1's ∀-scope)

* **R1 — all three exits of `handleAppendEntries` are live.** Accept (`raft.go:1820`); **reject** (`raft.go:1844`) when a later-`prev` MsgApp is picked before an earlier one; **commit-catch-up** (`raft.go:1816`, `a.prev.index < committed`) when a stale MsgApp is delivered after the follower has already committed past it via the leader's post-reject resend.
* **R2 — `becomeFollower(term, m.From)` at `raft.go:1146` is live**: a node whose MsgVote is still sitting in the multiset can be the target of the new leader's first MsgApp.
* **R3 — the vote-rejection send at `raft.go:1280` is live**, and only in the direction "follower already knows the leader": node 3 learns `lead=1` from that MsgApp, then the delayed MsgVote arrives at equal term, `canVote` is false (`Vote==None` but `lead!=None`, `raft.go:1235`), so a `Reject:true` MsgVoteResp is emitted. Conversely, **`poll(..., v=false)` is unreachable** — a rejection can only be produced *after* node 1 is already leader, so it lands in `stepLeader` (no case → no-op), never in `stepCandidate`. Hence `raft.go:1097`'s else-log and `quorum.VoteLost` are dead.

### 2.8 The whole dead-by-formatting class

Because `harnessLogger`'s bodies are empty (twin-lib.go:109-116), **no `fmt` verb ever runs**, so every `String()`/`Describe*()` in the tree is unreachable even where it is passed as a logging argument: `raft/util.go:83,93,97,104,109,152,156,193,208,247,262`, `raft/raft.go:140`, `raft/log.go:102`, `tracker/*.String`, `quorum/*.String`. (Contrast: argument *expressions* do run — §1, `zeroTermOnOutOfBounds`.) Also dead: `raft/status.go` in full, `raft/bootstrap.go` in full, `raft/read_only.go:60,65,72,79,93`, `raft/logger.go` except `SetLogger`, `raft/types.go:78,84,93`, `raft/node_decls.go:114`, `raft/raft.go:519,713,743,747,785,869,881,936,1859,1879,1970,2056,2068,2076,2085,2093,2165`.

---

## 3. MESSAGE-TYPE POPULATION

### 3.1 The closed set that can ever be in `t.net` (twin-lib.go:283-286)

| Type (`pb` value) | Emitting site | Route into the net |
|---|---|---|
| **`MsgVote`** (5) | `campaign`, **raft.go:1090** | `send:617` → `r.msgs` → `Ready.Messages` (`rawnode.go:146`) |
| **`MsgVoteResp`** (6) | grant **raft.go:1271**, reject **raft.go:1280** | `send:611` → `msgsAfterAppend` → `readyWithoutAccept:179-183` (only because `To != r.id`) |
| **`MsgApp`** (3) | `maybeSendAppend`, **raft.go:670** | `send:617` → `r.msgs` |
| **`MsgAppResp`** (4) | `handleAppendEntries` **:1816 / :1820 / :1844** | `send:611` → `msgsAfterAppend` → `readyWithoutAccept:179-183` |

That is the entire wire alphabet: **{3,4,5,6}** — matching the driver's `"type"+itoa(int(m.GetType()))` trace field (twin-chdriver.go:66).

### 3.2 Local / self-directed messages that bypass the net

| Type | Created at | Why it never hits the net |
|---|---|---|
| `MsgHup` (0) | `rawnode.go:84-86` | handed straight to `rn.raft.Step`; never passed to `send` |
| `MsgProp` (2) | `rawnode.go:91-95` | handed straight to `raft.Step`; the only forwarding site, `stepFollower:1747-1748`, is unreachable (node 1 is never a follower, nodes 2/3 are never proposed to) |
| `MsgVoteResp` to self | `campaign:1078` | `send:611` → `msgsAfterAppend`; **filtered out of `Ready.Messages` by `rawnode.go:180` (`m.GetTo() != r.id`)** and instead pushed onto `stepsOnAdvance` (`rawnode.go:414-418`), replayed by `Advance:485` |
| `MsgAppResp` to self | `appendEntry:864` | same route (this is the leader's self-ack that drives `MaybeUpdate`/`maybeCommit`) |
| `MsgStorageAppendResp` (20) | `newStorageAppendRespMsg:266` via `acceptReady:419-421` | To = self, From = `LocalAppendThread`; `stepsOnAdvance` → `Advance` → `Step:1216` → `raftLog.stableTo` |
| `MsgStorageApplyResp` (22) | `newStorageApplyRespMsg:387` via `acceptReady:423-425` | To = self, From = `LocalApplyThread`, `Term=0`; `stepsOnAdvance` → `Advance` → `Step:1224` → `appliedTo` + `reduceUncommittedSize` |

Note the belt-and-braces: even if a local message *were* injected into the net, `RawNode.Step`'s guard (`rawnode.go:118-120`, `IsLocalMsg && !IsLocalMsgTarget(From)`) would return `ErrStepLocalMsg` rather than step it.

### 3.3 Types PROVEN ABSENT (both from the net and from the machine entirely)

| Type | Only producer | Reason absent |
|---|---|---|
| `MsgBeat` (1) | `tickHeartbeat:904` | `RawNode.Tick` (rawnode.go:64) is never called — the driver emits no `opTick` (twin-chdriver.go has no `opTick` op). `r.tick` is assigned (`raft.go:913,928,959`) and never invoked. |
| **`MsgHeartbeat`** (8) | `sendHeartbeat:722` ← `bcastHeartbeatWithCtx:752` ← `bcastHeartbeat:744` | `bcastHeartbeat` has exactly two callers: `stepLeader:1298` (needs MsgBeat → needs a tick) and `sendMsgReadIndexResponse:2175` (needs MsgReadIndex → needs `RawNode.ReadIndex`, never called). **Absent.** |
| `MsgHeartbeatResp` (9) | `handleHeartbeat:1856` | requires receiving a MsgHeartbeat. |
| `MsgSnap` (7) | `maybeSendSnapshot:708` | §2.4 (no compaction ⇒ `term(prev)`/`entries(lo)` never error; `Next ≥ 2` always). |
| `MsgUnreachable` (10) | `RawNode.ReportUnreachable:530` | harness never calls it. |
| `MsgSnapStatus` (11) | `RawNode.ReportSnapshot:537` | harness never calls it. |
| `MsgCheckQuorum` (12) | `tickHeartbeat:888` | no ticks **and** `Config.CheckQuorum` false. |
| **`MsgTransferLeader`** (13) | `RawNode.TransferLeader:542`; forwarded at `stepFollower:1767` | harness never calls it; forwarding needs one to exist. |
| **`MsgTimeoutNow`** (14) | `sendTimeoutNow:2077` ← `stepLeader:1594` / `stepLeader:1681` | both call sites are gated on `r.leadTransferee != None`, which is only set at `stepLeader:1679` on a MsgTransferLeader. **Absent.** |
| `MsgReadIndex` (15) / `MsgReadIndexResp` (16) | `RawNode.ReadIndex:556` / `responseToReadIndexReq:2102` | harness never calls `ReadIndex`. |
| `MsgPreVote` (17) / `MsgPreVoteResp` (18) | `campaign:1090` under `t == campaignPreElection` | `Config.PreVote` false → `Step:1210` takes the else → `hup(campaignElection)` → `campaign` takes the else at `raft.go:1057`. |
| **`MsgStorageAppend`** (19) / `MsgStorageApply` (21) | `newStorageAppendMsg:223` / `newStorageApplyMsg:372` | reachable only under `if rn.asyncStorageWrites` (`rawnode.go:163`), which is false (§0). |
| `MsgForgetLeader` (23) | `RawNode.ForgetLeader:548` | harness never calls it. |
| `MsgHup` **on the wire** | — | never passed to `send`; and `IsLocalMsg(MsgHup)` (`util.go:32`) would make `RawNode.Step` reject it. |
| `MsgProp` **on the wire** | `stepFollower:1748` | unreachable — the only follower-side proposal forwarder, and no proposal is ever stepped at a follower (§2.2.3). *(Note: this type IS on the wire in the schedule battery's `follower-propose`/`perturb-mix` schedules, twin-lib.go:629/680 — it is absent specifically because T1's client is node-1-only.)* |

---

## 4. COUNTS, COSTING FLAGS, UNDECIDED

### 4.1 Distinct reachable function count (the Wave 3.1 unit driver)

| Bucket | Count |
|---|---|
| `raft` — rawnode.go | 16 |
| `raft` — raft.go | 33 |
| `raft` — log.go | 29 |
| `raft` — log_unstable.go | 11 |
| `raft` — util.go | 10 |
| `raft` — storage.go | 11 |
| `raft` — node_decls.go | 4 |
| `raft` — types.go / read_only.go / logger.go | 1 / 1 / 1 |
| `raft` — state_trace_nop.go (no-op hooks actually invoked) | 10 |
| **`raft` subtotal** | **127** |
| `tracker` | 25 |
| `quorum` | 6 |
| `confchange` | 14 named + 1 anonymous closure (`restore.go:128`) |
| **CORE TOTAL (raft+tracker+quorum+confchange)** | **172 named (173 units incl. the closure)** |
| `raftpb` accessors invoked (`Message` ×12, `Entry` ×4, `SnapshotMetadata` ×3, `Snapshot.GetMetadata`, `HardState` ×3, `ConfState.GetAutoLeave`) | 24 |
| `raftpb`/`proto` machinery (`proto.Clone`, `proto.Size`, `Entry.CloneMessage`, `Entry.SizeMessage`, `plainpbSizeVarint`, `Snapshot.CloneMessage`, `SnapshotMetadata.CloneMessage`, `ConfState.CloneMessage`, `ConfState.EqualMessage`, `ConfState.Equivalent`, `EnsureConfState`, `EnsureSnapshotMetadata`, `EnsureSnapshot`, `MessageType.Enum`) | 14 |
| **GRAND TOTAL** | **211** |

Denominator for context: 9 749 lines across the five packages; the raft package alone declares 205 functions, of which 127 are live.

### 4.2 Functions >100 lines (costing flags)

| Fn | file:line span | Total / non-comment lines | Note |
|---|---|---|---|
| **`stepLeader`** | raft.go:1294-1688 | **395 / 201** | by far the largest unit; ~half its bulk is the two long rejection-probing comment blocks. Live arms: MsgProp, MsgAppResp (both reject and accept). Natural split point: the `MsgAppResp` case is 194 of the 395 lines. |
| **`raft.Step`** | raft.go:1108-1290 | **183 / 99** | term prelude + type switch; the `m.Term < r.Term` block (54 lines) is entirely dead in T1 and is the obvious first excision. |

Near-threshold, flagged for the same reason: `newStorageAppendRespMsg` **98 lines / 17 code** (rawnode.go:266-363 — 81 lines of ABA-problem commentary), `raft.send` **88 / 27** (raft.go:533-620), `raft.restore` 83 (unreachable), `toConfChangeSingle` 72 (reachable), `stepFollower` 62 / ~30, `checkInvariants` 57.

### 4.3 UNDECIDED — reachability genuinely depends on runtime values

Reported, never silently pruned.

* **U1 — `raftLog.slice`'s mixed storage+unstable slow path, `log.go:529-547`, and with it `extend` (`util.go:334`) and `entsSize`'s use at `log.go:534,542`.** Entering it needs a single read range with `lo < unstable.offset < hi`, i.e. a follower ≥2 entries behind while the leader still holds an unstable tail. The argument for *unreachable*: the driver proposes only at quiescence (twin-chdriver.go:57-79), and quiescence implies every follower's `Match == lastIndex` (every MsgApp yields a resp, and `stepLeader:1588`'s `for maybeSendAppend(from,false)` drains the gap), so at most one entry is ever un-acked; and each harvest's `Advance` stabilizes the tail before the next send. That chain rests on runtime state (`Match`, `unstable.offset`) not settled statically. **Treat U1's three units as reachable-unless-proved for costing.**
* **U2 — the second disjunct at `stepLeader:1546`, `pr.Match == m.GetIndex() && pr.State == tracker.StateProbe`.** Requires a duplicate-index MsgAppResp arriving while the progress has been knocked back to `StateProbe` by an interleaved rejection. Constructible in principle from the reject scenario of §2.7-R1 plus a second in-flight resp; no concrete stream exhibited, and the net never duplicates. Undecided.
* **U3 — assertion branches whose reachability *is* a safety violation.** `log.go:120-121` (`ci <= l.committed` panic), `log.go:137-138`, `log.go:325-327` (`commitTo` out of range), `log.go:333-334` (`appliedTo` out of range), `log.go:348-349`, `raft.go:615` (self-addressed send), `raft.go:551/555` (term-stamping panics), `unstable.mustCheckOutOfBounds:233-238`, `util.go:325` (`assertConfStatesEquivalent` → `Logger.Panic` → twin-lib.go:119 panic). Pruned as *unreachable on a correct subject* — which is precisely what T1 asserts, so they must not be counted as proof obligations discharged by reachability: **they are obligations the specs prove unreachable.**
* **U4 — `lockedRand.Intn` (`raft.go:105`) is reachable but its *value* is unobservable.** It runs on every `reset` (`raft.go:809/2073`), yet `pastElectionTimeout` (`raft.go:2068`) — the only consumer of `randomizedElectionTimeout` — is unreachable without ticks. The D-11 choice site is therefore *live code, dead nondeterminism* in T1: the only surviving choice site is the driver's own `mapIter` pick (twin-chdriver.go:60-63). Worth recording explicitly, because a naive "choice sites in the reachable closure" count would double-count it.
* **U5 — the exact iteration-order dependence of `Progress.BecomeProbe`/`MaybeDecrTo`/`findConflictByTerm` (§2.7-R1).** These are reachable only for *some* choice streams. Under T1's ∀-quantification they belong in the closure (the statement ranges over all streams), but they will not appear in every trace; any per-run coverage instrument will show them flapping. Recorded as reachability-under-∀, not reachability-per-run.
