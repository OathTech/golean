import GoLeanProofs.Sym.Mirror

/-! GENERATED (A4-U25; `artifacts/probe/RoundVrGen.lean` — DO NOT
EDIT BY HAND). The MsgVoteResp ELECTION-COMPLETION FULL-ROUND
literals (anchor 2 to anchor 3: the CANDIDATE handles the
quorum-completing VoteResp — becomeLeader + the noop append +
bcastAppend), boundary schedule AUTO-DISCOVERED from the mirror's
own quit sites (the U23 template).
The window LINK theorems in `RoundVrEq*.lean` re-check every
literal against the mirror. -/

namespace GoLean.RaftSeam.RoundVr

open GoLean GoLean.GoCore GoLean.Sym

set_option maxRecDepth 8000000

def vrSB5 : SymState :=
  (GoLean.Sym.State.mk
  [((GoLean.Loc.base { id := 15 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 57 })))),
  ((GoLean.Loc.base { id := 18 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.lockedRand" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 67 })))),
  ((GoLean.Loc.base { id := 27 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))]))),
  ((GoLean.Loc.base { id := 28 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))]))),
  ((GoLean.Loc.base { id := 57 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Commit"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 67 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.lockedRand" })) (GoLean.Sym.Value.struct ({ key := "raft.lockedRand" }) #[(("mu"), (GoLean.Sym.Value.syncData (GoLean.SyncPrim.mutex false)))]))),
  ((GoLean.Loc.base { id := 110 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 115 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[]))),
  ((GoLean.Loc.base { id := 121 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twin" })) (GoLean.Sym.Value.struct ({ key := "main.twin" }) #[(("nodes"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 1764 }), offset := 0, len := 3, cap := 4 }))),
  (("net"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8195 }), offset := 0, len := 1, cap := 1 }))),
  (("live"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8196 }), offset := 0, len := 1, cap := 1 }))),
  (("leaderOf"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 115 }) }))),
  (("byIndex"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 118 }) }))),
  (("claims"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("violations"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("pending"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 136 }), offset := 0, len := 2, cap := 4 }))),
  (("driven"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("seq"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.int))),
  (("trace"), (GoLean.Sym.Value.string ({ bytes := #[91, 99, 104, 111, 105, 99, 101, 45, 100, 114, 105, 118, 101, 110, 93, 10, 99, 97, 109, 112, 97, 105, 103,
             110, 49, 114, 49, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 53, 45, 62, 50, 32, 32, 124, 67,
             49, 47, 49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 70, 48, 47, 48, 47, 48, 32, 110, 101, 116, 61, 50, 10,
             114, 50, 32, 112, 105, 99, 107, 35, 49, 32, 116, 121, 112, 101, 53, 45, 62, 51, 32, 32, 124, 67, 49, 47,
             49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 110, 101, 116, 61, 50, 10, 114, 51,
             32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 54, 45, 62, 49] }))),
  (("halt"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 170 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1742 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 179 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 167 }) })))]))),
  ((GoLean.Loc.base { id := 179 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.struct ({ key := "raft.MemoryStorage" }) #[(("Mutex"), (GoLean.Sym.Value.syncData (GoLean.SyncPrim.mutex false))),
  (("hardState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5675 }))),
  (("snapshot"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 258 }))),
  (("ents"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 300 }), offset := 0, len := 1, cap := 1 }))),
  (("callStats"), (GoLean.Sym.Value.struct ({ key := "raft.inMemStorageCallStats" }) #[(("initialState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("firstIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 4) (GoLean.GoCore.IntKind.int))),
  (("lastIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 15) (GoLean.GoCore.IntKind.int))),
  (("entries"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.int))),
  (("snapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))]))]))),
  ((GoLean.Loc.base { id := 286 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 295 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 298 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 286 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 295 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 300 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 298 }))]))),
  ((GoLean.Loc.base { id := 349 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })) (GoLean.Sym.Value.struct ({ key := "raft.raftLog" }) #[(("storage"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 179 })))),
  (("unstable"), (GoLean.Sym.Value.struct ({ key := "raft.unstable" }) #[(("snapshot"), (GoLean.Sym.Value.nil)),
  (("entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("offset"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("snapshotInProgress"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("offsetInProgress"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 }))))])),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applying"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("maxApplyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 389 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raft" })) (GoLean.Sym.Value.struct ({ key := "raft.raft" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Vote"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("readStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("raftLog"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 349 }))),
  (("maxMsgSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("maxUncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64))),
  (("trk"), (GoLean.Sym.Value.struct ({ key := "tracker.ProgressTracker" }) #[(("Config"), (GoLean.Sym.Value.struct ({ key := "tracker.Config" }) #[(("Voters"), (GoLean.Sym.Value.array #[(GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1086 }) })),
  (GoLean.Sym.Value.map ({ base := none }))])),
  (("AutoLeave"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Learners"), (GoLean.Sym.Value.map ({ base := none }))),
  (("LearnersNext"), (GoLean.Sym.Value.map ({ base := none })))])),
  (("Progress"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1103 }) }))),
  (("Votes"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 5058 }) }))),
  (("MaxInflight"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 256) (GoLean.GoCore.IntKind.int))),
  (("MaxInflightBytes"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64)))])),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("isLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("msgs"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("msgsAfterAppend"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("leadTransferee"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("pendingConfIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("disableConfChangeValidation"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("uncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("readOnly"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5198 }))),
  (("electionElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("heartbeatElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("checkQuorum"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("preVote"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("heartbeatTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("electionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("randomizedElectionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("disableProposalForwarding"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("stepDownOnRemoval"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("tick"), (GoLean.Sym.Value.funcVal ({ key := "raft.raft.tickElection" }) [(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 }))])),
  (("step"), (GoLean.Sym.Value.funcVal ({ key := "raft.stepCandidate" }) [])),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("pendingReadIndexMessages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("traceLogger"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 1086 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[])),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[])),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[]))]))),
  ((GoLean.Loc.base { id := 1103 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1107 }))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1110 }))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1212 })))]))),
  ((GoLean.Loc.base { id := 1107 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5102 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1110 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5156 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1212 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5189 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1742 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })) (GoLean.Sym.Value.struct ({ key := "raft.RawNode" }) #[(("raft"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 }))),
  (("asyncStorageWrites"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("prevSoftSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5661 }))),
  (("prevHardSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5675 }))),
  (("stepsOnAdvance"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 5758 }), offset := 0, len := 0, cap := 4 })))]))),
  ((GoLean.Loc.base { id := 1764 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 170 })),
  (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1770 })),
  (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3369 })),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 1770 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1767 }) })))]))),
  ((GoLean.Loc.base { id := 3369 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 4941 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3378 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 3366 }) })))]))),
  ((GoLean.Loc.base { id := 5058 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))))) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))]))),
  ((GoLean.Loc.base { id := 5198 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.readOnly" })) (GoLean.Sym.Value.struct ({ key := "raft.readOnly" }) #[(("option"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("acks"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 5195 }) }))),
  (("unconfirmedReads"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("confirmedReads"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 5661 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 5666 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5669 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5672 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5675 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5666 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5669 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5672 })))]))),
  ((GoLean.Loc.base { id := 5758 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 6070 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6072 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8191 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 6) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8192 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8193 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8194 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Message" }) #[(("Type"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8191 }))),
  (("To"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8192 }))),
  (("From"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8193 }))),
  (("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8197 }))),
  (("LogTerm"), (GoLean.Sym.Value.nil)),
  (("Index"), (GoLean.Sym.Value.nil)),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Commit"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("Reject"), (GoLean.Sym.Value.nil)),
  (("RejectHint"), (GoLean.Sym.Value.nil)),
  (("Context"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Responses"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 8195 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 }))]))),
  ((GoLean.Loc.base { id := 8196 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))]))),
  ((GoLean.Loc.base { id := 8197 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8198 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8199 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8200 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8198 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8199 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 8201 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8200 }))]))),
  ((GoLean.Loc.base { id := 8202 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8203 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8204 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 8205 }) })))),
  ((GoLean.Loc.base { id := 8205 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.int)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))]))),
  ((GoLean.Loc.base { id := 8206 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 8205 }) })))),
  ((GoLean.Loc.base { id := 8207 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8195 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 8208 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8209 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8210 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8211 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8212 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8213 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8214 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8215 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8216 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 2) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8217 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8218 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8219 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 2) (GoLean.Sym.SymInt.lit 1))))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8220 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8221 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8222 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8223 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8224 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8225 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8226 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8227 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8228 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8229 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8230 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8231 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8232 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8233 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8234 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8235 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8236 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int32)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8237 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8238 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8239 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8240 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8241 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8242 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8243 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8244 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8245 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8246 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8247 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8248 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 8249 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[114, 51, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 54, 45, 62, 49] })))),
  ((GoLean.Loc.base { id := 8250 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 8251 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8252 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8253 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8254 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8255 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8256 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 170 })))),
  ((GoLean.Loc.base { id := 8257 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8258 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1742 })))),
  ((GoLean.Loc.base { id := 8259 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8260 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8261 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8262 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8263 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8264 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8265 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8266 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8267 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8268 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8269 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 27 }), offset := 0, len := 23, cap := 23 })))),
  ((GoLean.Loc.base { id := 8270 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8271 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int32)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int32)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8272 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8273 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8274 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8275 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8276 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8277 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8278 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8279 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8280 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8281 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 28 }), offset := 0, len := 23, cap := 23 })))),
  ((GoLean.Loc.base { id := 8282 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8283 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int32)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int32)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8284 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8285 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8286 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8287 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8288 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8289 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8290 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8291 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8292 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8293 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8294 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8295 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8296 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8297 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8298 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8299 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8300 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8301 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 3)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8302 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8303 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8304 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8305 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8306 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8307 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8308 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8309 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8310 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8311 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8312 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8313 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8314 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8315 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8316 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 4)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8317 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8318 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8319 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8320 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8321 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8322 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8323 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8324 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8325 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8326 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8327 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 4)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8328 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8329 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8330 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8331 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8332 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8333 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8334 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8335 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8336 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8337 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8338 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8339 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8340 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8341 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8342 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8343 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8344 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8345 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8346 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8347 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8348 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8349 }), offset := 0, len := 4, cap := 4 })))),
  ((GoLean.Loc.base { id := 8349 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 8350 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  ((GoLean.Loc.base { id := 8351 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[37, 120, 32, 114, 101, 99, 101, 105, 118, 101, 100, 32, 37, 115, 32, 102, 114, 111, 109, 32, 37, 120, 32,
             97, 116, 32, 116, 101, 114, 109, 32, 37, 100] })))),
  ((GoLean.Loc.base { id := 8352 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8349 }), offset := 0, len := 4, cap := 4 })))),
  ((GoLean.Loc.base { id := 8353 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 389 }) { key := "raft.raft" } "trk")))),
  ((GoLean.Loc.base { id := 8354 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8355 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8356 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8357 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8358 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8359 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8360 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8361 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 389 }) { key := "raft.raft" } "trk")))),
  ((GoLean.Loc.base { id := 8362 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8363 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8364 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8365 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8366 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1107 }))))]
  8367)

def vrCB5 : SymConfig :=
  (GoLean.Sym.Config.exec (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.fieldGet
        (GoLean.GoCore.Expr.deref
          (GoLean.GoCore.Expr.var "pr")
          (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))
        { key := "tracker.Progress" }
        "IsLearner")
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.seqn
      #[GoLean.GoCore.Stmt.initialization { id := "v", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.initialization { id := "voted", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.mapLookup
          (GoLean.GoCore.Assignee.var "v")
          (GoLean.GoCore.Assignee.var "voted")
          (GoLean.GoCore.Expr.fieldGet
            (GoLean.GoCore.Expr.deref
              (GoLean.GoCore.Expr.var "p")
              (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
            { key := "tracker.ProgressTracker" }
            "Votes")
          (GoLean.GoCore.Expr.var "id")
          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
          (GoLean.GoCore.Ty.bool)],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "voted"))
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "v")
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "granted")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "granted")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "rejected")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "rejected")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])]) ([[("pr", GoLean.Loc.base { id := 8366 }), ("id", GoLean.Loc.base { id := 8365 })],
 [],
 [("$res2", GoLean.Loc.base { id := 8364 }),
  ("rejected", GoLean.Loc.base { id := 8363 }),
  ("granted", GoLean.Loc.base { id := 8362 }),
  ("p", GoLean.Loc.base { id := 8361 })]]) (GoLean.Sym.Cont.mapIterK (some "id") (some "pr") (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.fieldGet
        (GoLean.GoCore.Expr.deref
          (GoLean.GoCore.Expr.var "pr")
          (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))
        { key := "tracker.Progress" }
        "IsLearner")
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.seqn
      #[GoLean.GoCore.Stmt.initialization { id := "v", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.initialization { id := "voted", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.mapLookup
          (GoLean.GoCore.Assignee.var "v")
          (GoLean.GoCore.Assignee.var "voted")
          (GoLean.GoCore.Expr.fieldGet
            (GoLean.GoCore.Expr.deref
              (GoLean.GoCore.Expr.var "p")
              (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
            { key := "tracker.ProgressTracker" }
            "Votes")
          (GoLean.GoCore.Expr.var "id")
          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
          (GoLean.GoCore.Ty.bool)],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "voted"))
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "v")
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "granted")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "granted")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "rejected")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "rejected")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])]) (some (GoLean.Loc.base { id := 1103 })) #[(GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))] #[(GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)),
  (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)),
  (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64))] ([[],
 [("$res2", GoLean.Loc.base { id := 8364 }),
  ("rejected", GoLean.Loc.base { id := 8363 }),
  ("granted", GoLean.Loc.base { id := 8362 }),
  ("p", GoLean.Loc.base { id := 8361 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "result", typ := GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" } },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "result"]
       { key := "quorum.JointConfig.VoteResult" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.fieldGet
             (GoLean.GoCore.Expr.deref
               (GoLean.GoCore.Expr.var "p")
               (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
             { key := "tracker.ProgressTracker" }
             "Config")
           { key := "tracker.Config" }
           "Voters",
         GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref
             (GoLean.GoCore.Expr.var "p")
             (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
           { key := "tracker.ProgressTracker" }
           "Votes"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "granted") (GoLean.GoCore.Expr.var "granted"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "rejected") (GoLean.GoCore.Expr.var "rejected"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res2") (GoLean.GoCore.Expr.var "result"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[],
 [("$res2", GoLean.Loc.base { id := 8364 }),
  ("rejected", GoLean.Loc.base { id := 8363 }),
  ("granted", GoLean.Loc.base { id := 8362 }),
  ("p", GoLean.Loc.base { id := 8361 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1353"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1354"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1355"])]) ([[("$c1355", GoLean.Loc.base { id := 8360 }),
  ("$c1354", GoLean.Loc.base { id := 8359 }),
  ("$c1353", GoLean.Loc.base { id := 8358 })],
 [("result", GoLean.Loc.base { id := 8347 }),
  ("rejected", GoLean.Loc.base { id := 8346 }),
  ("granted", GoLean.Loc.base { id := 8345 }),
  ("v", GoLean.Loc.base { id := 8344 }),
  ("t", GoLean.Loc.base { id := 8343 }),
  ("id", GoLean.Loc.base { id := 8342 }),
  ("r", GoLean.Loc.base { id := 8341 })]]) ([GoLean.Loc.base { id := 8362 }, GoLean.Loc.base { id := 8363 }, GoLean.Loc.base { id := 8364 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "granted") (GoLean.GoCore.Expr.var "$c1353"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "rejected") (GoLean.GoCore.Expr.var "$c1354"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "result") (GoLean.GoCore.Expr.var "$c1355"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("$c1355", GoLean.Loc.base { id := 8360 }),
  ("$c1354", GoLean.Loc.base { id := 8359 }),
  ("$c1353", GoLean.Loc.base { id := 8358 })],
 [("result", GoLean.Loc.base { id := 8347 }),
  ("rejected", GoLean.Loc.base { id := 8346 }),
  ("granted", GoLean.Loc.base { id := 8345 }),
  ("v", GoLean.Loc.base { id := 8344 }),
  ("t", GoLean.Loc.base { id := 8343 }),
  ("id", GoLean.Loc.base { id := 8342 }),
  ("r", GoLean.Loc.base { id := 8341 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "gr"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "rj"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "res"])]) ([[("res", GoLean.Loc.base { id := 8340 }),
  ("rj", GoLean.Loc.base { id := 8339 }),
  ("gr", GoLean.Loc.base { id := 8338 }),
  ("$c1575", GoLean.Loc.base { id := 8335 }),
  ("$c1574", GoLean.Loc.base { id := 8332 }),
  ("$c1573", GoLean.Loc.base { id := 8329 })],
 [],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) ([GoLean.Loc.base { id := 8345 }, GoLean.Loc.base { id := 8346 }, GoLean.Loc.base { id := 8347 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "$c1576", typ := GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" } },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c1576"]
       { key := "raftpb.Message.GetType" }
       #[GoLean.GoCore.Expr.var "m"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "$c1577", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }) },
     GoLean.GoCore.Stmt.makeSlice
       (GoLean.GoCore.Assignee.var "$c1577")
       (GoLean.GoCore.Ty.interface { key := "any" })
       (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))
       (some (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
         (GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "r") (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
           { key := "raft.raft" }
           "id")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.var "gr")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })
         (GoLean.GoCore.Expr.var "$c1576")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.var "rj"))],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "raft.Logger.Infof" }
   #[GoLean.GoCore.Expr.fieldGet
       (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "r") (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
       { key := "raft.raft" }
       "logger",
     GoLean.GoCore.Expr.stringLit
       { bytes := #[37, 120, 32, 104, 97, 115, 32, 114, 101, 99, 101, 105, 118, 101, 100, 32, 37, 100, 32, 37, 115, 32,
                    118, 111, 116, 101, 115, 32, 97, 110, 100, 32, 37, 100, 32, 118, 111, 116, 101, 32, 114, 101, 106,
                    101, 99, 116, 105, 111, 110, 115] },
     GoLean.GoCore.Expr.var "$c1577"],
 GoLean.GoCore.Stmt.breakable
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$sw1578", typ := GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" } },
           GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$sw1578") (GoLean.GoCore.Expr.var "res")],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$swi1579", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
           GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))],
       GoLean.GoCore.Stmt.block
         #[]
         #[GoLean.GoCore.Stmt.ifThenElse
             (GoLean.GoCore.Expr.eqCmp
               (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })
               (GoLean.GoCore.Expr.var "$sw1578")
               (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.uint8)))
             (GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.var "$swi1579")
                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))])
             (GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.ifThenElse
                   (GoLean.GoCore.Expr.eqCmp
                     (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })
                     (GoLean.GoCore.Expr.var "$sw1578")
                     (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint8)))
                   (GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.assign
                         (GoLean.GoCore.Assignee.var "$swi1579")
                         (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))])
                   (GoLean.GoCore.Stmt.seqn #[])])],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$swf1579", typ := GoLean.GoCore.Ty.bool },
           GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.or
           (GoLean.GoCore.Expr.var "$swf1579")
           (GoLean.GoCore.Expr.eqCmp
             (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
             (GoLean.GoCore.Expr.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
             GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.ifThenElse
                   (GoLean.GoCore.Expr.eqCmp
                     (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
                     (GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "r")
                         (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                       { key := "raft.raft" }
                       "state")
                     (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.uint64)))
                   (GoLean.GoCore.Stmt.block
                     #[]
                     #[GoLean.GoCore.Stmt.call
                         #[]
                         { key := "raft.raft.campaign" }
                         #[GoLean.GoCore.Expr.var "r",
                           GoLean.GoCore.Expr.stringLit
                             { bytes := #[67, 97, 109, 112, 97, 105, 103, 110, 69, 108, 101, 99, 116, 105, 111,
                                          110] }]])
                   (GoLean.GoCore.Stmt.block
                     #[]
                     #[GoLean.GoCore.Stmt.call #[] { key := "raft.raft.becomeLeader" } #[GoLean.GoCore.Expr.var "r"],
                       GoLean.GoCore.Stmt.call #[] { key := "raft.raft.bcastAppend" } #[GoLean.GoCore.Expr.var "r"]])]])
         (GoLean.GoCore.Stmt.seqn #[]),
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.or
           (GoLean.GoCore.Expr.var "$swf1579")
           (GoLean.GoCore.Expr.eqCmp
             (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
             (GoLean.GoCore.Expr.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
             GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.call
                   #[]
                   { key := "raft.raft.becomeFollower" }
                   #[GoLean.GoCore.Expr.var "r",
                     GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "r")
                         (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                       { key := "raft.raft" }
                       "Term",
                     GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64)]]])
         (GoLean.GoCore.Stmt.seqn #[])])]) ([[("res", GoLean.Loc.base { id := 8340 }),
  ("rj", GoLean.Loc.base { id := 8339 }),
  ("gr", GoLean.Loc.base { id := 8338 }),
  ("$c1575", GoLean.Loc.base { id := 8335 }),
  ("$c1574", GoLean.Loc.base { id := 8332 }),
  ("$c1573", GoLean.Loc.base { id := 8329 })],
 [],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.or
     (GoLean.GoCore.Expr.var "$swf1582")
     (GoLean.GoCore.Expr.eqCmp
       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
       (GoLean.GoCore.Expr.var "$swi1582")
       (GoLean.GoCore.Expr.intLit 5 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1582") (GoLean.GoCore.Expr.boolLit false)],
       GoLean.GoCore.Stmt.block
         #[]
         #[GoLean.GoCore.Stmt.seqn
             #[GoLean.GoCore.Stmt.initialization
                 { id := "$c1580", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
               GoLean.GoCore.Stmt.call
                 #[GoLean.GoCore.Assignee.var "$c1580"]
                 { key := "raftpb.Message.GetFrom" }
                 #[GoLean.GoCore.Expr.var "m"]],
           GoLean.GoCore.Stmt.seqn
             #[GoLean.GoCore.Stmt.initialization
                 { id := "$c1581", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }) },
               GoLean.GoCore.Stmt.makeSlice
                 (GoLean.GoCore.Assignee.var "$c1581")
                 (GoLean.GoCore.Ty.interface { key := "any" })
                 (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))
                 (some (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "id")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "Term")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "state")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.var "$c1580"))],
           GoLean.GoCore.Stmt.call
             #[]
             { key := "raft.Logger.Debugf" }
             #[GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "r")
                   (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                 { key := "raft.raft" }
                 "logger",
               GoLean.GoCore.Expr.stringLit
                 { bytes := #[37, 120, 32, 91, 116, 101, 114, 109, 32, 37, 100, 32, 115, 116, 97, 116, 101, 32, 37, 118,
                              93, 32, 105, 103, 110, 111, 114, 101, 100, 32, 77, 115, 103, 84, 105, 109, 101, 111, 117,
                              116, 78, 111, 119, 32, 102, 114, 111, 109, 32, 37, 120] },
               GoLean.GoCore.Expr.var "$c1581"]]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.breakableK (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.nil none),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "err"])]) ([[("err", GoLean.Loc.base { id := 8318 })],
 [],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) ([GoLean.Loc.base { id := 8321 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.neqCmp
     (GoLean.GoCore.Ty.interface { key := "error" })
     (GoLean.GoCore.Expr.var "err")
     (GoLean.GoCore.Expr.nil none))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "err"),
           GoLean.GoCore.Stmt.returnStmt]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("err", GoLean.Loc.base { id := 8318 })],
 [],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.breakableK (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.nil none),
     GoLean.GoCore.Stmt.returnStmt]]) ([[],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1790"])]) ([[("$c1790", GoLean.Loc.base { id := 8295 }),
  ("$c1789", GoLean.Loc.base { id := 8291 }),
  ("$c1787", GoLean.Loc.base { id := 8284 }),
  ("$c1784", GoLean.Loc.base { id := 8276 }),
  ("$c1783", GoLean.Loc.base { id := 8273 }),
  ("$c1782", GoLean.Loc.base { id := 8272 }),
  ("$c1779", GoLean.Loc.base { id := 8264 }),
  ("$c1778", GoLean.Loc.base { id := 8261 })],
 [("$res0", GoLean.Loc.base { id := 8260 }),
  ("m", GoLean.Loc.base { id := 8259 }),
  ("rn", GoLean.Loc.base { id := 8258 })]]) ([GoLean.Loc.base { id := 8298 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "$c1790"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("$c1790", GoLean.Loc.base { id := 8295 }),
  ("$c1789", GoLean.Loc.base { id := 8291 }),
  ("$c1787", GoLean.Loc.base { id := 8284 }),
  ("$c1784", GoLean.Loc.base { id := 8276 }),
  ("$c1783", GoLean.Loc.base { id := 8273 }),
  ("$c1782", GoLean.Loc.base { id := 8272 }),
  ("$c1779", GoLean.Loc.base { id := 8264 }),
  ("$c1778", GoLean.Loc.base { id := 8261 })],
 [("$res0", GoLean.Loc.base { id := 8260 }),
  ("m", GoLean.Loc.base { id := 8259 }),
  ("rn", GoLean.Loc.base { id := 8258 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "err"])]) ([[("err", GoLean.Loc.base { id := 8257 })],
 [("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) ([GoLean.Loc.base { id := 8260 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.neqCmp
     (GoLean.GoCore.Ty.interface { key := "error" })
     (GoLean.GoCore.Expr.var "err")
     (GoLean.GoCore.Expr.nil none))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.stringLit { bytes := #[32, 115, 116, 101, 112, 101, 114, 114] }]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("err", GoLean.Loc.base { id := 8257 })],
 [("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$cr0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$cr0"]
       { key := "main.twin.harvest" }
       #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "to"]]]) ([[("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) (GoLean.Sym.Cont.frame ([]) ([[("$c2241", GoLean.Loc.base { id := 8243 }),
  ("$c2240", GoLean.Loc.base { id := 8240 }),
  ("$c2239", GoLean.Loc.base { id := 8232 }),
  ("$c2238", GoLean.Loc.base { id := 8229 }),
  ("$c2237", GoLean.Loc.base { id := 8223 }),
  ("$c2236", GoLean.Loc.base { id := 8215 }),
  ("m", GoLean.Loc.base { id := 8214 }),
  ("picked", GoLean.Loc.base { id := 8212 })],
 [("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) ([]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2242", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2242"]
       { key := "main.twin.projection" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add (GoLean.GoCore.Expr.stringLit { bytes := #[32] }) (GoLean.GoCore.Expr.var "$c2242"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "stuckPropose")
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.continueStmt]) ([[("$c2241", GoLean.Loc.base { id := 8243 }),
  ("$c2240", GoLean.Loc.base { id := 8240 }),
  ("$c2239", GoLean.Loc.base { id := 8232 }),
  ("$c2238", GoLean.Loc.base { id := 8229 }),
  ("$c2237", GoLean.Loc.base { id := 8223 }),
  ("$c2236", GoLean.Loc.base { id := 8215 }),
  ("m", GoLean.Loc.base { id := 8214 }),
  ("picked", GoLean.Loc.base { id := 8212 })],
 [("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2243", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2243"]
       { key := "main.twin.complete" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.and
     (GoLean.GoCore.Expr.var "$c2243")
     (GoLean.GoCore.Expr.eqCmp
       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
       (GoLean.GoCore.Expr.length
         (GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "pending")
         (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.breakStmt])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.greaterCmp
     (GoLean.GoCore.Expr.length
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "pending")
       (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$c2244", typ := GoLean.GoCore.Ty.string },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2244"]
             { key := "itoa" }
             #[GoLean.GoCore.Expr.add
                 (GoLean.GoCore.Expr.var "round")
                 (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.add
             (GoLean.GoCore.Expr.add
               (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
               (GoLean.GoCore.Expr.var "$c2244"))
             (GoLean.GoCore.Expr.stringLit { bytes := #[32] })],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.step" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.structLit
             (GoLean.GoCore.Ty.defined { key := "main.op" })
             #[GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int),
               GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int),
               GoLean.GoCore.Expr.defaultValue (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.stringLit { bytes := #[10] }],
       GoLean.GoCore.Stmt.assign
         (GoLean.GoCore.Assignee.var "stuckPropose")
         (GoLean.GoCore.Expr.add
           (GoLean.GoCore.Expr.var "stuckPropose")
           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.greaterCmp
           (GoLean.GoCore.Expr.var "stuckPropose")
           (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int)))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.addr
                     (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                   (GoLean.GoCore.Expr.boolLit true)],
             GoLean.GoCore.Stmt.call
               #[]
               { key := "main.twin.say" }
               #[GoLean.GoCore.Expr.var "t",
                 GoLean.GoCore.Expr.stringLit
                   { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112, 111, 115, 101, 32, 115,
                                116, 117, 99, 107, 32, 97, 116, 32, 113, 117, 105, 101, 115, 99, 101, 110, 99, 101,
                                10] }],
             GoLean.GoCore.Stmt.breakStmt])
         (GoLean.GoCore.Stmt.seqn #[]),
       GoLean.GoCore.Stmt.continueStmt])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
       (GoLean.GoCore.Expr.boolLit true)],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.stringLit
       { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101, 110, 116, 32, 119, 105,
                    116, 104, 111, 117, 116, 32, 83, 52, 10] }],
 GoLean.GoCore.Stmt.breakStmt]) ([[("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.loop (GoLean.GoCore.Expr.boolLit true) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "$forFirst")
      (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$forFirst") (GoLean.GoCore.Expr.boolLit false))
      (GoLean.GoCore.Stmt.assign
        (GoLean.GoCore.Assignee.var "round")
        (GoLean.GoCore.Expr.add
          (GoLean.GoCore.Expr.var "round")
          (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
    GoLean.GoCore.Stmt.seqn #[],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.lessCmp
        (GoLean.GoCore.Expr.var "round")
        (GoLean.GoCore.Expr.intLit 400 (GoLean.GoCore.IntKind.int)))
      (GoLean.GoCore.Stmt.seqn #[])
      (GoLean.GoCore.Stmt.breakStmt),
    GoLean.GoCore.Stmt.block
      #[]
      #[GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization
              { id := "$c2235",
                typ := GoLean.GoCore.Ty.map
                         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                         (GoLean.GoCore.Ty.bool) },
            GoLean.GoCore.Stmt.makeMap
              (GoLean.GoCore.Assignee.var "$c2235")
              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
              (GoLean.GoCore.Ty.bool)
              none],
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization
              { id := "live",
                typ := GoLean.GoCore.Ty.map
                         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                         (GoLean.GoCore.Ty.bool) },
            GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "live") (GoLean.GoCore.Expr.var "$c2235")],
        GoLean.GoCore.Stmt.block
          #[]
          #[GoLean.GoCore.Stmt.initialization
              { id := "$rcoll",
                typ := GoLean.GoCore.Ty.slice
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rcoll")
              (GoLean.GoCore.Expr.fieldGet
                (GoLean.GoCore.Expr.deref
                  (GoLean.GoCore.Expr.var "t")
                  (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                { key := "main.twin" }
                "net"),
            GoLean.GoCore.Stmt.initialization
              { id := "$rlen", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rlen")
              (GoLean.GoCore.Expr.length (GoLean.GoCore.Expr.var "$rcoll") none),
            GoLean.GoCore.Stmt.initialization
              { id := "$ridx", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$ridx")
              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)),
            GoLean.GoCore.Stmt.initialization { id := "$rfirst", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$rfirst") (GoLean.GoCore.Expr.boolLit true),
            GoLean.GoCore.Stmt.while
              (GoLean.GoCore.Expr.boolLit true)
              (GoLean.GoCore.Stmt.block
                #[]
                #[GoLean.GoCore.Stmt.ifThenElse
                    (GoLean.GoCore.Expr.var "$rfirst")
                    (GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "$rfirst")
                      (GoLean.GoCore.Expr.boolLit false))
                    (GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "$ridx")
                      (GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "$ridx")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
                  GoLean.GoCore.Stmt.ifThenElse
                    (GoLean.GoCore.Expr.atLeastCmp (GoLean.GoCore.Expr.var "$ridx") (GoLean.GoCore.Expr.var "$rlen"))
                    (GoLean.GoCore.Stmt.breakStmt)
                    (GoLean.GoCore.Stmt.seqn #[]),
                  GoLean.GoCore.Stmt.initialization
                    { id := "j", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                  GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "j") (GoLean.GoCore.Expr.var "$ridx"),
                  GoLean.GoCore.Stmt.block
                    #[]
                    #[GoLean.GoCore.Stmt.ifThenElse
                        (GoLean.GoCore.Expr.indexGet
                          (GoLean.GoCore.Expr.fieldGet
                            (GoLean.GoCore.Expr.deref
                              (GoLean.GoCore.Expr.var "t")
                              (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                            { key := "main.twin" }
                            "live")
                          (GoLean.GoCore.Expr.var "j"))
                        (GoLean.GoCore.Stmt.block
                          #[]
                          #[GoLean.GoCore.Stmt.mapAssign
                              (GoLean.GoCore.Expr.var "live")
                              (GoLean.GoCore.Expr.var "j")
                              (GoLean.GoCore.Expr.boolLit true)
                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                              (GoLean.GoCore.Ty.bool)])
                        (GoLean.GoCore.Stmt.seqn #[])]])],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.length
              (GoLean.GoCore.Expr.var "live")
              (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))))
            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "picked", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "picked")
                    (GoLean.GoCore.Expr.intLit (-1) (GoLean.GoCore.IntKind.int))],
              GoLean.GoCore.Stmt.mapRange
                (some "j")
                none
                (GoLean.GoCore.Expr.var "live")
                (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                (GoLean.GoCore.Ty.bool)
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "picked") (GoLean.GoCore.Expr.var "j")],
                    GoLean.GoCore.Stmt.breakStmt]),
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "m",
                      typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "m")
                    (GoLean.GoCore.Expr.indexGet
                      (GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "t")
                          (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                        { key := "main.twin" }
                        "net")
                      (GoLean.GoCore.Expr.var "picked"))],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2236", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2236"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "round")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2237", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2237"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.var "picked"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2238", typ := GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" } },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2238"]
                    { key := "raftpb.Message.GetType" }
                    #[GoLean.GoCore.Expr.var "m"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2239", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2239"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.convert
                        (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                        (GoLean.GoCore.Expr.var "$c2238")]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2240", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2240"]
                    { key := "raftpb.Message.GetTo" }
                    #[GoLean.GoCore.Expr.var "m"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2241", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2241"]
                    { key := "utoa" }
                    #[GoLean.GoCore.Expr.var "$c2240"]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.add
                          (GoLean.GoCore.Expr.add
                            (GoLean.GoCore.Expr.add
                              (GoLean.GoCore.Expr.add
                                (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
                                (GoLean.GoCore.Expr.var "$c2236"))
                              (GoLean.GoCore.Expr.stringLit { bytes := #[32, 112, 105, 99, 107, 35] }))
                            (GoLean.GoCore.Expr.var "$c2237"))
                          (GoLean.GoCore.Expr.stringLit { bytes := #[32, 116, 121, 112, 101] }))
                        (GoLean.GoCore.Expr.var "$c2239"))
                      (GoLean.GoCore.Expr.stringLit { bytes := #[45, 62] }))
                    (GoLean.GoCore.Expr.var "$c2241")],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.deliverIdx" }
                #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "picked"],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2242", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2242"]
                    { key := "main.twin.projection" }
                    #[GoLean.GoCore.Expr.var "t"]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.stringLit { bytes := #[32] })
                      (GoLean.GoCore.Expr.var "$c2242"))
                    (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "stuckPropose")
                    (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
              GoLean.GoCore.Stmt.continueStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "$c2243", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c2243"]
              { key := "main.twin.complete" }
              #[GoLean.GoCore.Expr.var "t"]],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.and
            (GoLean.GoCore.Expr.var "$c2243")
            (GoLean.GoCore.Expr.eqCmp
              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
              (GoLean.GoCore.Expr.length
                (GoLean.GoCore.Expr.fieldGet
                  (GoLean.GoCore.Expr.deref
                    (GoLean.GoCore.Expr.var "t")
                    (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                  { key := "main.twin" }
                  "pending")
                (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
          (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.breakStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.length
              (GoLean.GoCore.Expr.fieldGet
                (GoLean.GoCore.Expr.deref
                  (GoLean.GoCore.Expr.var "t")
                  (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                { key := "main.twin" }
                "pending")
              (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2244", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2244"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "round")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
                      (GoLean.GoCore.Expr.var "$c2244"))
                    (GoLean.GoCore.Expr.stringLit { bytes := #[32] })],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.step" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.structLit
                    (GoLean.GoCore.Ty.defined { key := "main.op" })
                    #[GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int),
                      GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int),
                      GoLean.GoCore.Expr.defaultValue (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.stringLit { bytes := #[10] }],
              GoLean.GoCore.Stmt.assign
                (GoLean.GoCore.Assignee.var "stuckPropose")
                (GoLean.GoCore.Expr.add
                  (GoLean.GoCore.Expr.var "stuckPropose")
                  (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.greaterCmp
                  (GoLean.GoCore.Expr.var "stuckPropose")
                  (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int)))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.addr
                            (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                          (GoLean.GoCore.Expr.boolLit true)],
                    GoLean.GoCore.Stmt.call
                      #[]
                      { key := "main.twin.say" }
                      #[GoLean.GoCore.Expr.var "t",
                        GoLean.GoCore.Expr.stringLit
                          { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112, 111, 115, 101, 32,
                                       115, 116, 117, 99, 107, 32, 97, 116, 32, 113, 117, 105, 101, 115, 99, 101, 110,
                                       99, 101, 10] }],
                    GoLean.GoCore.Stmt.breakStmt])
                (GoLean.GoCore.Stmt.seqn #[]),
              GoLean.GoCore.Stmt.continueStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.addr
                (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
              (GoLean.GoCore.Expr.boolLit true)],
        GoLean.GoCore.Stmt.call
          #[]
          { key := "main.twin.say" }
          #[GoLean.GoCore.Expr.var "t",
            GoLean.GoCore.Expr.stringLit
              { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101, 110, 116, 32,
                           119, 105, 116, 104, 111, 117, 116, 32, 83, 52, 10] }],
        GoLean.GoCore.Stmt.breakStmt]]) ([[("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "comp", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "comp")
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2245", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2245"]
       { key := "main.twin.complete" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.and
     (GoLean.GoCore.Expr.and
       (GoLean.GoCore.Expr.var "$c2245")
       (GoLean.GoCore.Expr.eqCmp
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.length
           (GoLean.GoCore.Expr.fieldGet
             (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
             { key := "main.twin" }
             "pending")
           (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
     (GoLean.GoCore.Expr.not
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "halt")))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "comp")
             (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "floorOK", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "floorOK")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.or
     (GoLean.GoCore.Expr.lessCmp
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "claims")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))
     (GoLean.GoCore.Expr.lessCmp
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "committed")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "floorOK")
             (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2246", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2246"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "violations"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2247", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2247"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "claims"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2248", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2248"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "committed"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2249", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call #[GoLean.GoCore.Assignee.var "$c2249"] { key := "itoa" } #[GoLean.GoCore.Expr.var "comp"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2250", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2250"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.var "floorOK"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2251", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2251"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.var "round"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add
         (GoLean.GoCore.Expr.add
           (GoLean.GoCore.Expr.add
             (GoLean.GoCore.Expr.add
               (GoLean.GoCore.Expr.add
                 (GoLean.GoCore.Expr.add
                   (GoLean.GoCore.Expr.add
                     (GoLean.GoCore.Expr.add
                       (GoLean.GoCore.Expr.add
                         (GoLean.GoCore.Expr.add
                           (GoLean.GoCore.Expr.add
                             (GoLean.GoCore.Expr.stringLit { bytes := #[101, 110, 100, 32, 118, 105, 111, 108, 61] })
                             (GoLean.GoCore.Expr.var "$c2246"))
                           (GoLean.GoCore.Expr.stringLit { bytes := #[32, 99, 108, 97, 105, 109, 115, 61] }))
                         (GoLean.GoCore.Expr.var "$c2247"))
                       (GoLean.GoCore.Expr.stringLit
                         { bytes := #[32, 99, 111, 109, 109, 105, 116, 116, 101, 100, 61] }))
                     (GoLean.GoCore.Expr.var "$c2248"))
                   (GoLean.GoCore.Expr.stringLit { bytes := #[32, 99, 111, 109, 112, 108, 101, 116, 101, 61] }))
                 (GoLean.GoCore.Expr.var "$c2249"))
               (GoLean.GoCore.Expr.stringLit { bytes := #[32, 102, 108, 111, 111, 114, 61] }))
             (GoLean.GoCore.Expr.var "$c2250"))
           (GoLean.GoCore.Expr.stringLit { bytes := #[32, 114, 111, 117, 110, 100, 115, 61] }))
         (GoLean.GoCore.Expr.var "$c2251"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2252", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2252"]
       { key := "main.twin.projection" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add
         (GoLean.GoCore.Expr.stringLit { bytes := #[102, 105, 110, 97, 108, 32] })
         (GoLean.GoCore.Expr.var "$c2252"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "t"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res1") (GoLean.GoCore.Expr.var "comp"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res2") (GoLean.GoCore.Expr.var "floorOK"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "t"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "comp"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "floorOK"])]) ([[("floorOK", GoLean.Loc.base { id := 105 }),
  ("comp", GoLean.Loc.base { id := 104 }),
  ("t", GoLean.Loc.base { id := 103 })],
 [("$res4", GoLean.Loc.base { id := 102 }),
  ("$res3", GoLean.Loc.base { id := 101 }),
  ("$res2", GoLean.Loc.base { id := 100 }),
  ("$res1", GoLean.Loc.base { id := 99 }),
  ("$res0", GoLean.Loc.base { id := 98 })]]) ([GoLean.Loc.base { id := 106 }, GoLean.Loc.base { id := 107 }, GoLean.Loc.base { id := 108 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res0")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "violations"),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res1")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "claims"),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res2")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "committed"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res3") (GoLean.GoCore.Expr.var "comp"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res4") (GoLean.GoCore.Expr.var "floorOK"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("floorOK", GoLean.Loc.base { id := 105 }),
  ("comp", GoLean.Loc.base { id := 104 }),
  ("t", GoLean.Loc.base { id := 103 })],
 [("$res4", GoLean.Loc.base { id := 102 }),
  ("$res3", GoLean.Loc.base { id := 101 }),
  ("$res2", GoLean.Loc.base { id := 100 }),
  ("$res1", GoLean.Loc.base { id := 99 }),
  ("$res0", GoLean.Loc.base { id := 98 })]]) (GoLean.Sym.Cont.frame ([]) ([]) ([]) [] (GoLean.Sym.Cont.stop) false)) false)))))))) false))) false)) false)))))) false)))))) false)) false))))

def vrSB6 : SymState :=
  (GoLean.Sym.State.mk
  [((GoLean.Loc.base { id := 15 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 57 })))),
  ((GoLean.Loc.base { id := 18 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.lockedRand" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 67 })))),
  ((GoLean.Loc.base { id := 27 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))]))),
  ((GoLean.Loc.base { id := 28 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))]))),
  ((GoLean.Loc.base { id := 57 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Commit"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 67 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.lockedRand" })) (GoLean.Sym.Value.struct ({ key := "raft.lockedRand" }) #[(("mu"), (GoLean.Sym.Value.syncData (GoLean.SyncPrim.mutex false)))]))),
  ((GoLean.Loc.base { id := 110 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 115 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[]))),
  ((GoLean.Loc.base { id := 121 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twin" })) (GoLean.Sym.Value.struct ({ key := "main.twin" }) #[(("nodes"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 1764 }), offset := 0, len := 3, cap := 4 }))),
  (("net"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8195 }), offset := 0, len := 1, cap := 1 }))),
  (("live"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8196 }), offset := 0, len := 1, cap := 1 }))),
  (("leaderOf"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 115 }) }))),
  (("byIndex"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 118 }) }))),
  (("claims"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("violations"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("pending"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 136 }), offset := 0, len := 2, cap := 4 }))),
  (("driven"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("seq"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.int))),
  (("trace"), (GoLean.Sym.Value.string ({ bytes := #[91, 99, 104, 111, 105, 99, 101, 45, 100, 114, 105, 118, 101, 110, 93, 10, 99, 97, 109, 112, 97, 105, 103,
             110, 49, 114, 49, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 53, 45, 62, 50, 32, 32, 124, 67,
             49, 47, 49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 70, 48, 47, 48, 47, 48, 32, 110, 101, 116, 61, 50, 10,
             114, 50, 32, 112, 105, 99, 107, 35, 49, 32, 116, 121, 112, 101, 53, 45, 62, 51, 32, 32, 124, 67, 49, 47,
             49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 110, 101, 116, 61, 50, 10, 114, 51,
             32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 54, 45, 62, 49] }))),
  (("halt"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 170 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1742 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 179 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 167 }) })))]))),
  ((GoLean.Loc.base { id := 179 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.struct ({ key := "raft.MemoryStorage" }) #[(("Mutex"), (GoLean.Sym.Value.syncData (GoLean.SyncPrim.mutex false))),
  (("hardState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5675 }))),
  (("snapshot"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 258 }))),
  (("ents"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 300 }), offset := 0, len := 1, cap := 1 }))),
  (("callStats"), (GoLean.Sym.Value.struct ({ key := "raft.inMemStorageCallStats" }) #[(("initialState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("firstIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 4) (GoLean.GoCore.IntKind.int))),
  (("lastIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 15) (GoLean.GoCore.IntKind.int))),
  (("entries"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.int))),
  (("snapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))]))]))),
  ((GoLean.Loc.base { id := 286 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 295 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 298 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 286 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 295 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 300 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 298 }))]))),
  ((GoLean.Loc.base { id := 349 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })) (GoLean.Sym.Value.struct ({ key := "raft.raftLog" }) #[(("storage"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 179 })))),
  (("unstable"), (GoLean.Sym.Value.struct ({ key := "raft.unstable" }) #[(("snapshot"), (GoLean.Sym.Value.nil)),
  (("entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("offset"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("snapshotInProgress"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("offsetInProgress"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 }))))])),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applying"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("maxApplyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 389 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raft" })) (GoLean.Sym.Value.struct ({ key := "raft.raft" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Vote"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("readStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("raftLog"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 349 }))),
  (("maxMsgSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("maxUncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64))),
  (("trk"), (GoLean.Sym.Value.struct ({ key := "tracker.ProgressTracker" }) #[(("Config"), (GoLean.Sym.Value.struct ({ key := "tracker.Config" }) #[(("Voters"), (GoLean.Sym.Value.array #[(GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1086 }) })),
  (GoLean.Sym.Value.map ({ base := none }))])),
  (("AutoLeave"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Learners"), (GoLean.Sym.Value.map ({ base := none }))),
  (("LearnersNext"), (GoLean.Sym.Value.map ({ base := none })))])),
  (("Progress"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1103 }) }))),
  (("Votes"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 5058 }) }))),
  (("MaxInflight"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 256) (GoLean.GoCore.IntKind.int))),
  (("MaxInflightBytes"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64)))])),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("isLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("msgs"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("msgsAfterAppend"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("leadTransferee"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("pendingConfIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("disableConfChangeValidation"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("uncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("readOnly"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5198 }))),
  (("electionElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("heartbeatElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("checkQuorum"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("preVote"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("heartbeatTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("electionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("randomizedElectionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("disableProposalForwarding"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("stepDownOnRemoval"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("tick"), (GoLean.Sym.Value.funcVal ({ key := "raft.raft.tickElection" }) [(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 }))])),
  (("step"), (GoLean.Sym.Value.funcVal ({ key := "raft.stepCandidate" }) [])),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("pendingReadIndexMessages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("traceLogger"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 1086 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[])),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[])),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[]))]))),
  ((GoLean.Loc.base { id := 1103 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1107 }))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1110 }))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1212 })))]))),
  ((GoLean.Loc.base { id := 1107 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5102 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1110 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5156 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1212 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5189 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1742 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })) (GoLean.Sym.Value.struct ({ key := "raft.RawNode" }) #[(("raft"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 }))),
  (("asyncStorageWrites"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("prevSoftSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5661 }))),
  (("prevHardSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5675 }))),
  (("stepsOnAdvance"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 5758 }), offset := 0, len := 0, cap := 4 })))]))),
  ((GoLean.Loc.base { id := 1764 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 170 })),
  (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1770 })),
  (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3369 })),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 1770 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1767 }) })))]))),
  ((GoLean.Loc.base { id := 3369 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 4941 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3378 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 3366 }) })))]))),
  ((GoLean.Loc.base { id := 5058 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))))) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))]))),
  ((GoLean.Loc.base { id := 5198 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.readOnly" })) (GoLean.Sym.Value.struct ({ key := "raft.readOnly" }) #[(("option"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("acks"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 5195 }) }))),
  (("unconfirmedReads"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("confirmedReads"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 5661 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 5666 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5669 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5672 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5675 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5666 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5669 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5672 })))]))),
  ((GoLean.Loc.base { id := 5758 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 6070 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6072 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8191 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 6) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8192 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8193 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8194 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Message" }) #[(("Type"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8191 }))),
  (("To"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8192 }))),
  (("From"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8193 }))),
  (("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8197 }))),
  (("LogTerm"), (GoLean.Sym.Value.nil)),
  (("Index"), (GoLean.Sym.Value.nil)),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Commit"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("Reject"), (GoLean.Sym.Value.nil)),
  (("RejectHint"), (GoLean.Sym.Value.nil)),
  (("Context"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Responses"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 8195 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 }))]))),
  ((GoLean.Loc.base { id := 8196 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))]))),
  ((GoLean.Loc.base { id := 8197 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8198 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8199 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8200 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8198 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8199 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 8201 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8200 }))]))),
  ((GoLean.Loc.base { id := 8202 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8203 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8204 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 8205 }) })))),
  ((GoLean.Loc.base { id := 8205 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.int)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))]))),
  ((GoLean.Loc.base { id := 8206 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 8205 }) })))),
  ((GoLean.Loc.base { id := 8207 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8195 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 8208 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8209 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8210 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8211 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8212 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8213 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8214 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8215 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8216 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 2) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8217 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8218 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8219 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 2) (GoLean.Sym.SymInt.lit 1))))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8220 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8221 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8222 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8223 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8224 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8225 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8226 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8227 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8228 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8229 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8230 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8231 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8232 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8233 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8234 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8235 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8236 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int32)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8237 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8238 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8239 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8240 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8241 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8242 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8243 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8244 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8245 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8246 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8247 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8248 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 8249 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[114, 51, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 54, 45, 62, 49] })))),
  ((GoLean.Loc.base { id := 8250 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 8251 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8252 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8253 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8254 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8255 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8256 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 170 })))),
  ((GoLean.Loc.base { id := 8257 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8258 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1742 })))),
  ((GoLean.Loc.base { id := 8259 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8260 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8261 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8262 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8263 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8264 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8265 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8266 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8267 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8268 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8269 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 27 }), offset := 0, len := 23, cap := 23 })))),
  ((GoLean.Loc.base { id := 8270 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8271 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int32)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int32)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8272 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8273 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8274 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8275 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8276 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8277 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8278 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8279 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8280 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8281 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 28 }), offset := 0, len := 23, cap := 23 })))),
  ((GoLean.Loc.base { id := 8282 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8283 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int32)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int32)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8284 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8285 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8286 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8287 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8288 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8289 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8290 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8291 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8292 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8293 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8294 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8295 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8296 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8297 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8298 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8299 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8300 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8301 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 3)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8302 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8303 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8304 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8305 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8306 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8307 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8308 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8309 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8310 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8311 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8312 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8313 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8314 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8315 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8316 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 4)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8317 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8318 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8319 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8320 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8321 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8322 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8323 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8324 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8325 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8326 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8327 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 4)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8328 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8329 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8330 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8331 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8332 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8333 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8334 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8335 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8336 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8337 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8338 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8339 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8340 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8341 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8342 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8343 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8344 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8345 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8346 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8347 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8348 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8349 }), offset := 0, len := 4, cap := 4 })))),
  ((GoLean.Loc.base { id := 8349 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 8350 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  ((GoLean.Loc.base { id := 8351 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[37, 120, 32, 114, 101, 99, 101, 105, 118, 101, 100, 32, 37, 115, 32, 102, 114, 111, 109, 32, 37, 120, 32,
             97, 116, 32, 116, 101, 114, 109, 32, 37, 100] })))),
  ((GoLean.Loc.base { id := 8352 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8349 }), offset := 0, len := 4, cap := 4 })))),
  ((GoLean.Loc.base { id := 8353 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 389 }) { key := "raft.raft" } "trk")))),
  ((GoLean.Loc.base { id := 8354 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8355 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8356 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8357 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8358 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8359 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8360 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8361 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 389 }) { key := "raft.raft" } "trk")))),
  ((GoLean.Loc.base { id := 8362 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 0) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8363 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8364 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8365 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8366 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1107 })))),
  ((GoLean.Loc.base { id := 8367 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8368 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))))]
  8369)

def vrCB6 : SymConfig :=
  (GoLean.Sym.Config.next (GoLean.Sym.Cont.mapIterK (some "id") (some "pr") (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.fieldGet
        (GoLean.GoCore.Expr.deref
          (GoLean.GoCore.Expr.var "pr")
          (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))
        { key := "tracker.Progress" }
        "IsLearner")
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.seqn
      #[GoLean.GoCore.Stmt.initialization { id := "v", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.initialization { id := "voted", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.mapLookup
          (GoLean.GoCore.Assignee.var "v")
          (GoLean.GoCore.Assignee.var "voted")
          (GoLean.GoCore.Expr.fieldGet
            (GoLean.GoCore.Expr.deref
              (GoLean.GoCore.Expr.var "p")
              (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
            { key := "tracker.ProgressTracker" }
            "Votes")
          (GoLean.GoCore.Expr.var "id")
          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
          (GoLean.GoCore.Ty.bool)],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "voted"))
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "v")
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "granted")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "granted")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "rejected")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "rejected")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])]) (some (GoLean.Loc.base { id := 1103 })) #[(GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))] #[(GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)),
  (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)),
  (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64))] ([[],
 [("$res2", GoLean.Loc.base { id := 8364 }),
  ("rejected", GoLean.Loc.base { id := 8363 }),
  ("granted", GoLean.Loc.base { id := 8362 }),
  ("p", GoLean.Loc.base { id := 8361 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "result", typ := GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" } },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "result"]
       { key := "quorum.JointConfig.VoteResult" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.fieldGet
             (GoLean.GoCore.Expr.deref
               (GoLean.GoCore.Expr.var "p")
               (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
             { key := "tracker.ProgressTracker" }
             "Config")
           { key := "tracker.Config" }
           "Voters",
         GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref
             (GoLean.GoCore.Expr.var "p")
             (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
           { key := "tracker.ProgressTracker" }
           "Votes"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "granted") (GoLean.GoCore.Expr.var "granted"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "rejected") (GoLean.GoCore.Expr.var "rejected"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res2") (GoLean.GoCore.Expr.var "result"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[],
 [("$res2", GoLean.Loc.base { id := 8364 }),
  ("rejected", GoLean.Loc.base { id := 8363 }),
  ("granted", GoLean.Loc.base { id := 8362 }),
  ("p", GoLean.Loc.base { id := 8361 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1353"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1354"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1355"])]) ([[("$c1355", GoLean.Loc.base { id := 8360 }),
  ("$c1354", GoLean.Loc.base { id := 8359 }),
  ("$c1353", GoLean.Loc.base { id := 8358 })],
 [("result", GoLean.Loc.base { id := 8347 }),
  ("rejected", GoLean.Loc.base { id := 8346 }),
  ("granted", GoLean.Loc.base { id := 8345 }),
  ("v", GoLean.Loc.base { id := 8344 }),
  ("t", GoLean.Loc.base { id := 8343 }),
  ("id", GoLean.Loc.base { id := 8342 }),
  ("r", GoLean.Loc.base { id := 8341 })]]) ([GoLean.Loc.base { id := 8362 }, GoLean.Loc.base { id := 8363 }, GoLean.Loc.base { id := 8364 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "granted") (GoLean.GoCore.Expr.var "$c1353"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "rejected") (GoLean.GoCore.Expr.var "$c1354"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "result") (GoLean.GoCore.Expr.var "$c1355"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("$c1355", GoLean.Loc.base { id := 8360 }),
  ("$c1354", GoLean.Loc.base { id := 8359 }),
  ("$c1353", GoLean.Loc.base { id := 8358 })],
 [("result", GoLean.Loc.base { id := 8347 }),
  ("rejected", GoLean.Loc.base { id := 8346 }),
  ("granted", GoLean.Loc.base { id := 8345 }),
  ("v", GoLean.Loc.base { id := 8344 }),
  ("t", GoLean.Loc.base { id := 8343 }),
  ("id", GoLean.Loc.base { id := 8342 }),
  ("r", GoLean.Loc.base { id := 8341 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "gr"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "rj"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "res"])]) ([[("res", GoLean.Loc.base { id := 8340 }),
  ("rj", GoLean.Loc.base { id := 8339 }),
  ("gr", GoLean.Loc.base { id := 8338 }),
  ("$c1575", GoLean.Loc.base { id := 8335 }),
  ("$c1574", GoLean.Loc.base { id := 8332 }),
  ("$c1573", GoLean.Loc.base { id := 8329 })],
 [],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) ([GoLean.Loc.base { id := 8345 }, GoLean.Loc.base { id := 8346 }, GoLean.Loc.base { id := 8347 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "$c1576", typ := GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" } },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c1576"]
       { key := "raftpb.Message.GetType" }
       #[GoLean.GoCore.Expr.var "m"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "$c1577", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }) },
     GoLean.GoCore.Stmt.makeSlice
       (GoLean.GoCore.Assignee.var "$c1577")
       (GoLean.GoCore.Ty.interface { key := "any" })
       (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))
       (some (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
         (GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "r") (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
           { key := "raft.raft" }
           "id")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.var "gr")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })
         (GoLean.GoCore.Expr.var "$c1576")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.var "rj"))],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "raft.Logger.Infof" }
   #[GoLean.GoCore.Expr.fieldGet
       (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "r") (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
       { key := "raft.raft" }
       "logger",
     GoLean.GoCore.Expr.stringLit
       { bytes := #[37, 120, 32, 104, 97, 115, 32, 114, 101, 99, 101, 105, 118, 101, 100, 32, 37, 100, 32, 37, 115, 32,
                    118, 111, 116, 101, 115, 32, 97, 110, 100, 32, 37, 100, 32, 118, 111, 116, 101, 32, 114, 101, 106,
                    101, 99, 116, 105, 111, 110, 115] },
     GoLean.GoCore.Expr.var "$c1577"],
 GoLean.GoCore.Stmt.breakable
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$sw1578", typ := GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" } },
           GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$sw1578") (GoLean.GoCore.Expr.var "res")],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$swi1579", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
           GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))],
       GoLean.GoCore.Stmt.block
         #[]
         #[GoLean.GoCore.Stmt.ifThenElse
             (GoLean.GoCore.Expr.eqCmp
               (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })
               (GoLean.GoCore.Expr.var "$sw1578")
               (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.uint8)))
             (GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.var "$swi1579")
                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))])
             (GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.ifThenElse
                   (GoLean.GoCore.Expr.eqCmp
                     (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })
                     (GoLean.GoCore.Expr.var "$sw1578")
                     (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint8)))
                   (GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.assign
                         (GoLean.GoCore.Assignee.var "$swi1579")
                         (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))])
                   (GoLean.GoCore.Stmt.seqn #[])])],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$swf1579", typ := GoLean.GoCore.Ty.bool },
           GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.or
           (GoLean.GoCore.Expr.var "$swf1579")
           (GoLean.GoCore.Expr.eqCmp
             (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
             (GoLean.GoCore.Expr.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
             GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.ifThenElse
                   (GoLean.GoCore.Expr.eqCmp
                     (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
                     (GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "r")
                         (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                       { key := "raft.raft" }
                       "state")
                     (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.uint64)))
                   (GoLean.GoCore.Stmt.block
                     #[]
                     #[GoLean.GoCore.Stmt.call
                         #[]
                         { key := "raft.raft.campaign" }
                         #[GoLean.GoCore.Expr.var "r",
                           GoLean.GoCore.Expr.stringLit
                             { bytes := #[67, 97, 109, 112, 97, 105, 103, 110, 69, 108, 101, 99, 116, 105, 111,
                                          110] }]])
                   (GoLean.GoCore.Stmt.block
                     #[]
                     #[GoLean.GoCore.Stmt.call #[] { key := "raft.raft.becomeLeader" } #[GoLean.GoCore.Expr.var "r"],
                       GoLean.GoCore.Stmt.call #[] { key := "raft.raft.bcastAppend" } #[GoLean.GoCore.Expr.var "r"]])]])
         (GoLean.GoCore.Stmt.seqn #[]),
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.or
           (GoLean.GoCore.Expr.var "$swf1579")
           (GoLean.GoCore.Expr.eqCmp
             (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
             (GoLean.GoCore.Expr.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
             GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.call
                   #[]
                   { key := "raft.raft.becomeFollower" }
                   #[GoLean.GoCore.Expr.var "r",
                     GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "r")
                         (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                       { key := "raft.raft" }
                       "Term",
                     GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64)]]])
         (GoLean.GoCore.Stmt.seqn #[])])]) ([[("res", GoLean.Loc.base { id := 8340 }),
  ("rj", GoLean.Loc.base { id := 8339 }),
  ("gr", GoLean.Loc.base { id := 8338 }),
  ("$c1575", GoLean.Loc.base { id := 8335 }),
  ("$c1574", GoLean.Loc.base { id := 8332 }),
  ("$c1573", GoLean.Loc.base { id := 8329 })],
 [],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.or
     (GoLean.GoCore.Expr.var "$swf1582")
     (GoLean.GoCore.Expr.eqCmp
       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
       (GoLean.GoCore.Expr.var "$swi1582")
       (GoLean.GoCore.Expr.intLit 5 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1582") (GoLean.GoCore.Expr.boolLit false)],
       GoLean.GoCore.Stmt.block
         #[]
         #[GoLean.GoCore.Stmt.seqn
             #[GoLean.GoCore.Stmt.initialization
                 { id := "$c1580", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
               GoLean.GoCore.Stmt.call
                 #[GoLean.GoCore.Assignee.var "$c1580"]
                 { key := "raftpb.Message.GetFrom" }
                 #[GoLean.GoCore.Expr.var "m"]],
           GoLean.GoCore.Stmt.seqn
             #[GoLean.GoCore.Stmt.initialization
                 { id := "$c1581", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }) },
               GoLean.GoCore.Stmt.makeSlice
                 (GoLean.GoCore.Assignee.var "$c1581")
                 (GoLean.GoCore.Ty.interface { key := "any" })
                 (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))
                 (some (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "id")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "Term")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "state")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.var "$c1580"))],
           GoLean.GoCore.Stmt.call
             #[]
             { key := "raft.Logger.Debugf" }
             #[GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "r")
                   (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                 { key := "raft.raft" }
                 "logger",
               GoLean.GoCore.Expr.stringLit
                 { bytes := #[37, 120, 32, 91, 116, 101, 114, 109, 32, 37, 100, 32, 115, 116, 97, 116, 101, 32, 37, 118,
                              93, 32, 105, 103, 110, 111, 114, 101, 100, 32, 77, 115, 103, 84, 105, 109, 101, 111, 117,
                              116, 78, 111, 119, 32, 102, 114, 111, 109, 32, 37, 120] },
               GoLean.GoCore.Expr.var "$c1581"]]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.breakableK (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.nil none),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "err"])]) ([[("err", GoLean.Loc.base { id := 8318 })],
 [],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) ([GoLean.Loc.base { id := 8321 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.neqCmp
     (GoLean.GoCore.Ty.interface { key := "error" })
     (GoLean.GoCore.Expr.var "err")
     (GoLean.GoCore.Expr.nil none))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "err"),
           GoLean.GoCore.Stmt.returnStmt]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("err", GoLean.Loc.base { id := 8318 })],
 [],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.breakableK (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.nil none),
     GoLean.GoCore.Stmt.returnStmt]]) ([[],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1790"])]) ([[("$c1790", GoLean.Loc.base { id := 8295 }),
  ("$c1789", GoLean.Loc.base { id := 8291 }),
  ("$c1787", GoLean.Loc.base { id := 8284 }),
  ("$c1784", GoLean.Loc.base { id := 8276 }),
  ("$c1783", GoLean.Loc.base { id := 8273 }),
  ("$c1782", GoLean.Loc.base { id := 8272 }),
  ("$c1779", GoLean.Loc.base { id := 8264 }),
  ("$c1778", GoLean.Loc.base { id := 8261 })],
 [("$res0", GoLean.Loc.base { id := 8260 }),
  ("m", GoLean.Loc.base { id := 8259 }),
  ("rn", GoLean.Loc.base { id := 8258 })]]) ([GoLean.Loc.base { id := 8298 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "$c1790"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("$c1790", GoLean.Loc.base { id := 8295 }),
  ("$c1789", GoLean.Loc.base { id := 8291 }),
  ("$c1787", GoLean.Loc.base { id := 8284 }),
  ("$c1784", GoLean.Loc.base { id := 8276 }),
  ("$c1783", GoLean.Loc.base { id := 8273 }),
  ("$c1782", GoLean.Loc.base { id := 8272 }),
  ("$c1779", GoLean.Loc.base { id := 8264 }),
  ("$c1778", GoLean.Loc.base { id := 8261 })],
 [("$res0", GoLean.Loc.base { id := 8260 }),
  ("m", GoLean.Loc.base { id := 8259 }),
  ("rn", GoLean.Loc.base { id := 8258 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "err"])]) ([[("err", GoLean.Loc.base { id := 8257 })],
 [("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) ([GoLean.Loc.base { id := 8260 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.neqCmp
     (GoLean.GoCore.Ty.interface { key := "error" })
     (GoLean.GoCore.Expr.var "err")
     (GoLean.GoCore.Expr.nil none))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.stringLit { bytes := #[32, 115, 116, 101, 112, 101, 114, 114] }]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("err", GoLean.Loc.base { id := 8257 })],
 [("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$cr0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$cr0"]
       { key := "main.twin.harvest" }
       #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "to"]]]) ([[("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) (GoLean.Sym.Cont.frame ([]) ([[("$c2241", GoLean.Loc.base { id := 8243 }),
  ("$c2240", GoLean.Loc.base { id := 8240 }),
  ("$c2239", GoLean.Loc.base { id := 8232 }),
  ("$c2238", GoLean.Loc.base { id := 8229 }),
  ("$c2237", GoLean.Loc.base { id := 8223 }),
  ("$c2236", GoLean.Loc.base { id := 8215 }),
  ("m", GoLean.Loc.base { id := 8214 }),
  ("picked", GoLean.Loc.base { id := 8212 })],
 [("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) ([]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2242", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2242"]
       { key := "main.twin.projection" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add (GoLean.GoCore.Expr.stringLit { bytes := #[32] }) (GoLean.GoCore.Expr.var "$c2242"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "stuckPropose")
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.continueStmt]) ([[("$c2241", GoLean.Loc.base { id := 8243 }),
  ("$c2240", GoLean.Loc.base { id := 8240 }),
  ("$c2239", GoLean.Loc.base { id := 8232 }),
  ("$c2238", GoLean.Loc.base { id := 8229 }),
  ("$c2237", GoLean.Loc.base { id := 8223 }),
  ("$c2236", GoLean.Loc.base { id := 8215 }),
  ("m", GoLean.Loc.base { id := 8214 }),
  ("picked", GoLean.Loc.base { id := 8212 })],
 [("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2243", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2243"]
       { key := "main.twin.complete" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.and
     (GoLean.GoCore.Expr.var "$c2243")
     (GoLean.GoCore.Expr.eqCmp
       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
       (GoLean.GoCore.Expr.length
         (GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "pending")
         (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.breakStmt])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.greaterCmp
     (GoLean.GoCore.Expr.length
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "pending")
       (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$c2244", typ := GoLean.GoCore.Ty.string },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2244"]
             { key := "itoa" }
             #[GoLean.GoCore.Expr.add
                 (GoLean.GoCore.Expr.var "round")
                 (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.add
             (GoLean.GoCore.Expr.add
               (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
               (GoLean.GoCore.Expr.var "$c2244"))
             (GoLean.GoCore.Expr.stringLit { bytes := #[32] })],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.step" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.structLit
             (GoLean.GoCore.Ty.defined { key := "main.op" })
             #[GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int),
               GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int),
               GoLean.GoCore.Expr.defaultValue (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.stringLit { bytes := #[10] }],
       GoLean.GoCore.Stmt.assign
         (GoLean.GoCore.Assignee.var "stuckPropose")
         (GoLean.GoCore.Expr.add
           (GoLean.GoCore.Expr.var "stuckPropose")
           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.greaterCmp
           (GoLean.GoCore.Expr.var "stuckPropose")
           (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int)))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.addr
                     (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                   (GoLean.GoCore.Expr.boolLit true)],
             GoLean.GoCore.Stmt.call
               #[]
               { key := "main.twin.say" }
               #[GoLean.GoCore.Expr.var "t",
                 GoLean.GoCore.Expr.stringLit
                   { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112, 111, 115, 101, 32, 115,
                                116, 117, 99, 107, 32, 97, 116, 32, 113, 117, 105, 101, 115, 99, 101, 110, 99, 101,
                                10] }],
             GoLean.GoCore.Stmt.breakStmt])
         (GoLean.GoCore.Stmt.seqn #[]),
       GoLean.GoCore.Stmt.continueStmt])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
       (GoLean.GoCore.Expr.boolLit true)],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.stringLit
       { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101, 110, 116, 32, 119, 105,
                    116, 104, 111, 117, 116, 32, 83, 52, 10] }],
 GoLean.GoCore.Stmt.breakStmt]) ([[("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.loop (GoLean.GoCore.Expr.boolLit true) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "$forFirst")
      (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$forFirst") (GoLean.GoCore.Expr.boolLit false))
      (GoLean.GoCore.Stmt.assign
        (GoLean.GoCore.Assignee.var "round")
        (GoLean.GoCore.Expr.add
          (GoLean.GoCore.Expr.var "round")
          (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
    GoLean.GoCore.Stmt.seqn #[],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.lessCmp
        (GoLean.GoCore.Expr.var "round")
        (GoLean.GoCore.Expr.intLit 400 (GoLean.GoCore.IntKind.int)))
      (GoLean.GoCore.Stmt.seqn #[])
      (GoLean.GoCore.Stmt.breakStmt),
    GoLean.GoCore.Stmt.block
      #[]
      #[GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization
              { id := "$c2235",
                typ := GoLean.GoCore.Ty.map
                         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                         (GoLean.GoCore.Ty.bool) },
            GoLean.GoCore.Stmt.makeMap
              (GoLean.GoCore.Assignee.var "$c2235")
              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
              (GoLean.GoCore.Ty.bool)
              none],
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization
              { id := "live",
                typ := GoLean.GoCore.Ty.map
                         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                         (GoLean.GoCore.Ty.bool) },
            GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "live") (GoLean.GoCore.Expr.var "$c2235")],
        GoLean.GoCore.Stmt.block
          #[]
          #[GoLean.GoCore.Stmt.initialization
              { id := "$rcoll",
                typ := GoLean.GoCore.Ty.slice
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rcoll")
              (GoLean.GoCore.Expr.fieldGet
                (GoLean.GoCore.Expr.deref
                  (GoLean.GoCore.Expr.var "t")
                  (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                { key := "main.twin" }
                "net"),
            GoLean.GoCore.Stmt.initialization
              { id := "$rlen", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rlen")
              (GoLean.GoCore.Expr.length (GoLean.GoCore.Expr.var "$rcoll") none),
            GoLean.GoCore.Stmt.initialization
              { id := "$ridx", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$ridx")
              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)),
            GoLean.GoCore.Stmt.initialization { id := "$rfirst", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$rfirst") (GoLean.GoCore.Expr.boolLit true),
            GoLean.GoCore.Stmt.while
              (GoLean.GoCore.Expr.boolLit true)
              (GoLean.GoCore.Stmt.block
                #[]
                #[GoLean.GoCore.Stmt.ifThenElse
                    (GoLean.GoCore.Expr.var "$rfirst")
                    (GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "$rfirst")
                      (GoLean.GoCore.Expr.boolLit false))
                    (GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "$ridx")
                      (GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "$ridx")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
                  GoLean.GoCore.Stmt.ifThenElse
                    (GoLean.GoCore.Expr.atLeastCmp (GoLean.GoCore.Expr.var "$ridx") (GoLean.GoCore.Expr.var "$rlen"))
                    (GoLean.GoCore.Stmt.breakStmt)
                    (GoLean.GoCore.Stmt.seqn #[]),
                  GoLean.GoCore.Stmt.initialization
                    { id := "j", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                  GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "j") (GoLean.GoCore.Expr.var "$ridx"),
                  GoLean.GoCore.Stmt.block
                    #[]
                    #[GoLean.GoCore.Stmt.ifThenElse
                        (GoLean.GoCore.Expr.indexGet
                          (GoLean.GoCore.Expr.fieldGet
                            (GoLean.GoCore.Expr.deref
                              (GoLean.GoCore.Expr.var "t")
                              (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                            { key := "main.twin" }
                            "live")
                          (GoLean.GoCore.Expr.var "j"))
                        (GoLean.GoCore.Stmt.block
                          #[]
                          #[GoLean.GoCore.Stmt.mapAssign
                              (GoLean.GoCore.Expr.var "live")
                              (GoLean.GoCore.Expr.var "j")
                              (GoLean.GoCore.Expr.boolLit true)
                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                              (GoLean.GoCore.Ty.bool)])
                        (GoLean.GoCore.Stmt.seqn #[])]])],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.length
              (GoLean.GoCore.Expr.var "live")
              (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))))
            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "picked", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "picked")
                    (GoLean.GoCore.Expr.intLit (-1) (GoLean.GoCore.IntKind.int))],
              GoLean.GoCore.Stmt.mapRange
                (some "j")
                none
                (GoLean.GoCore.Expr.var "live")
                (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                (GoLean.GoCore.Ty.bool)
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "picked") (GoLean.GoCore.Expr.var "j")],
                    GoLean.GoCore.Stmt.breakStmt]),
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "m",
                      typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "m")
                    (GoLean.GoCore.Expr.indexGet
                      (GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "t")
                          (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                        { key := "main.twin" }
                        "net")
                      (GoLean.GoCore.Expr.var "picked"))],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2236", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2236"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "round")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2237", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2237"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.var "picked"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2238", typ := GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" } },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2238"]
                    { key := "raftpb.Message.GetType" }
                    #[GoLean.GoCore.Expr.var "m"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2239", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2239"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.convert
                        (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                        (GoLean.GoCore.Expr.var "$c2238")]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2240", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2240"]
                    { key := "raftpb.Message.GetTo" }
                    #[GoLean.GoCore.Expr.var "m"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2241", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2241"]
                    { key := "utoa" }
                    #[GoLean.GoCore.Expr.var "$c2240"]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.add
                          (GoLean.GoCore.Expr.add
                            (GoLean.GoCore.Expr.add
                              (GoLean.GoCore.Expr.add
                                (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
                                (GoLean.GoCore.Expr.var "$c2236"))
                              (GoLean.GoCore.Expr.stringLit { bytes := #[32, 112, 105, 99, 107, 35] }))
                            (GoLean.GoCore.Expr.var "$c2237"))
                          (GoLean.GoCore.Expr.stringLit { bytes := #[32, 116, 121, 112, 101] }))
                        (GoLean.GoCore.Expr.var "$c2239"))
                      (GoLean.GoCore.Expr.stringLit { bytes := #[45, 62] }))
                    (GoLean.GoCore.Expr.var "$c2241")],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.deliverIdx" }
                #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "picked"],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2242", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2242"]
                    { key := "main.twin.projection" }
                    #[GoLean.GoCore.Expr.var "t"]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.stringLit { bytes := #[32] })
                      (GoLean.GoCore.Expr.var "$c2242"))
                    (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "stuckPropose")
                    (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
              GoLean.GoCore.Stmt.continueStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "$c2243", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c2243"]
              { key := "main.twin.complete" }
              #[GoLean.GoCore.Expr.var "t"]],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.and
            (GoLean.GoCore.Expr.var "$c2243")
            (GoLean.GoCore.Expr.eqCmp
              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
              (GoLean.GoCore.Expr.length
                (GoLean.GoCore.Expr.fieldGet
                  (GoLean.GoCore.Expr.deref
                    (GoLean.GoCore.Expr.var "t")
                    (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                  { key := "main.twin" }
                  "pending")
                (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
          (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.breakStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.length
              (GoLean.GoCore.Expr.fieldGet
                (GoLean.GoCore.Expr.deref
                  (GoLean.GoCore.Expr.var "t")
                  (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                { key := "main.twin" }
                "pending")
              (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2244", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2244"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "round")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
                      (GoLean.GoCore.Expr.var "$c2244"))
                    (GoLean.GoCore.Expr.stringLit { bytes := #[32] })],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.step" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.structLit
                    (GoLean.GoCore.Ty.defined { key := "main.op" })
                    #[GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int),
                      GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int),
                      GoLean.GoCore.Expr.defaultValue (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.stringLit { bytes := #[10] }],
              GoLean.GoCore.Stmt.assign
                (GoLean.GoCore.Assignee.var "stuckPropose")
                (GoLean.GoCore.Expr.add
                  (GoLean.GoCore.Expr.var "stuckPropose")
                  (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.greaterCmp
                  (GoLean.GoCore.Expr.var "stuckPropose")
                  (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int)))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.addr
                            (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                          (GoLean.GoCore.Expr.boolLit true)],
                    GoLean.GoCore.Stmt.call
                      #[]
                      { key := "main.twin.say" }
                      #[GoLean.GoCore.Expr.var "t",
                        GoLean.GoCore.Expr.stringLit
                          { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112, 111, 115, 101, 32,
                                       115, 116, 117, 99, 107, 32, 97, 116, 32, 113, 117, 105, 101, 115, 99, 101, 110,
                                       99, 101, 10] }],
                    GoLean.GoCore.Stmt.breakStmt])
                (GoLean.GoCore.Stmt.seqn #[]),
              GoLean.GoCore.Stmt.continueStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.addr
                (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
              (GoLean.GoCore.Expr.boolLit true)],
        GoLean.GoCore.Stmt.call
          #[]
          { key := "main.twin.say" }
          #[GoLean.GoCore.Expr.var "t",
            GoLean.GoCore.Expr.stringLit
              { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101, 110, 116, 32,
                           119, 105, 116, 104, 111, 117, 116, 32, 83, 52, 10] }],
        GoLean.GoCore.Stmt.breakStmt]]) ([[("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "comp", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "comp")
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2245", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2245"]
       { key := "main.twin.complete" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.and
     (GoLean.GoCore.Expr.and
       (GoLean.GoCore.Expr.var "$c2245")
       (GoLean.GoCore.Expr.eqCmp
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.length
           (GoLean.GoCore.Expr.fieldGet
             (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
             { key := "main.twin" }
             "pending")
           (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
     (GoLean.GoCore.Expr.not
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "halt")))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "comp")
             (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "floorOK", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "floorOK")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.or
     (GoLean.GoCore.Expr.lessCmp
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "claims")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))
     (GoLean.GoCore.Expr.lessCmp
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "committed")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "floorOK")
             (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2246", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2246"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "violations"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2247", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2247"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "claims"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2248", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2248"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "committed"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2249", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call #[GoLean.GoCore.Assignee.var "$c2249"] { key := "itoa" } #[GoLean.GoCore.Expr.var "comp"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2250", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2250"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.var "floorOK"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2251", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2251"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.var "round"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add
         (GoLean.GoCore.Expr.add
           (GoLean.GoCore.Expr.add
             (GoLean.GoCore.Expr.add
               (GoLean.GoCore.Expr.add
                 (GoLean.GoCore.Expr.add
                   (GoLean.GoCore.Expr.add
                     (GoLean.GoCore.Expr.add
                       (GoLean.GoCore.Expr.add
                         (GoLean.GoCore.Expr.add
                           (GoLean.GoCore.Expr.add
                             (GoLean.GoCore.Expr.stringLit { bytes := #[101, 110, 100, 32, 118, 105, 111, 108, 61] })
                             (GoLean.GoCore.Expr.var "$c2246"))
                           (GoLean.GoCore.Expr.stringLit { bytes := #[32, 99, 108, 97, 105, 109, 115, 61] }))
                         (GoLean.GoCore.Expr.var "$c2247"))
                       (GoLean.GoCore.Expr.stringLit
                         { bytes := #[32, 99, 111, 109, 109, 105, 116, 116, 101, 100, 61] }))
                     (GoLean.GoCore.Expr.var "$c2248"))
                   (GoLean.GoCore.Expr.stringLit { bytes := #[32, 99, 111, 109, 112, 108, 101, 116, 101, 61] }))
                 (GoLean.GoCore.Expr.var "$c2249"))
               (GoLean.GoCore.Expr.stringLit { bytes := #[32, 102, 108, 111, 111, 114, 61] }))
             (GoLean.GoCore.Expr.var "$c2250"))
           (GoLean.GoCore.Expr.stringLit { bytes := #[32, 114, 111, 117, 110, 100, 115, 61] }))
         (GoLean.GoCore.Expr.var "$c2251"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2252", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2252"]
       { key := "main.twin.projection" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add
         (GoLean.GoCore.Expr.stringLit { bytes := #[102, 105, 110, 97, 108, 32] })
         (GoLean.GoCore.Expr.var "$c2252"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "t"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res1") (GoLean.GoCore.Expr.var "comp"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res2") (GoLean.GoCore.Expr.var "floorOK"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "t"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "comp"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "floorOK"])]) ([[("floorOK", GoLean.Loc.base { id := 105 }),
  ("comp", GoLean.Loc.base { id := 104 }),
  ("t", GoLean.Loc.base { id := 103 })],
 [("$res4", GoLean.Loc.base { id := 102 }),
  ("$res3", GoLean.Loc.base { id := 101 }),
  ("$res2", GoLean.Loc.base { id := 100 }),
  ("$res1", GoLean.Loc.base { id := 99 }),
  ("$res0", GoLean.Loc.base { id := 98 })]]) ([GoLean.Loc.base { id := 106 }, GoLean.Loc.base { id := 107 }, GoLean.Loc.base { id := 108 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res0")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "violations"),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res1")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "claims"),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res2")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "committed"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res3") (GoLean.GoCore.Expr.var "comp"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res4") (GoLean.GoCore.Expr.var "floorOK"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("floorOK", GoLean.Loc.base { id := 105 }),
  ("comp", GoLean.Loc.base { id := 104 }),
  ("t", GoLean.Loc.base { id := 103 })],
 [("$res4", GoLean.Loc.base { id := 102 }),
  ("$res3", GoLean.Loc.base { id := 101 }),
  ("$res2", GoLean.Loc.base { id := 100 }),
  ("$res1", GoLean.Loc.base { id := 99 }),
  ("$res0", GoLean.Loc.base { id := 98 })]]) (GoLean.Sym.Cont.frame ([]) ([]) ([]) [] (GoLean.Sym.Cont.stop) false)) false)))))))) false))) false)) false)))))) false)))))) false)) false))))

def vrSB7 : SymState :=
  (GoLean.Sym.State.mk
  [((GoLean.Loc.base { id := 15 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 57 })))),
  ((GoLean.Loc.base { id := 18 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.lockedRand" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 67 })))),
  ((GoLean.Loc.base { id := 27 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))]))),
  ((GoLean.Loc.base { id := 28 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))]))),
  ((GoLean.Loc.base { id := 57 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Commit"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 67 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.lockedRand" })) (GoLean.Sym.Value.struct ({ key := "raft.lockedRand" }) #[(("mu"), (GoLean.Sym.Value.syncData (GoLean.SyncPrim.mutex false)))]))),
  ((GoLean.Loc.base { id := 110 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 115 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[]))),
  ((GoLean.Loc.base { id := 121 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twin" })) (GoLean.Sym.Value.struct ({ key := "main.twin" }) #[(("nodes"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 1764 }), offset := 0, len := 3, cap := 4 }))),
  (("net"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8195 }), offset := 0, len := 1, cap := 1 }))),
  (("live"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8196 }), offset := 0, len := 1, cap := 1 }))),
  (("leaderOf"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 115 }) }))),
  (("byIndex"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 118 }) }))),
  (("claims"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("violations"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("pending"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 136 }), offset := 0, len := 2, cap := 4 }))),
  (("driven"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("seq"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.int))),
  (("trace"), (GoLean.Sym.Value.string ({ bytes := #[91, 99, 104, 111, 105, 99, 101, 45, 100, 114, 105, 118, 101, 110, 93, 10, 99, 97, 109, 112, 97, 105, 103,
             110, 49, 114, 49, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 53, 45, 62, 50, 32, 32, 124, 67,
             49, 47, 49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 70, 48, 47, 48, 47, 48, 32, 110, 101, 116, 61, 50, 10,
             114, 50, 32, 112, 105, 99, 107, 35, 49, 32, 116, 121, 112, 101, 53, 45, 62, 51, 32, 32, 124, 67, 49, 47,
             49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 110, 101, 116, 61, 50, 10, 114, 51,
             32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 54, 45, 62, 49] }))),
  (("halt"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 170 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1742 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 179 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 167 }) })))]))),
  ((GoLean.Loc.base { id := 179 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.struct ({ key := "raft.MemoryStorage" }) #[(("Mutex"), (GoLean.Sym.Value.syncData (GoLean.SyncPrim.mutex false))),
  (("hardState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5675 }))),
  (("snapshot"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 258 }))),
  (("ents"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 300 }), offset := 0, len := 1, cap := 1 }))),
  (("callStats"), (GoLean.Sym.Value.struct ({ key := "raft.inMemStorageCallStats" }) #[(("initialState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("firstIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 4) (GoLean.GoCore.IntKind.int))),
  (("lastIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 15) (GoLean.GoCore.IntKind.int))),
  (("entries"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.int))),
  (("snapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))]))]))),
  ((GoLean.Loc.base { id := 286 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 295 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 298 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 286 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 295 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 300 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 298 }))]))),
  ((GoLean.Loc.base { id := 349 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })) (GoLean.Sym.Value.struct ({ key := "raft.raftLog" }) #[(("storage"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 179 })))),
  (("unstable"), (GoLean.Sym.Value.struct ({ key := "raft.unstable" }) #[(("snapshot"), (GoLean.Sym.Value.nil)),
  (("entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("offset"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("snapshotInProgress"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("offsetInProgress"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 }))))])),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applying"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("maxApplyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 389 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raft" })) (GoLean.Sym.Value.struct ({ key := "raft.raft" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Vote"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("readStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("raftLog"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 349 }))),
  (("maxMsgSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("maxUncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64))),
  (("trk"), (GoLean.Sym.Value.struct ({ key := "tracker.ProgressTracker" }) #[(("Config"), (GoLean.Sym.Value.struct ({ key := "tracker.Config" }) #[(("Voters"), (GoLean.Sym.Value.array #[(GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1086 }) })),
  (GoLean.Sym.Value.map ({ base := none }))])),
  (("AutoLeave"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Learners"), (GoLean.Sym.Value.map ({ base := none }))),
  (("LearnersNext"), (GoLean.Sym.Value.map ({ base := none })))])),
  (("Progress"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1103 }) }))),
  (("Votes"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 5058 }) }))),
  (("MaxInflight"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 256) (GoLean.GoCore.IntKind.int))),
  (("MaxInflightBytes"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64)))])),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("isLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("msgs"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("msgsAfterAppend"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("leadTransferee"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("pendingConfIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("disableConfChangeValidation"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("uncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("readOnly"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5198 }))),
  (("electionElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("heartbeatElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("checkQuorum"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("preVote"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("heartbeatTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("electionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("randomizedElectionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("disableProposalForwarding"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("stepDownOnRemoval"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("tick"), (GoLean.Sym.Value.funcVal ({ key := "raft.raft.tickElection" }) [(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 }))])),
  (("step"), (GoLean.Sym.Value.funcVal ({ key := "raft.stepCandidate" }) [])),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("pendingReadIndexMessages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("traceLogger"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 1086 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[])),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[])),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[]))]))),
  ((GoLean.Loc.base { id := 1103 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1107 }))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1110 }))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1212 })))]))),
  ((GoLean.Loc.base { id := 1107 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5102 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1110 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5156 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1212 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5189 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1742 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })) (GoLean.Sym.Value.struct ({ key := "raft.RawNode" }) #[(("raft"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 }))),
  (("asyncStorageWrites"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("prevSoftSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5661 }))),
  (("prevHardSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5675 }))),
  (("stepsOnAdvance"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 5758 }), offset := 0, len := 0, cap := 4 })))]))),
  ((GoLean.Loc.base { id := 1764 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 170 })),
  (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1770 })),
  (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3369 })),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 1770 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1767 }) })))]))),
  ((GoLean.Loc.base { id := 3369 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 4941 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3378 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 3366 }) })))]))),
  ((GoLean.Loc.base { id := 5058 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))))) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))]))),
  ((GoLean.Loc.base { id := 5198 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.readOnly" })) (GoLean.Sym.Value.struct ({ key := "raft.readOnly" }) #[(("option"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("acks"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 5195 }) }))),
  (("unconfirmedReads"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("confirmedReads"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 5661 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 5666 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5669 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5672 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5675 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5666 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5669 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5672 })))]))),
  ((GoLean.Loc.base { id := 5758 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 6070 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6072 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8191 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 6) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8192 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8193 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8194 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Message" }) #[(("Type"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8191 }))),
  (("To"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8192 }))),
  (("From"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8193 }))),
  (("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8197 }))),
  (("LogTerm"), (GoLean.Sym.Value.nil)),
  (("Index"), (GoLean.Sym.Value.nil)),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Commit"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("Reject"), (GoLean.Sym.Value.nil)),
  (("RejectHint"), (GoLean.Sym.Value.nil)),
  (("Context"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Responses"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 8195 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 }))]))),
  ((GoLean.Loc.base { id := 8196 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))]))),
  ((GoLean.Loc.base { id := 8197 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8198 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8199 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8200 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8198 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8199 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 8201 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8200 }))]))),
  ((GoLean.Loc.base { id := 8202 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8203 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8204 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 8205 }) })))),
  ((GoLean.Loc.base { id := 8205 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.int)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))]))),
  ((GoLean.Loc.base { id := 8206 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 8205 }) })))),
  ((GoLean.Loc.base { id := 8207 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8195 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 8208 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8209 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8210 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8211 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8212 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8213 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8214 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8215 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8216 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 2) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8217 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8218 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8219 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 2) (GoLean.Sym.SymInt.lit 1))))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8220 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8221 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8222 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8223 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8224 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8225 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8226 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8227 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8228 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8229 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8230 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8231 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8232 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8233 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8234 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8235 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8236 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int32)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8237 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8238 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8239 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8240 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8241 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8242 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8243 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8244 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8245 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8246 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8247 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8248 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 8249 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[114, 51, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 54, 45, 62, 49] })))),
  ((GoLean.Loc.base { id := 8250 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 8251 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8252 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8253 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8254 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8255 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8256 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 170 })))),
  ((GoLean.Loc.base { id := 8257 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8258 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1742 })))),
  ((GoLean.Loc.base { id := 8259 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8260 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8261 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8262 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8263 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8264 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8265 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8266 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8267 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8268 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8269 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 27 }), offset := 0, len := 23, cap := 23 })))),
  ((GoLean.Loc.base { id := 8270 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8271 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int32)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int32)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8272 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8273 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8274 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8275 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8276 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8277 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8278 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8279 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8280 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8281 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 28 }), offset := 0, len := 23, cap := 23 })))),
  ((GoLean.Loc.base { id := 8282 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8283 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int32)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int32)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8284 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8285 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8286 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8287 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8288 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8289 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8290 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8291 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8292 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8293 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8294 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8295 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8296 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8297 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8298 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8299 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8300 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8301 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 3)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8302 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8303 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8304 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8305 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8306 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8307 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8308 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8309 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8310 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8311 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8312 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8313 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8314 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8315 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8316 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 4)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8317 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8318 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8319 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8320 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8321 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8322 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8323 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8324 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8325 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8326 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8327 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 4)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8328 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8329 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8330 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8331 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8332 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8333 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8334 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8335 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8336 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8337 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8338 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8339 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8340 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8341 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8342 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8343 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8344 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8345 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8346 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8347 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8348 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8349 }), offset := 0, len := 4, cap := 4 })))),
  ((GoLean.Loc.base { id := 8349 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 8350 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  ((GoLean.Loc.base { id := 8351 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[37, 120, 32, 114, 101, 99, 101, 105, 118, 101, 100, 32, 37, 115, 32, 102, 114, 111, 109, 32, 37, 120, 32,
             97, 116, 32, 116, 101, 114, 109, 32, 37, 100] })))),
  ((GoLean.Loc.base { id := 8352 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8349 }), offset := 0, len := 4, cap := 4 })))),
  ((GoLean.Loc.base { id := 8353 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 389 }) { key := "raft.raft" } "trk")))),
  ((GoLean.Loc.base { id := 8354 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8355 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8356 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8357 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8358 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8359 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8360 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8361 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 389 }) { key := "raft.raft" } "trk")))),
  ((GoLean.Loc.base { id := 8362 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 0) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8363 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8364 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8365 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8366 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1107 })))),
  ((GoLean.Loc.base { id := 8367 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8368 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8369 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8370 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1110 }))))]
  8371)

def vrCB7 : SymConfig :=
  (GoLean.Sym.Config.exec (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.fieldGet
        (GoLean.GoCore.Expr.deref
          (GoLean.GoCore.Expr.var "pr")
          (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))
        { key := "tracker.Progress" }
        "IsLearner")
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.seqn
      #[GoLean.GoCore.Stmt.initialization { id := "v", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.initialization { id := "voted", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.mapLookup
          (GoLean.GoCore.Assignee.var "v")
          (GoLean.GoCore.Assignee.var "voted")
          (GoLean.GoCore.Expr.fieldGet
            (GoLean.GoCore.Expr.deref
              (GoLean.GoCore.Expr.var "p")
              (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
            { key := "tracker.ProgressTracker" }
            "Votes")
          (GoLean.GoCore.Expr.var "id")
          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
          (GoLean.GoCore.Ty.bool)],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "voted"))
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "v")
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "granted")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "granted")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "rejected")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "rejected")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])]) ([[("pr", GoLean.Loc.base { id := 8370 }), ("id", GoLean.Loc.base { id := 8369 })],
 [],
 [("$res2", GoLean.Loc.base { id := 8364 }),
  ("rejected", GoLean.Loc.base { id := 8363 }),
  ("granted", GoLean.Loc.base { id := 8362 }),
  ("p", GoLean.Loc.base { id := 8361 })]]) (GoLean.Sym.Cont.mapIterK (some "id") (some "pr") (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.fieldGet
        (GoLean.GoCore.Expr.deref
          (GoLean.GoCore.Expr.var "pr")
          (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))
        { key := "tracker.Progress" }
        "IsLearner")
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.seqn
      #[GoLean.GoCore.Stmt.initialization { id := "v", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.initialization { id := "voted", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.mapLookup
          (GoLean.GoCore.Assignee.var "v")
          (GoLean.GoCore.Assignee.var "voted")
          (GoLean.GoCore.Expr.fieldGet
            (GoLean.GoCore.Expr.deref
              (GoLean.GoCore.Expr.var "p")
              (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
            { key := "tracker.ProgressTracker" }
            "Votes")
          (GoLean.GoCore.Expr.var "id")
          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
          (GoLean.GoCore.Ty.bool)],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "voted"))
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "v")
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "granted")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "granted")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "rejected")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "rejected")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])]) (some (GoLean.Loc.base { id := 1103 })) #[(GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)),
  (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))] #[(GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)),
  (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)),
  (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64))] ([[],
 [("$res2", GoLean.Loc.base { id := 8364 }),
  ("rejected", GoLean.Loc.base { id := 8363 }),
  ("granted", GoLean.Loc.base { id := 8362 }),
  ("p", GoLean.Loc.base { id := 8361 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "result", typ := GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" } },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "result"]
       { key := "quorum.JointConfig.VoteResult" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.fieldGet
             (GoLean.GoCore.Expr.deref
               (GoLean.GoCore.Expr.var "p")
               (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
             { key := "tracker.ProgressTracker" }
             "Config")
           { key := "tracker.Config" }
           "Voters",
         GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref
             (GoLean.GoCore.Expr.var "p")
             (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
           { key := "tracker.ProgressTracker" }
           "Votes"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "granted") (GoLean.GoCore.Expr.var "granted"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "rejected") (GoLean.GoCore.Expr.var "rejected"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res2") (GoLean.GoCore.Expr.var "result"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[],
 [("$res2", GoLean.Loc.base { id := 8364 }),
  ("rejected", GoLean.Loc.base { id := 8363 }),
  ("granted", GoLean.Loc.base { id := 8362 }),
  ("p", GoLean.Loc.base { id := 8361 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1353"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1354"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1355"])]) ([[("$c1355", GoLean.Loc.base { id := 8360 }),
  ("$c1354", GoLean.Loc.base { id := 8359 }),
  ("$c1353", GoLean.Loc.base { id := 8358 })],
 [("result", GoLean.Loc.base { id := 8347 }),
  ("rejected", GoLean.Loc.base { id := 8346 }),
  ("granted", GoLean.Loc.base { id := 8345 }),
  ("v", GoLean.Loc.base { id := 8344 }),
  ("t", GoLean.Loc.base { id := 8343 }),
  ("id", GoLean.Loc.base { id := 8342 }),
  ("r", GoLean.Loc.base { id := 8341 })]]) ([GoLean.Loc.base { id := 8362 }, GoLean.Loc.base { id := 8363 }, GoLean.Loc.base { id := 8364 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "granted") (GoLean.GoCore.Expr.var "$c1353"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "rejected") (GoLean.GoCore.Expr.var "$c1354"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "result") (GoLean.GoCore.Expr.var "$c1355"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("$c1355", GoLean.Loc.base { id := 8360 }),
  ("$c1354", GoLean.Loc.base { id := 8359 }),
  ("$c1353", GoLean.Loc.base { id := 8358 })],
 [("result", GoLean.Loc.base { id := 8347 }),
  ("rejected", GoLean.Loc.base { id := 8346 }),
  ("granted", GoLean.Loc.base { id := 8345 }),
  ("v", GoLean.Loc.base { id := 8344 }),
  ("t", GoLean.Loc.base { id := 8343 }),
  ("id", GoLean.Loc.base { id := 8342 }),
  ("r", GoLean.Loc.base { id := 8341 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "gr"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "rj"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "res"])]) ([[("res", GoLean.Loc.base { id := 8340 }),
  ("rj", GoLean.Loc.base { id := 8339 }),
  ("gr", GoLean.Loc.base { id := 8338 }),
  ("$c1575", GoLean.Loc.base { id := 8335 }),
  ("$c1574", GoLean.Loc.base { id := 8332 }),
  ("$c1573", GoLean.Loc.base { id := 8329 })],
 [],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) ([GoLean.Loc.base { id := 8345 }, GoLean.Loc.base { id := 8346 }, GoLean.Loc.base { id := 8347 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "$c1576", typ := GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" } },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c1576"]
       { key := "raftpb.Message.GetType" }
       #[GoLean.GoCore.Expr.var "m"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "$c1577", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }) },
     GoLean.GoCore.Stmt.makeSlice
       (GoLean.GoCore.Assignee.var "$c1577")
       (GoLean.GoCore.Ty.interface { key := "any" })
       (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))
       (some (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
         (GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "r") (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
           { key := "raft.raft" }
           "id")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.var "gr")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })
         (GoLean.GoCore.Expr.var "$c1576")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.var "rj"))],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "raft.Logger.Infof" }
   #[GoLean.GoCore.Expr.fieldGet
       (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "r") (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
       { key := "raft.raft" }
       "logger",
     GoLean.GoCore.Expr.stringLit
       { bytes := #[37, 120, 32, 104, 97, 115, 32, 114, 101, 99, 101, 105, 118, 101, 100, 32, 37, 100, 32, 37, 115, 32,
                    118, 111, 116, 101, 115, 32, 97, 110, 100, 32, 37, 100, 32, 118, 111, 116, 101, 32, 114, 101, 106,
                    101, 99, 116, 105, 111, 110, 115] },
     GoLean.GoCore.Expr.var "$c1577"],
 GoLean.GoCore.Stmt.breakable
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$sw1578", typ := GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" } },
           GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$sw1578") (GoLean.GoCore.Expr.var "res")],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$swi1579", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
           GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))],
       GoLean.GoCore.Stmt.block
         #[]
         #[GoLean.GoCore.Stmt.ifThenElse
             (GoLean.GoCore.Expr.eqCmp
               (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })
               (GoLean.GoCore.Expr.var "$sw1578")
               (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.uint8)))
             (GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.var "$swi1579")
                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))])
             (GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.ifThenElse
                   (GoLean.GoCore.Expr.eqCmp
                     (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })
                     (GoLean.GoCore.Expr.var "$sw1578")
                     (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint8)))
                   (GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.assign
                         (GoLean.GoCore.Assignee.var "$swi1579")
                         (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))])
                   (GoLean.GoCore.Stmt.seqn #[])])],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$swf1579", typ := GoLean.GoCore.Ty.bool },
           GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.or
           (GoLean.GoCore.Expr.var "$swf1579")
           (GoLean.GoCore.Expr.eqCmp
             (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
             (GoLean.GoCore.Expr.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
             GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.ifThenElse
                   (GoLean.GoCore.Expr.eqCmp
                     (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
                     (GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "r")
                         (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                       { key := "raft.raft" }
                       "state")
                     (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.uint64)))
                   (GoLean.GoCore.Stmt.block
                     #[]
                     #[GoLean.GoCore.Stmt.call
                         #[]
                         { key := "raft.raft.campaign" }
                         #[GoLean.GoCore.Expr.var "r",
                           GoLean.GoCore.Expr.stringLit
                             { bytes := #[67, 97, 109, 112, 97, 105, 103, 110, 69, 108, 101, 99, 116, 105, 111,
                                          110] }]])
                   (GoLean.GoCore.Stmt.block
                     #[]
                     #[GoLean.GoCore.Stmt.call #[] { key := "raft.raft.becomeLeader" } #[GoLean.GoCore.Expr.var "r"],
                       GoLean.GoCore.Stmt.call #[] { key := "raft.raft.bcastAppend" } #[GoLean.GoCore.Expr.var "r"]])]])
         (GoLean.GoCore.Stmt.seqn #[]),
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.or
           (GoLean.GoCore.Expr.var "$swf1579")
           (GoLean.GoCore.Expr.eqCmp
             (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
             (GoLean.GoCore.Expr.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
             GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.call
                   #[]
                   { key := "raft.raft.becomeFollower" }
                   #[GoLean.GoCore.Expr.var "r",
                     GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "r")
                         (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                       { key := "raft.raft" }
                       "Term",
                     GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64)]]])
         (GoLean.GoCore.Stmt.seqn #[])])]) ([[("res", GoLean.Loc.base { id := 8340 }),
  ("rj", GoLean.Loc.base { id := 8339 }),
  ("gr", GoLean.Loc.base { id := 8338 }),
  ("$c1575", GoLean.Loc.base { id := 8335 }),
  ("$c1574", GoLean.Loc.base { id := 8332 }),
  ("$c1573", GoLean.Loc.base { id := 8329 })],
 [],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.or
     (GoLean.GoCore.Expr.var "$swf1582")
     (GoLean.GoCore.Expr.eqCmp
       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
       (GoLean.GoCore.Expr.var "$swi1582")
       (GoLean.GoCore.Expr.intLit 5 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1582") (GoLean.GoCore.Expr.boolLit false)],
       GoLean.GoCore.Stmt.block
         #[]
         #[GoLean.GoCore.Stmt.seqn
             #[GoLean.GoCore.Stmt.initialization
                 { id := "$c1580", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
               GoLean.GoCore.Stmt.call
                 #[GoLean.GoCore.Assignee.var "$c1580"]
                 { key := "raftpb.Message.GetFrom" }
                 #[GoLean.GoCore.Expr.var "m"]],
           GoLean.GoCore.Stmt.seqn
             #[GoLean.GoCore.Stmt.initialization
                 { id := "$c1581", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }) },
               GoLean.GoCore.Stmt.makeSlice
                 (GoLean.GoCore.Assignee.var "$c1581")
                 (GoLean.GoCore.Ty.interface { key := "any" })
                 (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))
                 (some (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "id")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "Term")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "state")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.var "$c1580"))],
           GoLean.GoCore.Stmt.call
             #[]
             { key := "raft.Logger.Debugf" }
             #[GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "r")
                   (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                 { key := "raft.raft" }
                 "logger",
               GoLean.GoCore.Expr.stringLit
                 { bytes := #[37, 120, 32, 91, 116, 101, 114, 109, 32, 37, 100, 32, 115, 116, 97, 116, 101, 32, 37, 118,
                              93, 32, 105, 103, 110, 111, 114, 101, 100, 32, 77, 115, 103, 84, 105, 109, 101, 111, 117,
                              116, 78, 111, 119, 32, 102, 114, 111, 109, 32, 37, 120] },
               GoLean.GoCore.Expr.var "$c1581"]]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.breakableK (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.nil none),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "err"])]) ([[("err", GoLean.Loc.base { id := 8318 })],
 [],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) ([GoLean.Loc.base { id := 8321 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.neqCmp
     (GoLean.GoCore.Ty.interface { key := "error" })
     (GoLean.GoCore.Expr.var "err")
     (GoLean.GoCore.Expr.nil none))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "err"),
           GoLean.GoCore.Stmt.returnStmt]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("err", GoLean.Loc.base { id := 8318 })],
 [],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.breakableK (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.nil none),
     GoLean.GoCore.Stmt.returnStmt]]) ([[],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1790"])]) ([[("$c1790", GoLean.Loc.base { id := 8295 }),
  ("$c1789", GoLean.Loc.base { id := 8291 }),
  ("$c1787", GoLean.Loc.base { id := 8284 }),
  ("$c1784", GoLean.Loc.base { id := 8276 }),
  ("$c1783", GoLean.Loc.base { id := 8273 }),
  ("$c1782", GoLean.Loc.base { id := 8272 }),
  ("$c1779", GoLean.Loc.base { id := 8264 }),
  ("$c1778", GoLean.Loc.base { id := 8261 })],
 [("$res0", GoLean.Loc.base { id := 8260 }),
  ("m", GoLean.Loc.base { id := 8259 }),
  ("rn", GoLean.Loc.base { id := 8258 })]]) ([GoLean.Loc.base { id := 8298 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "$c1790"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("$c1790", GoLean.Loc.base { id := 8295 }),
  ("$c1789", GoLean.Loc.base { id := 8291 }),
  ("$c1787", GoLean.Loc.base { id := 8284 }),
  ("$c1784", GoLean.Loc.base { id := 8276 }),
  ("$c1783", GoLean.Loc.base { id := 8273 }),
  ("$c1782", GoLean.Loc.base { id := 8272 }),
  ("$c1779", GoLean.Loc.base { id := 8264 }),
  ("$c1778", GoLean.Loc.base { id := 8261 })],
 [("$res0", GoLean.Loc.base { id := 8260 }),
  ("m", GoLean.Loc.base { id := 8259 }),
  ("rn", GoLean.Loc.base { id := 8258 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "err"])]) ([[("err", GoLean.Loc.base { id := 8257 })],
 [("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) ([GoLean.Loc.base { id := 8260 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.neqCmp
     (GoLean.GoCore.Ty.interface { key := "error" })
     (GoLean.GoCore.Expr.var "err")
     (GoLean.GoCore.Expr.nil none))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.stringLit { bytes := #[32, 115, 116, 101, 112, 101, 114, 114] }]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("err", GoLean.Loc.base { id := 8257 })],
 [("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$cr0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$cr0"]
       { key := "main.twin.harvest" }
       #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "to"]]]) ([[("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) (GoLean.Sym.Cont.frame ([]) ([[("$c2241", GoLean.Loc.base { id := 8243 }),
  ("$c2240", GoLean.Loc.base { id := 8240 }),
  ("$c2239", GoLean.Loc.base { id := 8232 }),
  ("$c2238", GoLean.Loc.base { id := 8229 }),
  ("$c2237", GoLean.Loc.base { id := 8223 }),
  ("$c2236", GoLean.Loc.base { id := 8215 }),
  ("m", GoLean.Loc.base { id := 8214 }),
  ("picked", GoLean.Loc.base { id := 8212 })],
 [("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) ([]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2242", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2242"]
       { key := "main.twin.projection" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add (GoLean.GoCore.Expr.stringLit { bytes := #[32] }) (GoLean.GoCore.Expr.var "$c2242"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "stuckPropose")
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.continueStmt]) ([[("$c2241", GoLean.Loc.base { id := 8243 }),
  ("$c2240", GoLean.Loc.base { id := 8240 }),
  ("$c2239", GoLean.Loc.base { id := 8232 }),
  ("$c2238", GoLean.Loc.base { id := 8229 }),
  ("$c2237", GoLean.Loc.base { id := 8223 }),
  ("$c2236", GoLean.Loc.base { id := 8215 }),
  ("m", GoLean.Loc.base { id := 8214 }),
  ("picked", GoLean.Loc.base { id := 8212 })],
 [("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2243", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2243"]
       { key := "main.twin.complete" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.and
     (GoLean.GoCore.Expr.var "$c2243")
     (GoLean.GoCore.Expr.eqCmp
       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
       (GoLean.GoCore.Expr.length
         (GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "pending")
         (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.breakStmt])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.greaterCmp
     (GoLean.GoCore.Expr.length
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "pending")
       (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$c2244", typ := GoLean.GoCore.Ty.string },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2244"]
             { key := "itoa" }
             #[GoLean.GoCore.Expr.add
                 (GoLean.GoCore.Expr.var "round")
                 (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.add
             (GoLean.GoCore.Expr.add
               (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
               (GoLean.GoCore.Expr.var "$c2244"))
             (GoLean.GoCore.Expr.stringLit { bytes := #[32] })],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.step" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.structLit
             (GoLean.GoCore.Ty.defined { key := "main.op" })
             #[GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int),
               GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int),
               GoLean.GoCore.Expr.defaultValue (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.stringLit { bytes := #[10] }],
       GoLean.GoCore.Stmt.assign
         (GoLean.GoCore.Assignee.var "stuckPropose")
         (GoLean.GoCore.Expr.add
           (GoLean.GoCore.Expr.var "stuckPropose")
           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.greaterCmp
           (GoLean.GoCore.Expr.var "stuckPropose")
           (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int)))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.addr
                     (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                   (GoLean.GoCore.Expr.boolLit true)],
             GoLean.GoCore.Stmt.call
               #[]
               { key := "main.twin.say" }
               #[GoLean.GoCore.Expr.var "t",
                 GoLean.GoCore.Expr.stringLit
                   { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112, 111, 115, 101, 32, 115,
                                116, 117, 99, 107, 32, 97, 116, 32, 113, 117, 105, 101, 115, 99, 101, 110, 99, 101,
                                10] }],
             GoLean.GoCore.Stmt.breakStmt])
         (GoLean.GoCore.Stmt.seqn #[]),
       GoLean.GoCore.Stmt.continueStmt])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
       (GoLean.GoCore.Expr.boolLit true)],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.stringLit
       { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101, 110, 116, 32, 119, 105,
                    116, 104, 111, 117, 116, 32, 83, 52, 10] }],
 GoLean.GoCore.Stmt.breakStmt]) ([[("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.loop (GoLean.GoCore.Expr.boolLit true) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "$forFirst")
      (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$forFirst") (GoLean.GoCore.Expr.boolLit false))
      (GoLean.GoCore.Stmt.assign
        (GoLean.GoCore.Assignee.var "round")
        (GoLean.GoCore.Expr.add
          (GoLean.GoCore.Expr.var "round")
          (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
    GoLean.GoCore.Stmt.seqn #[],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.lessCmp
        (GoLean.GoCore.Expr.var "round")
        (GoLean.GoCore.Expr.intLit 400 (GoLean.GoCore.IntKind.int)))
      (GoLean.GoCore.Stmt.seqn #[])
      (GoLean.GoCore.Stmt.breakStmt),
    GoLean.GoCore.Stmt.block
      #[]
      #[GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization
              { id := "$c2235",
                typ := GoLean.GoCore.Ty.map
                         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                         (GoLean.GoCore.Ty.bool) },
            GoLean.GoCore.Stmt.makeMap
              (GoLean.GoCore.Assignee.var "$c2235")
              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
              (GoLean.GoCore.Ty.bool)
              none],
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization
              { id := "live",
                typ := GoLean.GoCore.Ty.map
                         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                         (GoLean.GoCore.Ty.bool) },
            GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "live") (GoLean.GoCore.Expr.var "$c2235")],
        GoLean.GoCore.Stmt.block
          #[]
          #[GoLean.GoCore.Stmt.initialization
              { id := "$rcoll",
                typ := GoLean.GoCore.Ty.slice
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rcoll")
              (GoLean.GoCore.Expr.fieldGet
                (GoLean.GoCore.Expr.deref
                  (GoLean.GoCore.Expr.var "t")
                  (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                { key := "main.twin" }
                "net"),
            GoLean.GoCore.Stmt.initialization
              { id := "$rlen", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rlen")
              (GoLean.GoCore.Expr.length (GoLean.GoCore.Expr.var "$rcoll") none),
            GoLean.GoCore.Stmt.initialization
              { id := "$ridx", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$ridx")
              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)),
            GoLean.GoCore.Stmt.initialization { id := "$rfirst", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$rfirst") (GoLean.GoCore.Expr.boolLit true),
            GoLean.GoCore.Stmt.while
              (GoLean.GoCore.Expr.boolLit true)
              (GoLean.GoCore.Stmt.block
                #[]
                #[GoLean.GoCore.Stmt.ifThenElse
                    (GoLean.GoCore.Expr.var "$rfirst")
                    (GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "$rfirst")
                      (GoLean.GoCore.Expr.boolLit false))
                    (GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "$ridx")
                      (GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "$ridx")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
                  GoLean.GoCore.Stmt.ifThenElse
                    (GoLean.GoCore.Expr.atLeastCmp (GoLean.GoCore.Expr.var "$ridx") (GoLean.GoCore.Expr.var "$rlen"))
                    (GoLean.GoCore.Stmt.breakStmt)
                    (GoLean.GoCore.Stmt.seqn #[]),
                  GoLean.GoCore.Stmt.initialization
                    { id := "j", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                  GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "j") (GoLean.GoCore.Expr.var "$ridx"),
                  GoLean.GoCore.Stmt.block
                    #[]
                    #[GoLean.GoCore.Stmt.ifThenElse
                        (GoLean.GoCore.Expr.indexGet
                          (GoLean.GoCore.Expr.fieldGet
                            (GoLean.GoCore.Expr.deref
                              (GoLean.GoCore.Expr.var "t")
                              (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                            { key := "main.twin" }
                            "live")
                          (GoLean.GoCore.Expr.var "j"))
                        (GoLean.GoCore.Stmt.block
                          #[]
                          #[GoLean.GoCore.Stmt.mapAssign
                              (GoLean.GoCore.Expr.var "live")
                              (GoLean.GoCore.Expr.var "j")
                              (GoLean.GoCore.Expr.boolLit true)
                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                              (GoLean.GoCore.Ty.bool)])
                        (GoLean.GoCore.Stmt.seqn #[])]])],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.length
              (GoLean.GoCore.Expr.var "live")
              (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))))
            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "picked", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "picked")
                    (GoLean.GoCore.Expr.intLit (-1) (GoLean.GoCore.IntKind.int))],
              GoLean.GoCore.Stmt.mapRange
                (some "j")
                none
                (GoLean.GoCore.Expr.var "live")
                (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                (GoLean.GoCore.Ty.bool)
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "picked") (GoLean.GoCore.Expr.var "j")],
                    GoLean.GoCore.Stmt.breakStmt]),
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "m",
                      typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "m")
                    (GoLean.GoCore.Expr.indexGet
                      (GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "t")
                          (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                        { key := "main.twin" }
                        "net")
                      (GoLean.GoCore.Expr.var "picked"))],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2236", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2236"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "round")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2237", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2237"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.var "picked"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2238", typ := GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" } },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2238"]
                    { key := "raftpb.Message.GetType" }
                    #[GoLean.GoCore.Expr.var "m"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2239", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2239"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.convert
                        (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                        (GoLean.GoCore.Expr.var "$c2238")]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2240", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2240"]
                    { key := "raftpb.Message.GetTo" }
                    #[GoLean.GoCore.Expr.var "m"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2241", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2241"]
                    { key := "utoa" }
                    #[GoLean.GoCore.Expr.var "$c2240"]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.add
                          (GoLean.GoCore.Expr.add
                            (GoLean.GoCore.Expr.add
                              (GoLean.GoCore.Expr.add
                                (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
                                (GoLean.GoCore.Expr.var "$c2236"))
                              (GoLean.GoCore.Expr.stringLit { bytes := #[32, 112, 105, 99, 107, 35] }))
                            (GoLean.GoCore.Expr.var "$c2237"))
                          (GoLean.GoCore.Expr.stringLit { bytes := #[32, 116, 121, 112, 101] }))
                        (GoLean.GoCore.Expr.var "$c2239"))
                      (GoLean.GoCore.Expr.stringLit { bytes := #[45, 62] }))
                    (GoLean.GoCore.Expr.var "$c2241")],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.deliverIdx" }
                #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "picked"],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2242", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2242"]
                    { key := "main.twin.projection" }
                    #[GoLean.GoCore.Expr.var "t"]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.stringLit { bytes := #[32] })
                      (GoLean.GoCore.Expr.var "$c2242"))
                    (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "stuckPropose")
                    (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
              GoLean.GoCore.Stmt.continueStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "$c2243", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c2243"]
              { key := "main.twin.complete" }
              #[GoLean.GoCore.Expr.var "t"]],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.and
            (GoLean.GoCore.Expr.var "$c2243")
            (GoLean.GoCore.Expr.eqCmp
              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
              (GoLean.GoCore.Expr.length
                (GoLean.GoCore.Expr.fieldGet
                  (GoLean.GoCore.Expr.deref
                    (GoLean.GoCore.Expr.var "t")
                    (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                  { key := "main.twin" }
                  "pending")
                (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
          (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.breakStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.length
              (GoLean.GoCore.Expr.fieldGet
                (GoLean.GoCore.Expr.deref
                  (GoLean.GoCore.Expr.var "t")
                  (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                { key := "main.twin" }
                "pending")
              (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2244", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2244"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "round")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
                      (GoLean.GoCore.Expr.var "$c2244"))
                    (GoLean.GoCore.Expr.stringLit { bytes := #[32] })],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.step" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.structLit
                    (GoLean.GoCore.Ty.defined { key := "main.op" })
                    #[GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int),
                      GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int),
                      GoLean.GoCore.Expr.defaultValue (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.stringLit { bytes := #[10] }],
              GoLean.GoCore.Stmt.assign
                (GoLean.GoCore.Assignee.var "stuckPropose")
                (GoLean.GoCore.Expr.add
                  (GoLean.GoCore.Expr.var "stuckPropose")
                  (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.greaterCmp
                  (GoLean.GoCore.Expr.var "stuckPropose")
                  (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int)))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.addr
                            (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                          (GoLean.GoCore.Expr.boolLit true)],
                    GoLean.GoCore.Stmt.call
                      #[]
                      { key := "main.twin.say" }
                      #[GoLean.GoCore.Expr.var "t",
                        GoLean.GoCore.Expr.stringLit
                          { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112, 111, 115, 101, 32,
                                       115, 116, 117, 99, 107, 32, 97, 116, 32, 113, 117, 105, 101, 115, 99, 101, 110,
                                       99, 101, 10] }],
                    GoLean.GoCore.Stmt.breakStmt])
                (GoLean.GoCore.Stmt.seqn #[]),
              GoLean.GoCore.Stmt.continueStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.addr
                (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
              (GoLean.GoCore.Expr.boolLit true)],
        GoLean.GoCore.Stmt.call
          #[]
          { key := "main.twin.say" }
          #[GoLean.GoCore.Expr.var "t",
            GoLean.GoCore.Expr.stringLit
              { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101, 110, 116, 32,
                           119, 105, 116, 104, 111, 117, 116, 32, 83, 52, 10] }],
        GoLean.GoCore.Stmt.breakStmt]]) ([[("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "comp", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "comp")
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2245", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2245"]
       { key := "main.twin.complete" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.and
     (GoLean.GoCore.Expr.and
       (GoLean.GoCore.Expr.var "$c2245")
       (GoLean.GoCore.Expr.eqCmp
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.length
           (GoLean.GoCore.Expr.fieldGet
             (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
             { key := "main.twin" }
             "pending")
           (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
     (GoLean.GoCore.Expr.not
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "halt")))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "comp")
             (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "floorOK", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "floorOK")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.or
     (GoLean.GoCore.Expr.lessCmp
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "claims")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))
     (GoLean.GoCore.Expr.lessCmp
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "committed")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "floorOK")
             (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2246", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2246"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "violations"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2247", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2247"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "claims"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2248", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2248"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "committed"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2249", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call #[GoLean.GoCore.Assignee.var "$c2249"] { key := "itoa" } #[GoLean.GoCore.Expr.var "comp"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2250", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2250"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.var "floorOK"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2251", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2251"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.var "round"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add
         (GoLean.GoCore.Expr.add
           (GoLean.GoCore.Expr.add
             (GoLean.GoCore.Expr.add
               (GoLean.GoCore.Expr.add
                 (GoLean.GoCore.Expr.add
                   (GoLean.GoCore.Expr.add
                     (GoLean.GoCore.Expr.add
                       (GoLean.GoCore.Expr.add
                         (GoLean.GoCore.Expr.add
                           (GoLean.GoCore.Expr.add
                             (GoLean.GoCore.Expr.stringLit { bytes := #[101, 110, 100, 32, 118, 105, 111, 108, 61] })
                             (GoLean.GoCore.Expr.var "$c2246"))
                           (GoLean.GoCore.Expr.stringLit { bytes := #[32, 99, 108, 97, 105, 109, 115, 61] }))
                         (GoLean.GoCore.Expr.var "$c2247"))
                       (GoLean.GoCore.Expr.stringLit
                         { bytes := #[32, 99, 111, 109, 109, 105, 116, 116, 101, 100, 61] }))
                     (GoLean.GoCore.Expr.var "$c2248"))
                   (GoLean.GoCore.Expr.stringLit { bytes := #[32, 99, 111, 109, 112, 108, 101, 116, 101, 61] }))
                 (GoLean.GoCore.Expr.var "$c2249"))
               (GoLean.GoCore.Expr.stringLit { bytes := #[32, 102, 108, 111, 111, 114, 61] }))
             (GoLean.GoCore.Expr.var "$c2250"))
           (GoLean.GoCore.Expr.stringLit { bytes := #[32, 114, 111, 117, 110, 100, 115, 61] }))
         (GoLean.GoCore.Expr.var "$c2251"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2252", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2252"]
       { key := "main.twin.projection" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add
         (GoLean.GoCore.Expr.stringLit { bytes := #[102, 105, 110, 97, 108, 32] })
         (GoLean.GoCore.Expr.var "$c2252"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "t"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res1") (GoLean.GoCore.Expr.var "comp"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res2") (GoLean.GoCore.Expr.var "floorOK"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "t"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "comp"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "floorOK"])]) ([[("floorOK", GoLean.Loc.base { id := 105 }),
  ("comp", GoLean.Loc.base { id := 104 }),
  ("t", GoLean.Loc.base { id := 103 })],
 [("$res4", GoLean.Loc.base { id := 102 }),
  ("$res3", GoLean.Loc.base { id := 101 }),
  ("$res2", GoLean.Loc.base { id := 100 }),
  ("$res1", GoLean.Loc.base { id := 99 }),
  ("$res0", GoLean.Loc.base { id := 98 })]]) ([GoLean.Loc.base { id := 106 }, GoLean.Loc.base { id := 107 }, GoLean.Loc.base { id := 108 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res0")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "violations"),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res1")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "claims"),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res2")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "committed"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res3") (GoLean.GoCore.Expr.var "comp"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res4") (GoLean.GoCore.Expr.var "floorOK"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("floorOK", GoLean.Loc.base { id := 105 }),
  ("comp", GoLean.Loc.base { id := 104 }),
  ("t", GoLean.Loc.base { id := 103 })],
 [("$res4", GoLean.Loc.base { id := 102 }),
  ("$res3", GoLean.Loc.base { id := 101 }),
  ("$res2", GoLean.Loc.base { id := 100 }),
  ("$res1", GoLean.Loc.base { id := 99 }),
  ("$res0", GoLean.Loc.base { id := 98 })]]) (GoLean.Sym.Cont.frame ([]) ([]) ([]) [] (GoLean.Sym.Cont.stop) false)) false)))))))) false))) false)) false)))))) false)))))) false)) false))))

def vrSB8 : SymState :=
  (GoLean.Sym.State.mk
  [((GoLean.Loc.base { id := 15 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 57 })))),
  ((GoLean.Loc.base { id := 18 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.lockedRand" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 67 })))),
  ((GoLean.Loc.base { id := 27 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))]))),
  ((GoLean.Loc.base { id := 28 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))]))),
  ((GoLean.Loc.base { id := 57 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Commit"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 67 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.lockedRand" })) (GoLean.Sym.Value.struct ({ key := "raft.lockedRand" }) #[(("mu"), (GoLean.Sym.Value.syncData (GoLean.SyncPrim.mutex false)))]))),
  ((GoLean.Loc.base { id := 110 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 115 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[]))),
  ((GoLean.Loc.base { id := 121 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twin" })) (GoLean.Sym.Value.struct ({ key := "main.twin" }) #[(("nodes"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 1764 }), offset := 0, len := 3, cap := 4 }))),
  (("net"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8195 }), offset := 0, len := 1, cap := 1 }))),
  (("live"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8196 }), offset := 0, len := 1, cap := 1 }))),
  (("leaderOf"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 115 }) }))),
  (("byIndex"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 118 }) }))),
  (("claims"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("violations"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("pending"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 136 }), offset := 0, len := 2, cap := 4 }))),
  (("driven"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("seq"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.int))),
  (("trace"), (GoLean.Sym.Value.string ({ bytes := #[91, 99, 104, 111, 105, 99, 101, 45, 100, 114, 105, 118, 101, 110, 93, 10, 99, 97, 109, 112, 97, 105, 103,
             110, 49, 114, 49, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 53, 45, 62, 50, 32, 32, 124, 67,
             49, 47, 49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 70, 48, 47, 48, 47, 48, 32, 110, 101, 116, 61, 50, 10,
             114, 50, 32, 112, 105, 99, 107, 35, 49, 32, 116, 121, 112, 101, 53, 45, 62, 51, 32, 32, 124, 67, 49, 47,
             49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 110, 101, 116, 61, 50, 10, 114, 51,
             32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 54, 45, 62, 49] }))),
  (("halt"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 170 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1742 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 179 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 167 }) })))]))),
  ((GoLean.Loc.base { id := 179 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.struct ({ key := "raft.MemoryStorage" }) #[(("Mutex"), (GoLean.Sym.Value.syncData (GoLean.SyncPrim.mutex false))),
  (("hardState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5675 }))),
  (("snapshot"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 258 }))),
  (("ents"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 300 }), offset := 0, len := 1, cap := 1 }))),
  (("callStats"), (GoLean.Sym.Value.struct ({ key := "raft.inMemStorageCallStats" }) #[(("initialState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("firstIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 4) (GoLean.GoCore.IntKind.int))),
  (("lastIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 15) (GoLean.GoCore.IntKind.int))),
  (("entries"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.int))),
  (("snapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))]))]))),
  ((GoLean.Loc.base { id := 286 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 295 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 298 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 286 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 295 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 300 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 298 }))]))),
  ((GoLean.Loc.base { id := 349 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })) (GoLean.Sym.Value.struct ({ key := "raft.raftLog" }) #[(("storage"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 179 })))),
  (("unstable"), (GoLean.Sym.Value.struct ({ key := "raft.unstable" }) #[(("snapshot"), (GoLean.Sym.Value.nil)),
  (("entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("offset"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("snapshotInProgress"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("offsetInProgress"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 }))))])),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applying"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("maxApplyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 389 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raft" })) (GoLean.Sym.Value.struct ({ key := "raft.raft" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Vote"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("readStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("raftLog"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 349 }))),
  (("maxMsgSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("maxUncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64))),
  (("trk"), (GoLean.Sym.Value.struct ({ key := "tracker.ProgressTracker" }) #[(("Config"), (GoLean.Sym.Value.struct ({ key := "tracker.Config" }) #[(("Voters"), (GoLean.Sym.Value.array #[(GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1086 }) })),
  (GoLean.Sym.Value.map ({ base := none }))])),
  (("AutoLeave"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Learners"), (GoLean.Sym.Value.map ({ base := none }))),
  (("LearnersNext"), (GoLean.Sym.Value.map ({ base := none })))])),
  (("Progress"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1103 }) }))),
  (("Votes"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 5058 }) }))),
  (("MaxInflight"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 256) (GoLean.GoCore.IntKind.int))),
  (("MaxInflightBytes"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64)))])),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("isLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("msgs"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("msgsAfterAppend"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("leadTransferee"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("pendingConfIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("disableConfChangeValidation"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("uncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("readOnly"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5198 }))),
  (("electionElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("heartbeatElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("checkQuorum"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("preVote"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("heartbeatTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("electionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("randomizedElectionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("disableProposalForwarding"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("stepDownOnRemoval"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("tick"), (GoLean.Sym.Value.funcVal ({ key := "raft.raft.tickElection" }) [(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 }))])),
  (("step"), (GoLean.Sym.Value.funcVal ({ key := "raft.stepCandidate" }) [])),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("pendingReadIndexMessages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("traceLogger"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 1086 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[])),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[])),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[]))]))),
  ((GoLean.Loc.base { id := 1103 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1107 }))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1110 }))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1212 })))]))),
  ((GoLean.Loc.base { id := 1107 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5102 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1110 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5156 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1212 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5189 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1742 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })) (GoLean.Sym.Value.struct ({ key := "raft.RawNode" }) #[(("raft"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 }))),
  (("asyncStorageWrites"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("prevSoftSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5661 }))),
  (("prevHardSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5675 }))),
  (("stepsOnAdvance"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 5758 }), offset := 0, len := 0, cap := 4 })))]))),
  ((GoLean.Loc.base { id := 1764 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 170 })),
  (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1770 })),
  (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3369 })),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 1770 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1767 }) })))]))),
  ((GoLean.Loc.base { id := 3369 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 4941 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3378 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 3366 }) })))]))),
  ((GoLean.Loc.base { id := 5058 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))))) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))]))),
  ((GoLean.Loc.base { id := 5198 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.readOnly" })) (GoLean.Sym.Value.struct ({ key := "raft.readOnly" }) #[(("option"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("acks"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 5195 }) }))),
  (("unconfirmedReads"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("confirmedReads"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 5661 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 5666 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5669 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5672 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5675 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5666 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5669 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5672 })))]))),
  ((GoLean.Loc.base { id := 5758 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 6070 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6072 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8191 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 6) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8192 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8193 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8194 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Message" }) #[(("Type"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8191 }))),
  (("To"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8192 }))),
  (("From"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8193 }))),
  (("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8197 }))),
  (("LogTerm"), (GoLean.Sym.Value.nil)),
  (("Index"), (GoLean.Sym.Value.nil)),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Commit"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("Reject"), (GoLean.Sym.Value.nil)),
  (("RejectHint"), (GoLean.Sym.Value.nil)),
  (("Context"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Responses"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 8195 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 }))]))),
  ((GoLean.Loc.base { id := 8196 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))]))),
  ((GoLean.Loc.base { id := 8197 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8198 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8199 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8200 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8198 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8199 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 8201 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8200 }))]))),
  ((GoLean.Loc.base { id := 8202 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8203 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8204 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 8205 }) })))),
  ((GoLean.Loc.base { id := 8205 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.int)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))]))),
  ((GoLean.Loc.base { id := 8206 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 8205 }) })))),
  ((GoLean.Loc.base { id := 8207 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8195 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 8208 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8209 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8210 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8211 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8212 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8213 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8214 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8215 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8216 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 2) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8217 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8218 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8219 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 2) (GoLean.Sym.SymInt.lit 1))))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8220 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8221 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8222 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8223 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8224 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8225 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8226 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8227 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8228 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8229 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8230 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8231 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8232 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8233 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8234 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8235 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8236 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int32)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8237 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8238 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8239 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8240 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8241 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8242 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8243 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8244 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8245 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8246 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8247 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8248 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 8249 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[114, 51, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 54, 45, 62, 49] })))),
  ((GoLean.Loc.base { id := 8250 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 8251 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8252 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8253 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8254 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8255 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8256 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 170 })))),
  ((GoLean.Loc.base { id := 8257 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8258 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1742 })))),
  ((GoLean.Loc.base { id := 8259 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8260 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8261 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8262 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8263 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8264 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8265 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8266 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8267 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8268 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8269 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 27 }), offset := 0, len := 23, cap := 23 })))),
  ((GoLean.Loc.base { id := 8270 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8271 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int32)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int32)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8272 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8273 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8274 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8275 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8276 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8277 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8278 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8279 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8280 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8281 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 28 }), offset := 0, len := 23, cap := 23 })))),
  ((GoLean.Loc.base { id := 8282 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8283 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int32)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int32)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8284 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8285 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8286 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8287 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8288 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8289 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8290 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8291 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8292 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8293 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8294 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8295 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8296 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8297 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8298 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8299 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8300 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8301 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 3)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8302 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8303 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8304 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8305 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8306 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8307 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8308 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8309 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8310 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8311 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8312 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8313 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8314 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8315 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8316 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 4)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8317 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8318 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8319 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8320 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8321 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8322 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8323 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8324 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8325 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8326 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8327 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 4)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8328 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8329 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8330 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8331 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8332 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8333 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8334 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8335 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8336 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8337 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8338 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8339 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8340 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8341 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8342 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8343 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8344 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8345 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8346 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8347 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8348 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8349 }), offset := 0, len := 4, cap := 4 })))),
  ((GoLean.Loc.base { id := 8349 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 8350 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  ((GoLean.Loc.base { id := 8351 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[37, 120, 32, 114, 101, 99, 101, 105, 118, 101, 100, 32, 37, 115, 32, 102, 114, 111, 109, 32, 37, 120, 32,
             97, 116, 32, 116, 101, 114, 109, 32, 37, 100] })))),
  ((GoLean.Loc.base { id := 8352 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8349 }), offset := 0, len := 4, cap := 4 })))),
  ((GoLean.Loc.base { id := 8353 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 389 }) { key := "raft.raft" } "trk")))),
  ((GoLean.Loc.base { id := 8354 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8355 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8356 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8357 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8358 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8359 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8360 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8361 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 389 }) { key := "raft.raft" } "trk")))),
  ((GoLean.Loc.base { id := 8362 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 0) (GoLean.Sym.SymInt.lit 1))))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8363 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8364 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8365 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8366 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1107 })))),
  ((GoLean.Loc.base { id := 8367 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8368 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8369 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8370 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1110 })))),
  ((GoLean.Loc.base { id := 8371 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8372 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))))]
  8373)

def vrCB8 : SymConfig :=
  (GoLean.Sym.Config.next (GoLean.Sym.Cont.mapIterK (some "id") (some "pr") (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.fieldGet
        (GoLean.GoCore.Expr.deref
          (GoLean.GoCore.Expr.var "pr")
          (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))
        { key := "tracker.Progress" }
        "IsLearner")
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.seqn
      #[GoLean.GoCore.Stmt.initialization { id := "v", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.initialization { id := "voted", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.mapLookup
          (GoLean.GoCore.Assignee.var "v")
          (GoLean.GoCore.Assignee.var "voted")
          (GoLean.GoCore.Expr.fieldGet
            (GoLean.GoCore.Expr.deref
              (GoLean.GoCore.Expr.var "p")
              (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
            { key := "tracker.ProgressTracker" }
            "Votes")
          (GoLean.GoCore.Expr.var "id")
          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
          (GoLean.GoCore.Ty.bool)],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "voted"))
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "v")
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "granted")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "granted")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "rejected")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "rejected")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])]) (some (GoLean.Loc.base { id := 1103 })) #[(GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)),
  (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))] #[(GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)),
  (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)),
  (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64))] ([[],
 [("$res2", GoLean.Loc.base { id := 8364 }),
  ("rejected", GoLean.Loc.base { id := 8363 }),
  ("granted", GoLean.Loc.base { id := 8362 }),
  ("p", GoLean.Loc.base { id := 8361 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "result", typ := GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" } },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "result"]
       { key := "quorum.JointConfig.VoteResult" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.fieldGet
             (GoLean.GoCore.Expr.deref
               (GoLean.GoCore.Expr.var "p")
               (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
             { key := "tracker.ProgressTracker" }
             "Config")
           { key := "tracker.Config" }
           "Voters",
         GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref
             (GoLean.GoCore.Expr.var "p")
             (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
           { key := "tracker.ProgressTracker" }
           "Votes"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "granted") (GoLean.GoCore.Expr.var "granted"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "rejected") (GoLean.GoCore.Expr.var "rejected"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res2") (GoLean.GoCore.Expr.var "result"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[],
 [("$res2", GoLean.Loc.base { id := 8364 }),
  ("rejected", GoLean.Loc.base { id := 8363 }),
  ("granted", GoLean.Loc.base { id := 8362 }),
  ("p", GoLean.Loc.base { id := 8361 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1353"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1354"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1355"])]) ([[("$c1355", GoLean.Loc.base { id := 8360 }),
  ("$c1354", GoLean.Loc.base { id := 8359 }),
  ("$c1353", GoLean.Loc.base { id := 8358 })],
 [("result", GoLean.Loc.base { id := 8347 }),
  ("rejected", GoLean.Loc.base { id := 8346 }),
  ("granted", GoLean.Loc.base { id := 8345 }),
  ("v", GoLean.Loc.base { id := 8344 }),
  ("t", GoLean.Loc.base { id := 8343 }),
  ("id", GoLean.Loc.base { id := 8342 }),
  ("r", GoLean.Loc.base { id := 8341 })]]) ([GoLean.Loc.base { id := 8362 }, GoLean.Loc.base { id := 8363 }, GoLean.Loc.base { id := 8364 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "granted") (GoLean.GoCore.Expr.var "$c1353"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "rejected") (GoLean.GoCore.Expr.var "$c1354"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "result") (GoLean.GoCore.Expr.var "$c1355"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("$c1355", GoLean.Loc.base { id := 8360 }),
  ("$c1354", GoLean.Loc.base { id := 8359 }),
  ("$c1353", GoLean.Loc.base { id := 8358 })],
 [("result", GoLean.Loc.base { id := 8347 }),
  ("rejected", GoLean.Loc.base { id := 8346 }),
  ("granted", GoLean.Loc.base { id := 8345 }),
  ("v", GoLean.Loc.base { id := 8344 }),
  ("t", GoLean.Loc.base { id := 8343 }),
  ("id", GoLean.Loc.base { id := 8342 }),
  ("r", GoLean.Loc.base { id := 8341 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "gr"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "rj"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "res"])]) ([[("res", GoLean.Loc.base { id := 8340 }),
  ("rj", GoLean.Loc.base { id := 8339 }),
  ("gr", GoLean.Loc.base { id := 8338 }),
  ("$c1575", GoLean.Loc.base { id := 8335 }),
  ("$c1574", GoLean.Loc.base { id := 8332 }),
  ("$c1573", GoLean.Loc.base { id := 8329 })],
 [],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) ([GoLean.Loc.base { id := 8345 }, GoLean.Loc.base { id := 8346 }, GoLean.Loc.base { id := 8347 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "$c1576", typ := GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" } },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c1576"]
       { key := "raftpb.Message.GetType" }
       #[GoLean.GoCore.Expr.var "m"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "$c1577", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }) },
     GoLean.GoCore.Stmt.makeSlice
       (GoLean.GoCore.Assignee.var "$c1577")
       (GoLean.GoCore.Ty.interface { key := "any" })
       (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))
       (some (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
         (GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "r") (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
           { key := "raft.raft" }
           "id")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.var "gr")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })
         (GoLean.GoCore.Expr.var "$c1576")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.var "rj"))],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "raft.Logger.Infof" }
   #[GoLean.GoCore.Expr.fieldGet
       (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "r") (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
       { key := "raft.raft" }
       "logger",
     GoLean.GoCore.Expr.stringLit
       { bytes := #[37, 120, 32, 104, 97, 115, 32, 114, 101, 99, 101, 105, 118, 101, 100, 32, 37, 100, 32, 37, 115, 32,
                    118, 111, 116, 101, 115, 32, 97, 110, 100, 32, 37, 100, 32, 118, 111, 116, 101, 32, 114, 101, 106,
                    101, 99, 116, 105, 111, 110, 115] },
     GoLean.GoCore.Expr.var "$c1577"],
 GoLean.GoCore.Stmt.breakable
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$sw1578", typ := GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" } },
           GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$sw1578") (GoLean.GoCore.Expr.var "res")],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$swi1579", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
           GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))],
       GoLean.GoCore.Stmt.block
         #[]
         #[GoLean.GoCore.Stmt.ifThenElse
             (GoLean.GoCore.Expr.eqCmp
               (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })
               (GoLean.GoCore.Expr.var "$sw1578")
               (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.uint8)))
             (GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.var "$swi1579")
                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))])
             (GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.ifThenElse
                   (GoLean.GoCore.Expr.eqCmp
                     (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })
                     (GoLean.GoCore.Expr.var "$sw1578")
                     (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint8)))
                   (GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.assign
                         (GoLean.GoCore.Assignee.var "$swi1579")
                         (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))])
                   (GoLean.GoCore.Stmt.seqn #[])])],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$swf1579", typ := GoLean.GoCore.Ty.bool },
           GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.or
           (GoLean.GoCore.Expr.var "$swf1579")
           (GoLean.GoCore.Expr.eqCmp
             (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
             (GoLean.GoCore.Expr.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
             GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.ifThenElse
                   (GoLean.GoCore.Expr.eqCmp
                     (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
                     (GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "r")
                         (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                       { key := "raft.raft" }
                       "state")
                     (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.uint64)))
                   (GoLean.GoCore.Stmt.block
                     #[]
                     #[GoLean.GoCore.Stmt.call
                         #[]
                         { key := "raft.raft.campaign" }
                         #[GoLean.GoCore.Expr.var "r",
                           GoLean.GoCore.Expr.stringLit
                             { bytes := #[67, 97, 109, 112, 97, 105, 103, 110, 69, 108, 101, 99, 116, 105, 111,
                                          110] }]])
                   (GoLean.GoCore.Stmt.block
                     #[]
                     #[GoLean.GoCore.Stmt.call #[] { key := "raft.raft.becomeLeader" } #[GoLean.GoCore.Expr.var "r"],
                       GoLean.GoCore.Stmt.call #[] { key := "raft.raft.bcastAppend" } #[GoLean.GoCore.Expr.var "r"]])]])
         (GoLean.GoCore.Stmt.seqn #[]),
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.or
           (GoLean.GoCore.Expr.var "$swf1579")
           (GoLean.GoCore.Expr.eqCmp
             (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
             (GoLean.GoCore.Expr.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
             GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.call
                   #[]
                   { key := "raft.raft.becomeFollower" }
                   #[GoLean.GoCore.Expr.var "r",
                     GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "r")
                         (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                       { key := "raft.raft" }
                       "Term",
                     GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64)]]])
         (GoLean.GoCore.Stmt.seqn #[])])]) ([[("res", GoLean.Loc.base { id := 8340 }),
  ("rj", GoLean.Loc.base { id := 8339 }),
  ("gr", GoLean.Loc.base { id := 8338 }),
  ("$c1575", GoLean.Loc.base { id := 8335 }),
  ("$c1574", GoLean.Loc.base { id := 8332 }),
  ("$c1573", GoLean.Loc.base { id := 8329 })],
 [],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.or
     (GoLean.GoCore.Expr.var "$swf1582")
     (GoLean.GoCore.Expr.eqCmp
       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
       (GoLean.GoCore.Expr.var "$swi1582")
       (GoLean.GoCore.Expr.intLit 5 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1582") (GoLean.GoCore.Expr.boolLit false)],
       GoLean.GoCore.Stmt.block
         #[]
         #[GoLean.GoCore.Stmt.seqn
             #[GoLean.GoCore.Stmt.initialization
                 { id := "$c1580", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
               GoLean.GoCore.Stmt.call
                 #[GoLean.GoCore.Assignee.var "$c1580"]
                 { key := "raftpb.Message.GetFrom" }
                 #[GoLean.GoCore.Expr.var "m"]],
           GoLean.GoCore.Stmt.seqn
             #[GoLean.GoCore.Stmt.initialization
                 { id := "$c1581", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }) },
               GoLean.GoCore.Stmt.makeSlice
                 (GoLean.GoCore.Assignee.var "$c1581")
                 (GoLean.GoCore.Ty.interface { key := "any" })
                 (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))
                 (some (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "id")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "Term")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "state")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.var "$c1580"))],
           GoLean.GoCore.Stmt.call
             #[]
             { key := "raft.Logger.Debugf" }
             #[GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "r")
                   (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                 { key := "raft.raft" }
                 "logger",
               GoLean.GoCore.Expr.stringLit
                 { bytes := #[37, 120, 32, 91, 116, 101, 114, 109, 32, 37, 100, 32, 115, 116, 97, 116, 101, 32, 37, 118,
                              93, 32, 105, 103, 110, 111, 114, 101, 100, 32, 77, 115, 103, 84, 105, 109, 101, 111, 117,
                              116, 78, 111, 119, 32, 102, 114, 111, 109, 32, 37, 120] },
               GoLean.GoCore.Expr.var "$c1581"]]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.breakableK (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.nil none),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "err"])]) ([[("err", GoLean.Loc.base { id := 8318 })],
 [],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) ([GoLean.Loc.base { id := 8321 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.neqCmp
     (GoLean.GoCore.Ty.interface { key := "error" })
     (GoLean.GoCore.Expr.var "err")
     (GoLean.GoCore.Expr.nil none))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "err"),
           GoLean.GoCore.Stmt.returnStmt]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("err", GoLean.Loc.base { id := 8318 })],
 [],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.breakableK (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.nil none),
     GoLean.GoCore.Stmt.returnStmt]]) ([[],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1790"])]) ([[("$c1790", GoLean.Loc.base { id := 8295 }),
  ("$c1789", GoLean.Loc.base { id := 8291 }),
  ("$c1787", GoLean.Loc.base { id := 8284 }),
  ("$c1784", GoLean.Loc.base { id := 8276 }),
  ("$c1783", GoLean.Loc.base { id := 8273 }),
  ("$c1782", GoLean.Loc.base { id := 8272 }),
  ("$c1779", GoLean.Loc.base { id := 8264 }),
  ("$c1778", GoLean.Loc.base { id := 8261 })],
 [("$res0", GoLean.Loc.base { id := 8260 }),
  ("m", GoLean.Loc.base { id := 8259 }),
  ("rn", GoLean.Loc.base { id := 8258 })]]) ([GoLean.Loc.base { id := 8298 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "$c1790"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("$c1790", GoLean.Loc.base { id := 8295 }),
  ("$c1789", GoLean.Loc.base { id := 8291 }),
  ("$c1787", GoLean.Loc.base { id := 8284 }),
  ("$c1784", GoLean.Loc.base { id := 8276 }),
  ("$c1783", GoLean.Loc.base { id := 8273 }),
  ("$c1782", GoLean.Loc.base { id := 8272 }),
  ("$c1779", GoLean.Loc.base { id := 8264 }),
  ("$c1778", GoLean.Loc.base { id := 8261 })],
 [("$res0", GoLean.Loc.base { id := 8260 }),
  ("m", GoLean.Loc.base { id := 8259 }),
  ("rn", GoLean.Loc.base { id := 8258 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "err"])]) ([[("err", GoLean.Loc.base { id := 8257 })],
 [("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) ([GoLean.Loc.base { id := 8260 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.neqCmp
     (GoLean.GoCore.Ty.interface { key := "error" })
     (GoLean.GoCore.Expr.var "err")
     (GoLean.GoCore.Expr.nil none))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.stringLit { bytes := #[32, 115, 116, 101, 112, 101, 114, 114] }]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("err", GoLean.Loc.base { id := 8257 })],
 [("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$cr0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$cr0"]
       { key := "main.twin.harvest" }
       #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "to"]]]) ([[("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) (GoLean.Sym.Cont.frame ([]) ([[("$c2241", GoLean.Loc.base { id := 8243 }),
  ("$c2240", GoLean.Loc.base { id := 8240 }),
  ("$c2239", GoLean.Loc.base { id := 8232 }),
  ("$c2238", GoLean.Loc.base { id := 8229 }),
  ("$c2237", GoLean.Loc.base { id := 8223 }),
  ("$c2236", GoLean.Loc.base { id := 8215 }),
  ("m", GoLean.Loc.base { id := 8214 }),
  ("picked", GoLean.Loc.base { id := 8212 })],
 [("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) ([]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2242", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2242"]
       { key := "main.twin.projection" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add (GoLean.GoCore.Expr.stringLit { bytes := #[32] }) (GoLean.GoCore.Expr.var "$c2242"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "stuckPropose")
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.continueStmt]) ([[("$c2241", GoLean.Loc.base { id := 8243 }),
  ("$c2240", GoLean.Loc.base { id := 8240 }),
  ("$c2239", GoLean.Loc.base { id := 8232 }),
  ("$c2238", GoLean.Loc.base { id := 8229 }),
  ("$c2237", GoLean.Loc.base { id := 8223 }),
  ("$c2236", GoLean.Loc.base { id := 8215 }),
  ("m", GoLean.Loc.base { id := 8214 }),
  ("picked", GoLean.Loc.base { id := 8212 })],
 [("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2243", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2243"]
       { key := "main.twin.complete" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.and
     (GoLean.GoCore.Expr.var "$c2243")
     (GoLean.GoCore.Expr.eqCmp
       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
       (GoLean.GoCore.Expr.length
         (GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "pending")
         (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.breakStmt])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.greaterCmp
     (GoLean.GoCore.Expr.length
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "pending")
       (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$c2244", typ := GoLean.GoCore.Ty.string },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2244"]
             { key := "itoa" }
             #[GoLean.GoCore.Expr.add
                 (GoLean.GoCore.Expr.var "round")
                 (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.add
             (GoLean.GoCore.Expr.add
               (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
               (GoLean.GoCore.Expr.var "$c2244"))
             (GoLean.GoCore.Expr.stringLit { bytes := #[32] })],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.step" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.structLit
             (GoLean.GoCore.Ty.defined { key := "main.op" })
             #[GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int),
               GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int),
               GoLean.GoCore.Expr.defaultValue (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.stringLit { bytes := #[10] }],
       GoLean.GoCore.Stmt.assign
         (GoLean.GoCore.Assignee.var "stuckPropose")
         (GoLean.GoCore.Expr.add
           (GoLean.GoCore.Expr.var "stuckPropose")
           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.greaterCmp
           (GoLean.GoCore.Expr.var "stuckPropose")
           (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int)))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.addr
                     (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                   (GoLean.GoCore.Expr.boolLit true)],
             GoLean.GoCore.Stmt.call
               #[]
               { key := "main.twin.say" }
               #[GoLean.GoCore.Expr.var "t",
                 GoLean.GoCore.Expr.stringLit
                   { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112, 111, 115, 101, 32, 115,
                                116, 117, 99, 107, 32, 97, 116, 32, 113, 117, 105, 101, 115, 99, 101, 110, 99, 101,
                                10] }],
             GoLean.GoCore.Stmt.breakStmt])
         (GoLean.GoCore.Stmt.seqn #[]),
       GoLean.GoCore.Stmt.continueStmt])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
       (GoLean.GoCore.Expr.boolLit true)],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.stringLit
       { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101, 110, 116, 32, 119, 105,
                    116, 104, 111, 117, 116, 32, 83, 52, 10] }],
 GoLean.GoCore.Stmt.breakStmt]) ([[("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.loop (GoLean.GoCore.Expr.boolLit true) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "$forFirst")
      (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$forFirst") (GoLean.GoCore.Expr.boolLit false))
      (GoLean.GoCore.Stmt.assign
        (GoLean.GoCore.Assignee.var "round")
        (GoLean.GoCore.Expr.add
          (GoLean.GoCore.Expr.var "round")
          (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
    GoLean.GoCore.Stmt.seqn #[],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.lessCmp
        (GoLean.GoCore.Expr.var "round")
        (GoLean.GoCore.Expr.intLit 400 (GoLean.GoCore.IntKind.int)))
      (GoLean.GoCore.Stmt.seqn #[])
      (GoLean.GoCore.Stmt.breakStmt),
    GoLean.GoCore.Stmt.block
      #[]
      #[GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization
              { id := "$c2235",
                typ := GoLean.GoCore.Ty.map
                         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                         (GoLean.GoCore.Ty.bool) },
            GoLean.GoCore.Stmt.makeMap
              (GoLean.GoCore.Assignee.var "$c2235")
              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
              (GoLean.GoCore.Ty.bool)
              none],
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization
              { id := "live",
                typ := GoLean.GoCore.Ty.map
                         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                         (GoLean.GoCore.Ty.bool) },
            GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "live") (GoLean.GoCore.Expr.var "$c2235")],
        GoLean.GoCore.Stmt.block
          #[]
          #[GoLean.GoCore.Stmt.initialization
              { id := "$rcoll",
                typ := GoLean.GoCore.Ty.slice
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rcoll")
              (GoLean.GoCore.Expr.fieldGet
                (GoLean.GoCore.Expr.deref
                  (GoLean.GoCore.Expr.var "t")
                  (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                { key := "main.twin" }
                "net"),
            GoLean.GoCore.Stmt.initialization
              { id := "$rlen", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rlen")
              (GoLean.GoCore.Expr.length (GoLean.GoCore.Expr.var "$rcoll") none),
            GoLean.GoCore.Stmt.initialization
              { id := "$ridx", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$ridx")
              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)),
            GoLean.GoCore.Stmt.initialization { id := "$rfirst", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$rfirst") (GoLean.GoCore.Expr.boolLit true),
            GoLean.GoCore.Stmt.while
              (GoLean.GoCore.Expr.boolLit true)
              (GoLean.GoCore.Stmt.block
                #[]
                #[GoLean.GoCore.Stmt.ifThenElse
                    (GoLean.GoCore.Expr.var "$rfirst")
                    (GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "$rfirst")
                      (GoLean.GoCore.Expr.boolLit false))
                    (GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "$ridx")
                      (GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "$ridx")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
                  GoLean.GoCore.Stmt.ifThenElse
                    (GoLean.GoCore.Expr.atLeastCmp (GoLean.GoCore.Expr.var "$ridx") (GoLean.GoCore.Expr.var "$rlen"))
                    (GoLean.GoCore.Stmt.breakStmt)
                    (GoLean.GoCore.Stmt.seqn #[]),
                  GoLean.GoCore.Stmt.initialization
                    { id := "j", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                  GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "j") (GoLean.GoCore.Expr.var "$ridx"),
                  GoLean.GoCore.Stmt.block
                    #[]
                    #[GoLean.GoCore.Stmt.ifThenElse
                        (GoLean.GoCore.Expr.indexGet
                          (GoLean.GoCore.Expr.fieldGet
                            (GoLean.GoCore.Expr.deref
                              (GoLean.GoCore.Expr.var "t")
                              (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                            { key := "main.twin" }
                            "live")
                          (GoLean.GoCore.Expr.var "j"))
                        (GoLean.GoCore.Stmt.block
                          #[]
                          #[GoLean.GoCore.Stmt.mapAssign
                              (GoLean.GoCore.Expr.var "live")
                              (GoLean.GoCore.Expr.var "j")
                              (GoLean.GoCore.Expr.boolLit true)
                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                              (GoLean.GoCore.Ty.bool)])
                        (GoLean.GoCore.Stmt.seqn #[])]])],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.length
              (GoLean.GoCore.Expr.var "live")
              (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))))
            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "picked", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "picked")
                    (GoLean.GoCore.Expr.intLit (-1) (GoLean.GoCore.IntKind.int))],
              GoLean.GoCore.Stmt.mapRange
                (some "j")
                none
                (GoLean.GoCore.Expr.var "live")
                (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                (GoLean.GoCore.Ty.bool)
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "picked") (GoLean.GoCore.Expr.var "j")],
                    GoLean.GoCore.Stmt.breakStmt]),
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "m",
                      typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "m")
                    (GoLean.GoCore.Expr.indexGet
                      (GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "t")
                          (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                        { key := "main.twin" }
                        "net")
                      (GoLean.GoCore.Expr.var "picked"))],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2236", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2236"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "round")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2237", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2237"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.var "picked"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2238", typ := GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" } },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2238"]
                    { key := "raftpb.Message.GetType" }
                    #[GoLean.GoCore.Expr.var "m"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2239", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2239"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.convert
                        (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                        (GoLean.GoCore.Expr.var "$c2238")]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2240", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2240"]
                    { key := "raftpb.Message.GetTo" }
                    #[GoLean.GoCore.Expr.var "m"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2241", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2241"]
                    { key := "utoa" }
                    #[GoLean.GoCore.Expr.var "$c2240"]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.add
                          (GoLean.GoCore.Expr.add
                            (GoLean.GoCore.Expr.add
                              (GoLean.GoCore.Expr.add
                                (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
                                (GoLean.GoCore.Expr.var "$c2236"))
                              (GoLean.GoCore.Expr.stringLit { bytes := #[32, 112, 105, 99, 107, 35] }))
                            (GoLean.GoCore.Expr.var "$c2237"))
                          (GoLean.GoCore.Expr.stringLit { bytes := #[32, 116, 121, 112, 101] }))
                        (GoLean.GoCore.Expr.var "$c2239"))
                      (GoLean.GoCore.Expr.stringLit { bytes := #[45, 62] }))
                    (GoLean.GoCore.Expr.var "$c2241")],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.deliverIdx" }
                #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "picked"],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2242", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2242"]
                    { key := "main.twin.projection" }
                    #[GoLean.GoCore.Expr.var "t"]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.stringLit { bytes := #[32] })
                      (GoLean.GoCore.Expr.var "$c2242"))
                    (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "stuckPropose")
                    (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
              GoLean.GoCore.Stmt.continueStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "$c2243", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c2243"]
              { key := "main.twin.complete" }
              #[GoLean.GoCore.Expr.var "t"]],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.and
            (GoLean.GoCore.Expr.var "$c2243")
            (GoLean.GoCore.Expr.eqCmp
              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
              (GoLean.GoCore.Expr.length
                (GoLean.GoCore.Expr.fieldGet
                  (GoLean.GoCore.Expr.deref
                    (GoLean.GoCore.Expr.var "t")
                    (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                  { key := "main.twin" }
                  "pending")
                (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
          (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.breakStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.length
              (GoLean.GoCore.Expr.fieldGet
                (GoLean.GoCore.Expr.deref
                  (GoLean.GoCore.Expr.var "t")
                  (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                { key := "main.twin" }
                "pending")
              (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2244", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2244"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "round")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
                      (GoLean.GoCore.Expr.var "$c2244"))
                    (GoLean.GoCore.Expr.stringLit { bytes := #[32] })],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.step" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.structLit
                    (GoLean.GoCore.Ty.defined { key := "main.op" })
                    #[GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int),
                      GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int),
                      GoLean.GoCore.Expr.defaultValue (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.stringLit { bytes := #[10] }],
              GoLean.GoCore.Stmt.assign
                (GoLean.GoCore.Assignee.var "stuckPropose")
                (GoLean.GoCore.Expr.add
                  (GoLean.GoCore.Expr.var "stuckPropose")
                  (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.greaterCmp
                  (GoLean.GoCore.Expr.var "stuckPropose")
                  (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int)))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.addr
                            (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                          (GoLean.GoCore.Expr.boolLit true)],
                    GoLean.GoCore.Stmt.call
                      #[]
                      { key := "main.twin.say" }
                      #[GoLean.GoCore.Expr.var "t",
                        GoLean.GoCore.Expr.stringLit
                          { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112, 111, 115, 101, 32,
                                       115, 116, 117, 99, 107, 32, 97, 116, 32, 113, 117, 105, 101, 115, 99, 101, 110,
                                       99, 101, 10] }],
                    GoLean.GoCore.Stmt.breakStmt])
                (GoLean.GoCore.Stmt.seqn #[]),
              GoLean.GoCore.Stmt.continueStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.addr
                (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
              (GoLean.GoCore.Expr.boolLit true)],
        GoLean.GoCore.Stmt.call
          #[]
          { key := "main.twin.say" }
          #[GoLean.GoCore.Expr.var "t",
            GoLean.GoCore.Expr.stringLit
              { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101, 110, 116, 32,
                           119, 105, 116, 104, 111, 117, 116, 32, 83, 52, 10] }],
        GoLean.GoCore.Stmt.breakStmt]]) ([[("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "comp", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "comp")
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2245", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2245"]
       { key := "main.twin.complete" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.and
     (GoLean.GoCore.Expr.and
       (GoLean.GoCore.Expr.var "$c2245")
       (GoLean.GoCore.Expr.eqCmp
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.length
           (GoLean.GoCore.Expr.fieldGet
             (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
             { key := "main.twin" }
             "pending")
           (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
     (GoLean.GoCore.Expr.not
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "halt")))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "comp")
             (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "floorOK", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "floorOK")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.or
     (GoLean.GoCore.Expr.lessCmp
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "claims")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))
     (GoLean.GoCore.Expr.lessCmp
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "committed")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "floorOK")
             (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2246", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2246"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "violations"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2247", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2247"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "claims"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2248", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2248"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "committed"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2249", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call #[GoLean.GoCore.Assignee.var "$c2249"] { key := "itoa" } #[GoLean.GoCore.Expr.var "comp"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2250", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2250"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.var "floorOK"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2251", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2251"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.var "round"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add
         (GoLean.GoCore.Expr.add
           (GoLean.GoCore.Expr.add
             (GoLean.GoCore.Expr.add
               (GoLean.GoCore.Expr.add
                 (GoLean.GoCore.Expr.add
                   (GoLean.GoCore.Expr.add
                     (GoLean.GoCore.Expr.add
                       (GoLean.GoCore.Expr.add
                         (GoLean.GoCore.Expr.add
                           (GoLean.GoCore.Expr.add
                             (GoLean.GoCore.Expr.stringLit { bytes := #[101, 110, 100, 32, 118, 105, 111, 108, 61] })
                             (GoLean.GoCore.Expr.var "$c2246"))
                           (GoLean.GoCore.Expr.stringLit { bytes := #[32, 99, 108, 97, 105, 109, 115, 61] }))
                         (GoLean.GoCore.Expr.var "$c2247"))
                       (GoLean.GoCore.Expr.stringLit
                         { bytes := #[32, 99, 111, 109, 109, 105, 116, 116, 101, 100, 61] }))
                     (GoLean.GoCore.Expr.var "$c2248"))
                   (GoLean.GoCore.Expr.stringLit { bytes := #[32, 99, 111, 109, 112, 108, 101, 116, 101, 61] }))
                 (GoLean.GoCore.Expr.var "$c2249"))
               (GoLean.GoCore.Expr.stringLit { bytes := #[32, 102, 108, 111, 111, 114, 61] }))
             (GoLean.GoCore.Expr.var "$c2250"))
           (GoLean.GoCore.Expr.stringLit { bytes := #[32, 114, 111, 117, 110, 100, 115, 61] }))
         (GoLean.GoCore.Expr.var "$c2251"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2252", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2252"]
       { key := "main.twin.projection" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add
         (GoLean.GoCore.Expr.stringLit { bytes := #[102, 105, 110, 97, 108, 32] })
         (GoLean.GoCore.Expr.var "$c2252"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "t"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res1") (GoLean.GoCore.Expr.var "comp"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res2") (GoLean.GoCore.Expr.var "floorOK"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "t"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "comp"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "floorOK"])]) ([[("floorOK", GoLean.Loc.base { id := 105 }),
  ("comp", GoLean.Loc.base { id := 104 }),
  ("t", GoLean.Loc.base { id := 103 })],
 [("$res4", GoLean.Loc.base { id := 102 }),
  ("$res3", GoLean.Loc.base { id := 101 }),
  ("$res2", GoLean.Loc.base { id := 100 }),
  ("$res1", GoLean.Loc.base { id := 99 }),
  ("$res0", GoLean.Loc.base { id := 98 })]]) ([GoLean.Loc.base { id := 106 }, GoLean.Loc.base { id := 107 }, GoLean.Loc.base { id := 108 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res0")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "violations"),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res1")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "claims"),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res2")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "committed"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res3") (GoLean.GoCore.Expr.var "comp"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res4") (GoLean.GoCore.Expr.var "floorOK"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("floorOK", GoLean.Loc.base { id := 105 }),
  ("comp", GoLean.Loc.base { id := 104 }),
  ("t", GoLean.Loc.base { id := 103 })],
 [("$res4", GoLean.Loc.base { id := 102 }),
  ("$res3", GoLean.Loc.base { id := 101 }),
  ("$res2", GoLean.Loc.base { id := 100 }),
  ("$res1", GoLean.Loc.base { id := 99 }),
  ("$res0", GoLean.Loc.base { id := 98 })]]) (GoLean.Sym.Cont.frame ([]) ([]) ([]) [] (GoLean.Sym.Cont.stop) false)) false)))))))) false))) false)) false)))))) false)))))) false)) false))))

def vrSB9 : SymState :=
  (GoLean.Sym.State.mk
  [((GoLean.Loc.base { id := 15 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 57 })))),
  ((GoLean.Loc.base { id := 18 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.lockedRand" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 67 })))),
  ((GoLean.Loc.base { id := 27 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))]))),
  ((GoLean.Loc.base { id := 28 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)),
  (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))]))),
  ((GoLean.Loc.base { id := 57 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Commit"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 67 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.lockedRand" })) (GoLean.Sym.Value.struct ({ key := "raft.lockedRand" }) #[(("mu"), (GoLean.Sym.Value.syncData (GoLean.SyncPrim.mutex false)))]))),
  ((GoLean.Loc.base { id := 110 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 115 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[]))),
  ((GoLean.Loc.base { id := 121 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twin" })) (GoLean.Sym.Value.struct ({ key := "main.twin" }) #[(("nodes"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 1764 }), offset := 0, len := 3, cap := 4 }))),
  (("net"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8195 }), offset := 0, len := 1, cap := 1 }))),
  (("live"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8196 }), offset := 0, len := 1, cap := 1 }))),
  (("leaderOf"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 115 }) }))),
  (("byIndex"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 118 }) }))),
  (("claims"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("violations"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int))),
  (("pending"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 136 }), offset := 0, len := 2, cap := 4 }))),
  (("driven"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("seq"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.int))),
  (("trace"), (GoLean.Sym.Value.string ({ bytes := #[91, 99, 104, 111, 105, 99, 101, 45, 100, 114, 105, 118, 101, 110, 93, 10, 99, 97, 109, 112, 97, 105, 103,
             110, 49, 114, 49, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 53, 45, 62, 50, 32, 32, 124, 67,
             49, 47, 49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 70, 48, 47, 48, 47, 48, 32, 110, 101, 116, 61, 50, 10,
             114, 50, 32, 112, 105, 99, 107, 35, 49, 32, 116, 121, 112, 101, 53, 45, 62, 51, 32, 32, 124, 67, 49, 47,
             49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 70, 49, 47, 49, 47, 48, 32, 110, 101, 116, 61, 50, 10, 114, 51,
             32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 54, 45, 62, 49] }))),
  (("halt"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 170 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1742 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 179 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 167 }) })))]))),
  ((GoLean.Loc.base { id := 179 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.struct ({ key := "raft.MemoryStorage" }) #[(("Mutex"), (GoLean.Sym.Value.syncData (GoLean.SyncPrim.mutex false))),
  (("hardState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5675 }))),
  (("snapshot"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 258 }))),
  (("ents"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 300 }), offset := 0, len := 1, cap := 1 }))),
  (("callStats"), (GoLean.Sym.Value.struct ({ key := "raft.inMemStorageCallStats" }) #[(("initialState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("firstIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 4) (GoLean.GoCore.IntKind.int))),
  (("lastIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 15) (GoLean.GoCore.IntKind.int))),
  (("entries"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.int))),
  (("snapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))]))]))),
  ((GoLean.Loc.base { id := 286 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 295 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 298 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 286 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 295 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 300 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 298 }))]))),
  ((GoLean.Loc.base { id := 349 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })) (GoLean.Sym.Value.struct ({ key := "raft.raftLog" }) #[(("storage"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 179 })))),
  (("unstable"), (GoLean.Sym.Value.struct ({ key := "raft.unstable" }) #[(("snapshot"), (GoLean.Sym.Value.nil)),
  (("entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("offset"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("snapshotInProgress"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("offsetInProgress"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 }))))])),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applying"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("maxApplyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 389 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raft" })) (GoLean.Sym.Value.struct ({ key := "raft.raft" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Vote"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("readStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("raftLog"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 349 }))),
  (("maxMsgSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("maxUncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64))),
  (("trk"), (GoLean.Sym.Value.struct ({ key := "tracker.ProgressTracker" }) #[(("Config"), (GoLean.Sym.Value.struct ({ key := "tracker.Config" }) #[(("Voters"), (GoLean.Sym.Value.array #[(GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1086 }) })),
  (GoLean.Sym.Value.map ({ base := none }))])),
  (("AutoLeave"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Learners"), (GoLean.Sym.Value.map ({ base := none }))),
  (("LearnersNext"), (GoLean.Sym.Value.map ({ base := none })))])),
  (("Progress"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1103 }) }))),
  (("Votes"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 5058 }) }))),
  (("MaxInflight"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 256) (GoLean.GoCore.IntKind.int))),
  (("MaxInflightBytes"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64)))])),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("isLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("msgs"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("msgsAfterAppend"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("leadTransferee"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("pendingConfIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("disableConfChangeValidation"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("uncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("readOnly"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5198 }))),
  (("electionElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("heartbeatElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("checkQuorum"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("preVote"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("heartbeatTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("electionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("randomizedElectionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("disableProposalForwarding"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("stepDownOnRemoval"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("tick"), (GoLean.Sym.Value.funcVal ({ key := "raft.raft.tickElection" }) [(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 }))])),
  (("step"), (GoLean.Sym.Value.funcVal ({ key := "raft.stepCandidate" }) [])),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("pendingReadIndexMessages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("traceLogger"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 1086 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[])),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[])),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.struct ({ key := "struct{}" }) #[]))]))),
  ((GoLean.Loc.base { id := 1103 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1107 }))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1110 }))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1212 })))]))),
  ((GoLean.Loc.base { id := 1107 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5102 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1110 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5156 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1212 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.Sym.Value.struct ({ key := "tracker.Progress" }) #[(("Match"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("Next"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("sentCommit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("State"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("PendingSnapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RecentActive"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("MsgAppFlowPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Inflights"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5189 }))),
  (("IsLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1742 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })) (GoLean.Sym.Value.struct ({ key := "raft.RawNode" }) #[(("raft"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 }))),
  (("asyncStorageWrites"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("prevSoftSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5661 }))),
  (("prevHardSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5675 }))),
  (("stepsOnAdvance"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 5758 }), offset := 0, len := 0, cap := 4 })))]))),
  ((GoLean.Loc.base { id := 1764 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 170 })),
  (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1770 })),
  (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3369 })),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 1770 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1767 }) })))]))),
  ((GoLean.Loc.base { id := 3369 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 4941 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3378 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 3366 }) })))]))),
  ((GoLean.Loc.base { id := 5058 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true))),
  ((GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))))) (GoLean.GoCore.IntKind.uint64)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))]))),
  ((GoLean.Loc.base { id := 5198 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.readOnly" })) (GoLean.Sym.Value.struct ({ key := "raft.readOnly" }) #[(("option"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("acks"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 5195 }) }))),
  (("unconfirmedReads"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("confirmedReads"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 5661 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 5666 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5669 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5672 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 5675 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5666 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5669 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 5672 })))]))),
  ((GoLean.Loc.base { id := 5758 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 6070 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6072 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8191 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 6) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8192 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8193 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8194 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Message" }) #[(("Type"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8191 }))),
  (("To"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8192 }))),
  (("From"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8193 }))),
  (("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8197 }))),
  (("LogTerm"), (GoLean.Sym.Value.nil)),
  (("Index"), (GoLean.Sym.Value.nil)),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Commit"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("Reject"), (GoLean.Sym.Value.nil)),
  (("RejectHint"), (GoLean.Sym.Value.nil)),
  (("Context"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Responses"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 8195 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 }))]))),
  ((GoLean.Loc.base { id := 8196 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))]))),
  ((GoLean.Loc.base { id := 8197 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8198 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8199 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8200 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8198 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8199 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 8201 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8200 }))]))),
  ((GoLean.Loc.base { id := 8202 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8203 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8204 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 8205 }) })))),
  ((GoLean.Loc.base { id := 8205 }), (GoLean.Sym.HeapCell.mk (none) (GoLean.Sym.Value.mapData #[((GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.int)), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))]))),
  ((GoLean.Loc.base { id := 8206 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 8205 }) })))),
  ((GoLean.Loc.base { id := 8207 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8195 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 8208 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8209 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8210 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8211 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8212 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8213 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8214 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8215 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8216 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 2) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8217 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8218 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8219 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 2) (GoLean.Sym.SymInt.lit 1))))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8220 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8221 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[51] })))),
  ((GoLean.Loc.base { id := 8222 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8223 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8224 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8225 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8226 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8227 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8228 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[48] })))),
  ((GoLean.Loc.base { id := 8229 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8230 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8231 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8232 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8233 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8234 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8235 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8236 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int32)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8237 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8238 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[54] })))),
  ((GoLean.Loc.base { id := 8239 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8240 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8241 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8242 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8243 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8244 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.divC
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))
      10))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8245 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8246 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[49] })))),
  ((GoLean.Loc.base { id := 8247 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8248 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 8249 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[114, 51, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 54, 45, 62, 49] })))),
  ((GoLean.Loc.base { id := 8250 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 8251 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8252 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8253 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8254 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8255 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8256 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 170 })))),
  ((GoLean.Loc.base { id := 8257 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8258 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1742 })))),
  ((GoLean.Loc.base { id := 8259 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8260 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8261 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8262 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8263 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8264 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8265 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8266 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8267 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8268 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8269 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 27 }), offset := 0, len := 23, cap := 23 })))),
  ((GoLean.Loc.base { id := 8270 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8271 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int32)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int32)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8272 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8273 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8274 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8275 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8276 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8277 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8278 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8279 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8280 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8281 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 28 }), offset := 0, len := 23, cap := 23 })))),
  ((GoLean.Loc.base { id := 8282 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8283 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int32)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int32)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int32)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8284 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8285 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8286 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8287 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8288 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8289 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8290 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8291 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8292 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8293 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8294 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8295 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8296 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8297 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8298 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8299 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8300 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8301 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 3)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8302 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8303 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8304 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8305 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8306 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8307 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8308 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8309 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8310 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8311 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8312 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8313 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8314 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8315 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8316 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 4)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8317 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8318 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8319 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8320 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8321 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 8322 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8323 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8324 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8325 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8326 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8327 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 4)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8328 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8329 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8330 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8331 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8332 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8333 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8334 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8335 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8336 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 8194 })))),
  ((GoLean.Loc.base { id := 8337 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8338 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8339 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8340 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8341 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 389 })))),
  ((GoLean.Loc.base { id := 8342 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8343 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32)))),
  ((GoLean.Loc.base { id := 8344 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8345 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8346 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8347 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8348 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8349 }), offset := 0, len := 4, cap := 4 })))),
  ((GoLean.Loc.base { id := 8349 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int32)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int32)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int32) (GoLean.Sym.SymInt.lit 6)))) (GoLean.GoCore.IntKind.int32))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64))),
  (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 8350 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  ((GoLean.Loc.base { id := 8351 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.string)) (GoLean.Sym.Value.string ({ bytes := #[37, 120, 32, 114, 101, 99, 101, 105, 118, 101, 100, 32, 37, 115, 32, 102, 114, 111, 109, 32, 37, 120, 32,
             97, 116, 32, 116, 101, 114, 109, 32, 37, 100] })))),
  ((GoLean.Loc.base { id := 8352 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 8349 }), offset := 0, len := 4, cap := 4 })))),
  ((GoLean.Loc.base { id := 8353 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 389 }) { key := "raft.raft" } "trk")))),
  ((GoLean.Loc.base { id := 8354 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8355 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8356 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8357 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 8358 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8359 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8360 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8361 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 389 }) { key := "raft.raft" } "trk")))),
  ((GoLean.Loc.base { id := 8362 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 0) (GoLean.Sym.SymInt.lit 1))))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8363 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 8364 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint8)))),
  ((GoLean.Loc.base { id := 8365 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8366 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1107 })))),
  ((GoLean.Loc.base { id := 8367 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8368 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8369 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8370 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1110 })))),
  ((GoLean.Loc.base { id := 8371 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 8372 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 8373 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 8374 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1212 }))))]
  8375)

def vrCB9 : SymConfig :=
  (GoLean.Sym.Config.exec (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.fieldGet
        (GoLean.GoCore.Expr.deref
          (GoLean.GoCore.Expr.var "pr")
          (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))
        { key := "tracker.Progress" }
        "IsLearner")
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.seqn
      #[GoLean.GoCore.Stmt.initialization { id := "v", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.initialization { id := "voted", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.mapLookup
          (GoLean.GoCore.Assignee.var "v")
          (GoLean.GoCore.Assignee.var "voted")
          (GoLean.GoCore.Expr.fieldGet
            (GoLean.GoCore.Expr.deref
              (GoLean.GoCore.Expr.var "p")
              (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
            { key := "tracker.ProgressTracker" }
            "Votes")
          (GoLean.GoCore.Expr.var "id")
          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
          (GoLean.GoCore.Ty.bool)],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "voted"))
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "v")
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "granted")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "granted")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "rejected")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "rejected")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])]) ([[("pr", GoLean.Loc.base { id := 8374 }), ("id", GoLean.Loc.base { id := 8373 })],
 [],
 [("$res2", GoLean.Loc.base { id := 8364 }),
  ("rejected", GoLean.Loc.base { id := 8363 }),
  ("granted", GoLean.Loc.base { id := 8362 }),
  ("p", GoLean.Loc.base { id := 8361 })]]) (GoLean.Sym.Cont.mapIterK (some "id") (some "pr") (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "tracker.Progress" })) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.fieldGet
        (GoLean.GoCore.Expr.deref
          (GoLean.GoCore.Expr.var "pr")
          (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }))
        { key := "tracker.Progress" }
        "IsLearner")
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.seqn
      #[GoLean.GoCore.Stmt.initialization { id := "v", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.initialization { id := "voted", typ := GoLean.GoCore.Ty.bool },
        GoLean.GoCore.Stmt.mapLookup
          (GoLean.GoCore.Assignee.var "v")
          (GoLean.GoCore.Assignee.var "voted")
          (GoLean.GoCore.Expr.fieldGet
            (GoLean.GoCore.Expr.deref
              (GoLean.GoCore.Expr.var "p")
              (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
            { key := "tracker.ProgressTracker" }
            "Votes")
          (GoLean.GoCore.Expr.var "id")
          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
          (GoLean.GoCore.Ty.bool)],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "voted"))
      (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.continueStmt])
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "v")
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "granted")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "granted")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.assign
            (GoLean.GoCore.Assignee.var "rejected")
            (GoLean.GoCore.Expr.add
              (GoLean.GoCore.Expr.var "rejected")
              (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))])]) (some (GoLean.Loc.base { id := 1103 })) #[(GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)),
  (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)),
  (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64))] #[(GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)),
  (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)),
  (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 3) (GoLean.GoCore.IntKind.uint64))] ([[],
 [("$res2", GoLean.Loc.base { id := 8364 }),
  ("rejected", GoLean.Loc.base { id := 8363 }),
  ("granted", GoLean.Loc.base { id := 8362 }),
  ("p", GoLean.Loc.base { id := 8361 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "result", typ := GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" } },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "result"]
       { key := "quorum.JointConfig.VoteResult" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.fieldGet
             (GoLean.GoCore.Expr.deref
               (GoLean.GoCore.Expr.var "p")
               (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
             { key := "tracker.ProgressTracker" }
             "Config")
           { key := "tracker.Config" }
           "Voters",
         GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref
             (GoLean.GoCore.Expr.var "p")
             (GoLean.GoCore.Ty.defined { key := "tracker.ProgressTracker" }))
           { key := "tracker.ProgressTracker" }
           "Votes"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "granted") (GoLean.GoCore.Expr.var "granted"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "rejected") (GoLean.GoCore.Expr.var "rejected"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res2") (GoLean.GoCore.Expr.var "result"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[],
 [("$res2", GoLean.Loc.base { id := 8364 }),
  ("rejected", GoLean.Loc.base { id := 8363 }),
  ("granted", GoLean.Loc.base { id := 8362 }),
  ("p", GoLean.Loc.base { id := 8361 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1353"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1354"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1355"])]) ([[("$c1355", GoLean.Loc.base { id := 8360 }),
  ("$c1354", GoLean.Loc.base { id := 8359 }),
  ("$c1353", GoLean.Loc.base { id := 8358 })],
 [("result", GoLean.Loc.base { id := 8347 }),
  ("rejected", GoLean.Loc.base { id := 8346 }),
  ("granted", GoLean.Loc.base { id := 8345 }),
  ("v", GoLean.Loc.base { id := 8344 }),
  ("t", GoLean.Loc.base { id := 8343 }),
  ("id", GoLean.Loc.base { id := 8342 }),
  ("r", GoLean.Loc.base { id := 8341 })]]) ([GoLean.Loc.base { id := 8362 }, GoLean.Loc.base { id := 8363 }, GoLean.Loc.base { id := 8364 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "granted") (GoLean.GoCore.Expr.var "$c1353"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "rejected") (GoLean.GoCore.Expr.var "$c1354"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "result") (GoLean.GoCore.Expr.var "$c1355"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("$c1355", GoLean.Loc.base { id := 8360 }),
  ("$c1354", GoLean.Loc.base { id := 8359 }),
  ("$c1353", GoLean.Loc.base { id := 8358 })],
 [("result", GoLean.Loc.base { id := 8347 }),
  ("rejected", GoLean.Loc.base { id := 8346 }),
  ("granted", GoLean.Loc.base { id := 8345 }),
  ("v", GoLean.Loc.base { id := 8344 }),
  ("t", GoLean.Loc.base { id := 8343 }),
  ("id", GoLean.Loc.base { id := 8342 }),
  ("r", GoLean.Loc.base { id := 8341 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "gr"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "rj"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "res"])]) ([[("res", GoLean.Loc.base { id := 8340 }),
  ("rj", GoLean.Loc.base { id := 8339 }),
  ("gr", GoLean.Loc.base { id := 8338 }),
  ("$c1575", GoLean.Loc.base { id := 8335 }),
  ("$c1574", GoLean.Loc.base { id := 8332 }),
  ("$c1573", GoLean.Loc.base { id := 8329 })],
 [],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) ([GoLean.Loc.base { id := 8345 }, GoLean.Loc.base { id := 8346 }, GoLean.Loc.base { id := 8347 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "$c1576", typ := GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" } },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c1576"]
       { key := "raftpb.Message.GetType" }
       #[GoLean.GoCore.Expr.var "m"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization
       { id := "$c1577", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }) },
     GoLean.GoCore.Stmt.makeSlice
       (GoLean.GoCore.Assignee.var "$c1577")
       (GoLean.GoCore.Ty.interface { key := "any" })
       (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))
       (some (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
         (GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "r") (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
           { key := "raft.raft" }
           "id")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.var "gr")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })
         (GoLean.GoCore.Expr.var "$c1576")),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.indexAddr
           (GoLean.GoCore.Expr.var "$c1577")
           (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))))
       (GoLean.GoCore.Expr.toInterface
         (GoLean.GoCore.Ty.interface { key := "any" })
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.var "rj"))],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "raft.Logger.Infof" }
   #[GoLean.GoCore.Expr.fieldGet
       (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "r") (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
       { key := "raft.raft" }
       "logger",
     GoLean.GoCore.Expr.stringLit
       { bytes := #[37, 120, 32, 104, 97, 115, 32, 114, 101, 99, 101, 105, 118, 101, 100, 32, 37, 100, 32, 37, 115, 32,
                    118, 111, 116, 101, 115, 32, 97, 110, 100, 32, 37, 100, 32, 118, 111, 116, 101, 32, 114, 101, 106,
                    101, 99, 116, 105, 111, 110, 115] },
     GoLean.GoCore.Expr.var "$c1577"],
 GoLean.GoCore.Stmt.breakable
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$sw1578", typ := GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" } },
           GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$sw1578") (GoLean.GoCore.Expr.var "res")],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$swi1579", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
           GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))],
       GoLean.GoCore.Stmt.block
         #[]
         #[GoLean.GoCore.Stmt.ifThenElse
             (GoLean.GoCore.Expr.eqCmp
               (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })
               (GoLean.GoCore.Expr.var "$sw1578")
               (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.uint8)))
             (GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.var "$swi1579")
                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))])
             (GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.ifThenElse
                   (GoLean.GoCore.Expr.eqCmp
                     (GoLean.GoCore.Ty.defined { key := "quorum.VoteResult" })
                     (GoLean.GoCore.Expr.var "$sw1578")
                     (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint8)))
                   (GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.assign
                         (GoLean.GoCore.Assignee.var "$swi1579")
                         (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))])
                   (GoLean.GoCore.Stmt.seqn #[])])],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$swf1579", typ := GoLean.GoCore.Ty.bool },
           GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.or
           (GoLean.GoCore.Expr.var "$swf1579")
           (GoLean.GoCore.Expr.eqCmp
             (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
             (GoLean.GoCore.Expr.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
             GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.ifThenElse
                   (GoLean.GoCore.Expr.eqCmp
                     (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
                     (GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "r")
                         (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                       { key := "raft.raft" }
                       "state")
                     (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.uint64)))
                   (GoLean.GoCore.Stmt.block
                     #[]
                     #[GoLean.GoCore.Stmt.call
                         #[]
                         { key := "raft.raft.campaign" }
                         #[GoLean.GoCore.Expr.var "r",
                           GoLean.GoCore.Expr.stringLit
                             { bytes := #[67, 97, 109, 112, 97, 105, 103, 110, 69, 108, 101, 99, 116, 105, 111,
                                          110] }]])
                   (GoLean.GoCore.Stmt.block
                     #[]
                     #[GoLean.GoCore.Stmt.call #[] { key := "raft.raft.becomeLeader" } #[GoLean.GoCore.Expr.var "r"],
                       GoLean.GoCore.Stmt.call #[] { key := "raft.raft.bcastAppend" } #[GoLean.GoCore.Expr.var "r"]])]])
         (GoLean.GoCore.Stmt.seqn #[]),
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.or
           (GoLean.GoCore.Expr.var "$swf1579")
           (GoLean.GoCore.Expr.eqCmp
             (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
             (GoLean.GoCore.Expr.var "$swi1579")
             (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1579") (GoLean.GoCore.Expr.boolLit false)],
             GoLean.GoCore.Stmt.block
               #[]
               #[GoLean.GoCore.Stmt.call
                   #[]
                   { key := "raft.raft.becomeFollower" }
                   #[GoLean.GoCore.Expr.var "r",
                     GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "r")
                         (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                       { key := "raft.raft" }
                       "Term",
                     GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64)]]])
         (GoLean.GoCore.Stmt.seqn #[])])]) ([[("res", GoLean.Loc.base { id := 8340 }),
  ("rj", GoLean.Loc.base { id := 8339 }),
  ("gr", GoLean.Loc.base { id := 8338 }),
  ("$c1575", GoLean.Loc.base { id := 8335 }),
  ("$c1574", GoLean.Loc.base { id := 8332 }),
  ("$c1573", GoLean.Loc.base { id := 8329 })],
 [],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.or
     (GoLean.GoCore.Expr.var "$swf1582")
     (GoLean.GoCore.Expr.eqCmp
       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
       (GoLean.GoCore.Expr.var "$swi1582")
       (GoLean.GoCore.Expr.intLit 5 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$swf1582") (GoLean.GoCore.Expr.boolLit false)],
       GoLean.GoCore.Stmt.block
         #[]
         #[GoLean.GoCore.Stmt.seqn
             #[GoLean.GoCore.Stmt.initialization
                 { id := "$c1580", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
               GoLean.GoCore.Stmt.call
                 #[GoLean.GoCore.Assignee.var "$c1580"]
                 { key := "raftpb.Message.GetFrom" }
                 #[GoLean.GoCore.Expr.var "m"]],
           GoLean.GoCore.Stmt.seqn
             #[GoLean.GoCore.Stmt.initialization
                 { id := "$c1581", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.interface { key := "any" }) },
               GoLean.GoCore.Stmt.makeSlice
                 (GoLean.GoCore.Assignee.var "$c1581")
                 (GoLean.GoCore.Ty.interface { key := "any" })
                 (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))
                 (some (GoLean.GoCore.Expr.intLit 4 (GoLean.GoCore.IntKind.int))),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "id")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "Term")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "r")
                       (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                     { key := "raft.raft" }
                     "state")),
               GoLean.GoCore.Stmt.assign
                 (GoLean.GoCore.Assignee.addr
                   (GoLean.GoCore.Expr.indexAddr
                     (GoLean.GoCore.Expr.var "$c1581")
                     (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.toInterface
                   (GoLean.GoCore.Ty.interface { key := "any" })
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.var "$c1580"))],
           GoLean.GoCore.Stmt.call
             #[]
             { key := "raft.Logger.Debugf" }
             #[GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "r")
                   (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
                 { key := "raft.raft" }
                 "logger",
               GoLean.GoCore.Expr.stringLit
                 { bytes := #[37, 120, 32, 91, 116, 101, 114, 109, 32, 37, 100, 32, 115, 116, 97, 116, 101, 32, 37, 118,
                              93, 32, 105, 103, 110, 111, 114, 101, 100, 32, 77, 115, 103, 84, 105, 109, 101, 111, 117,
                              116, 78, 111, 119, 32, 102, 114, 111, 109, 32, 37, 120] },
               GoLean.GoCore.Expr.var "$c1581"]]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("$swf1582", GoLean.Loc.base { id := 8328 }),
  ("$swi1582", GoLean.Loc.base { id := 8327 }),
  ("$sw1565", GoLean.Loc.base { id := 8326 }),
  ("$c1564", GoLean.Loc.base { id := 8323 })],
 [("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.breakableK (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.nil none),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("myVoteRespType", GoLean.Loc.base { id := 8322 })],
 [("$res0", GoLean.Loc.base { id := 8321 }),
  ("m", GoLean.Loc.base { id := 8320 }),
  ("r", GoLean.Loc.base { id := 8319 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "err"])]) ([[("err", GoLean.Loc.base { id := 8318 })],
 [],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) ([GoLean.Loc.base { id := 8321 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.neqCmp
     (GoLean.GoCore.Ty.interface { key := "error" })
     (GoLean.GoCore.Expr.var "err")
     (GoLean.GoCore.Expr.nil none))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "err"),
           GoLean.GoCore.Stmt.returnStmt]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("err", GoLean.Loc.base { id := 8318 })],
 [],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$swf1467", GoLean.Loc.base { id := 8317 }),
  ("$swi1467", GoLean.Loc.base { id := 8316 }),
  ("$sw1419", GoLean.Loc.base { id := 8315 }),
  ("$c1418", GoLean.Loc.base { id := 8312 })],
 [],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.breakableK (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.nil none),
     GoLean.GoCore.Stmt.returnStmt]]) ([[],
 [("$res0", GoLean.Loc.base { id := 8298 }),
  ("m", GoLean.Loc.base { id := 8297 }),
  ("r", GoLean.Loc.base { id := 8296 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c1790"])]) ([[("$c1790", GoLean.Loc.base { id := 8295 }),
  ("$c1789", GoLean.Loc.base { id := 8291 }),
  ("$c1787", GoLean.Loc.base { id := 8284 }),
  ("$c1784", GoLean.Loc.base { id := 8276 }),
  ("$c1783", GoLean.Loc.base { id := 8273 }),
  ("$c1782", GoLean.Loc.base { id := 8272 }),
  ("$c1779", GoLean.Loc.base { id := 8264 }),
  ("$c1778", GoLean.Loc.base { id := 8261 })],
 [("$res0", GoLean.Loc.base { id := 8260 }),
  ("m", GoLean.Loc.base { id := 8259 }),
  ("rn", GoLean.Loc.base { id := 8258 })]]) ([GoLean.Loc.base { id := 8298 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "$c1790"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("$c1790", GoLean.Loc.base { id := 8295 }),
  ("$c1789", GoLean.Loc.base { id := 8291 }),
  ("$c1787", GoLean.Loc.base { id := 8284 }),
  ("$c1784", GoLean.Loc.base { id := 8276 }),
  ("$c1783", GoLean.Loc.base { id := 8273 }),
  ("$c1782", GoLean.Loc.base { id := 8272 }),
  ("$c1779", GoLean.Loc.base { id := 8264 }),
  ("$c1778", GoLean.Loc.base { id := 8261 })],
 [("$res0", GoLean.Loc.base { id := 8260 }),
  ("m", GoLean.Loc.base { id := 8259 }),
  ("rn", GoLean.Loc.base { id := 8258 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "err"])]) ([[("err", GoLean.Loc.base { id := 8257 })],
 [("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) ([GoLean.Loc.base { id := 8260 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.neqCmp
     (GoLean.GoCore.Ty.interface { key := "error" })
     (GoLean.GoCore.Expr.var "err")
     (GoLean.GoCore.Expr.nil none))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.stringLit { bytes := #[32, 115, 116, 101, 112, 101, 114, 114] }]])
   (GoLean.GoCore.Stmt.seqn #[])]) ([[("err", GoLean.Loc.base { id := 8257 })],
 [("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$cr0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$cr0"]
       { key := "main.twin.harvest" }
       #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "to"]]]) ([[("to", GoLean.Loc.base { id := 8256 }),
  ("$c2316", GoLean.Loc.base { id := 8253 }),
  ("m", GoLean.Loc.base { id := 8252 })],
 [("i", GoLean.Loc.base { id := 8251 }), ("t", GoLean.Loc.base { id := 8250 })]]) (GoLean.Sym.Cont.frame ([]) ([[("$c2241", GoLean.Loc.base { id := 8243 }),
  ("$c2240", GoLean.Loc.base { id := 8240 }),
  ("$c2239", GoLean.Loc.base { id := 8232 }),
  ("$c2238", GoLean.Loc.base { id := 8229 }),
  ("$c2237", GoLean.Loc.base { id := 8223 }),
  ("$c2236", GoLean.Loc.base { id := 8215 }),
  ("m", GoLean.Loc.base { id := 8214 }),
  ("picked", GoLean.Loc.base { id := 8212 })],
 [("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) ([]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2242", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2242"]
       { key := "main.twin.projection" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add (GoLean.GoCore.Expr.stringLit { bytes := #[32] }) (GoLean.GoCore.Expr.var "$c2242"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "stuckPropose")
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.continueStmt]) ([[("$c2241", GoLean.Loc.base { id := 8243 }),
  ("$c2240", GoLean.Loc.base { id := 8240 }),
  ("$c2239", GoLean.Loc.base { id := 8232 }),
  ("$c2238", GoLean.Loc.base { id := 8229 }),
  ("$c2237", GoLean.Loc.base { id := 8223 }),
  ("$c2236", GoLean.Loc.base { id := 8215 }),
  ("m", GoLean.Loc.base { id := 8214 }),
  ("picked", GoLean.Loc.base { id := 8212 })],
 [("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2243", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2243"]
       { key := "main.twin.complete" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.and
     (GoLean.GoCore.Expr.var "$c2243")
     (GoLean.GoCore.Expr.eqCmp
       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
       (GoLean.GoCore.Expr.length
         (GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "pending")
         (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.breakStmt])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.greaterCmp
     (GoLean.GoCore.Expr.length
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "pending")
       (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$c2244", typ := GoLean.GoCore.Ty.string },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2244"]
             { key := "itoa" }
             #[GoLean.GoCore.Expr.add
                 (GoLean.GoCore.Expr.var "round")
                 (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.add
             (GoLean.GoCore.Expr.add
               (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
               (GoLean.GoCore.Expr.var "$c2244"))
             (GoLean.GoCore.Expr.stringLit { bytes := #[32] })],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.step" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.structLit
             (GoLean.GoCore.Ty.defined { key := "main.op" })
             #[GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int),
               GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int),
               GoLean.GoCore.Expr.defaultValue (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.say" }
         #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.stringLit { bytes := #[10] }],
       GoLean.GoCore.Stmt.assign
         (GoLean.GoCore.Assignee.var "stuckPropose")
         (GoLean.GoCore.Expr.add
           (GoLean.GoCore.Expr.var "stuckPropose")
           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.greaterCmp
           (GoLean.GoCore.Expr.var "stuckPropose")
           (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int)))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.addr
                     (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                   (GoLean.GoCore.Expr.boolLit true)],
             GoLean.GoCore.Stmt.call
               #[]
               { key := "main.twin.say" }
               #[GoLean.GoCore.Expr.var "t",
                 GoLean.GoCore.Expr.stringLit
                   { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112, 111, 115, 101, 32, 115,
                                116, 117, 99, 107, 32, 97, 116, 32, 113, 117, 105, 101, 115, 99, 101, 110, 99, 101,
                                10] }],
             GoLean.GoCore.Stmt.breakStmt])
         (GoLean.GoCore.Stmt.seqn #[]),
       GoLean.GoCore.Stmt.continueStmt])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
       (GoLean.GoCore.Expr.boolLit true)],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.stringLit
       { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101, 110, 116, 32, 119, 105,
                    116, 104, 111, 117, 116, 32, 83, 52, 10] }],
 GoLean.GoCore.Stmt.breakStmt]) ([[("live", GoLean.Loc.base { id := 8206 }), ("$c2235", GoLean.Loc.base { id := 8204 })],
 [],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.loop (GoLean.GoCore.Expr.boolLit true) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "$forFirst")
      (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$forFirst") (GoLean.GoCore.Expr.boolLit false))
      (GoLean.GoCore.Stmt.assign
        (GoLean.GoCore.Assignee.var "round")
        (GoLean.GoCore.Expr.add
          (GoLean.GoCore.Expr.var "round")
          (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
    GoLean.GoCore.Stmt.seqn #[],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.lessCmp
        (GoLean.GoCore.Expr.var "round")
        (GoLean.GoCore.Expr.intLit 400 (GoLean.GoCore.IntKind.int)))
      (GoLean.GoCore.Stmt.seqn #[])
      (GoLean.GoCore.Stmt.breakStmt),
    GoLean.GoCore.Stmt.block
      #[]
      #[GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization
              { id := "$c2235",
                typ := GoLean.GoCore.Ty.map
                         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                         (GoLean.GoCore.Ty.bool) },
            GoLean.GoCore.Stmt.makeMap
              (GoLean.GoCore.Assignee.var "$c2235")
              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
              (GoLean.GoCore.Ty.bool)
              none],
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization
              { id := "live",
                typ := GoLean.GoCore.Ty.map
                         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                         (GoLean.GoCore.Ty.bool) },
            GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "live") (GoLean.GoCore.Expr.var "$c2235")],
        GoLean.GoCore.Stmt.block
          #[]
          #[GoLean.GoCore.Stmt.initialization
              { id := "$rcoll",
                typ := GoLean.GoCore.Ty.slice
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rcoll")
              (GoLean.GoCore.Expr.fieldGet
                (GoLean.GoCore.Expr.deref
                  (GoLean.GoCore.Expr.var "t")
                  (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                { key := "main.twin" }
                "net"),
            GoLean.GoCore.Stmt.initialization
              { id := "$rlen", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rlen")
              (GoLean.GoCore.Expr.length (GoLean.GoCore.Expr.var "$rcoll") none),
            GoLean.GoCore.Stmt.initialization
              { id := "$ridx", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$ridx")
              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)),
            GoLean.GoCore.Stmt.initialization { id := "$rfirst", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$rfirst") (GoLean.GoCore.Expr.boolLit true),
            GoLean.GoCore.Stmt.while
              (GoLean.GoCore.Expr.boolLit true)
              (GoLean.GoCore.Stmt.block
                #[]
                #[GoLean.GoCore.Stmt.ifThenElse
                    (GoLean.GoCore.Expr.var "$rfirst")
                    (GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "$rfirst")
                      (GoLean.GoCore.Expr.boolLit false))
                    (GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "$ridx")
                      (GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "$ridx")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))),
                  GoLean.GoCore.Stmt.ifThenElse
                    (GoLean.GoCore.Expr.atLeastCmp (GoLean.GoCore.Expr.var "$ridx") (GoLean.GoCore.Expr.var "$rlen"))
                    (GoLean.GoCore.Stmt.breakStmt)
                    (GoLean.GoCore.Stmt.seqn #[]),
                  GoLean.GoCore.Stmt.initialization
                    { id := "j", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                  GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "j") (GoLean.GoCore.Expr.var "$ridx"),
                  GoLean.GoCore.Stmt.block
                    #[]
                    #[GoLean.GoCore.Stmt.ifThenElse
                        (GoLean.GoCore.Expr.indexGet
                          (GoLean.GoCore.Expr.fieldGet
                            (GoLean.GoCore.Expr.deref
                              (GoLean.GoCore.Expr.var "t")
                              (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                            { key := "main.twin" }
                            "live")
                          (GoLean.GoCore.Expr.var "j"))
                        (GoLean.GoCore.Stmt.block
                          #[]
                          #[GoLean.GoCore.Stmt.mapAssign
                              (GoLean.GoCore.Expr.var "live")
                              (GoLean.GoCore.Expr.var "j")
                              (GoLean.GoCore.Expr.boolLit true)
                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                              (GoLean.GoCore.Ty.bool)])
                        (GoLean.GoCore.Stmt.seqn #[])]])],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.length
              (GoLean.GoCore.Expr.var "live")
              (some (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)) (GoLean.GoCore.Ty.bool))))
            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "picked", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "picked")
                    (GoLean.GoCore.Expr.intLit (-1) (GoLean.GoCore.IntKind.int))],
              GoLean.GoCore.Stmt.mapRange
                (some "j")
                none
                (GoLean.GoCore.Expr.var "live")
                (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                (GoLean.GoCore.Ty.bool)
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "picked") (GoLean.GoCore.Expr.var "j")],
                    GoLean.GoCore.Stmt.breakStmt]),
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "m",
                      typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "m")
                    (GoLean.GoCore.Expr.indexGet
                      (GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "t")
                          (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                        { key := "main.twin" }
                        "net")
                      (GoLean.GoCore.Expr.var "picked"))],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2236", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2236"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "round")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2237", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2237"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.var "picked"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2238", typ := GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" } },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2238"]
                    { key := "raftpb.Message.GetType" }
                    #[GoLean.GoCore.Expr.var "m"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2239", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2239"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.convert
                        (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                        (GoLean.GoCore.Expr.var "$c2238")]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2240", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2240"]
                    { key := "raftpb.Message.GetTo" }
                    #[GoLean.GoCore.Expr.var "m"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2241", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2241"]
                    { key := "utoa" }
                    #[GoLean.GoCore.Expr.var "$c2240"]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.add
                          (GoLean.GoCore.Expr.add
                            (GoLean.GoCore.Expr.add
                              (GoLean.GoCore.Expr.add
                                (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
                                (GoLean.GoCore.Expr.var "$c2236"))
                              (GoLean.GoCore.Expr.stringLit { bytes := #[32, 112, 105, 99, 107, 35] }))
                            (GoLean.GoCore.Expr.var "$c2237"))
                          (GoLean.GoCore.Expr.stringLit { bytes := #[32, 116, 121, 112, 101] }))
                        (GoLean.GoCore.Expr.var "$c2239"))
                      (GoLean.GoCore.Expr.stringLit { bytes := #[45, 62] }))
                    (GoLean.GoCore.Expr.var "$c2241")],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.deliverIdx" }
                #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "picked"],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2242", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2242"]
                    { key := "main.twin.projection" }
                    #[GoLean.GoCore.Expr.var "t"]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.stringLit { bytes := #[32] })
                      (GoLean.GoCore.Expr.var "$c2242"))
                    (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "stuckPropose")
                    (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
              GoLean.GoCore.Stmt.continueStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "$c2243", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c2243"]
              { key := "main.twin.complete" }
              #[GoLean.GoCore.Expr.var "t"]],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.and
            (GoLean.GoCore.Expr.var "$c2243")
            (GoLean.GoCore.Expr.eqCmp
              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
              (GoLean.GoCore.Expr.length
                (GoLean.GoCore.Expr.fieldGet
                  (GoLean.GoCore.Expr.deref
                    (GoLean.GoCore.Expr.var "t")
                    (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                  { key := "main.twin" }
                  "pending")
                (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
          (GoLean.GoCore.Stmt.block #[] #[GoLean.GoCore.Stmt.breakStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.length
              (GoLean.GoCore.Expr.fieldGet
                (GoLean.GoCore.Expr.deref
                  (GoLean.GoCore.Expr.var "t")
                  (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                { key := "main.twin" }
                "pending")
              (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "$c2244", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2244"]
                    { key := "itoa" }
                    #[GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.var "round")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.add
                    (GoLean.GoCore.Expr.add
                      (GoLean.GoCore.Expr.stringLit { bytes := #[114] })
                      (GoLean.GoCore.Expr.var "$c2244"))
                    (GoLean.GoCore.Expr.stringLit { bytes := #[32] })],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.step" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.structLit
                    (GoLean.GoCore.Ty.defined { key := "main.op" })
                    #[GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.int),
                      GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int),
                      GoLean.GoCore.Expr.defaultValue (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.stringLit { bytes := #[10] }],
              GoLean.GoCore.Stmt.assign
                (GoLean.GoCore.Assignee.var "stuckPropose")
                (GoLean.GoCore.Expr.add
                  (GoLean.GoCore.Expr.var "stuckPropose")
                  (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.greaterCmp
                  (GoLean.GoCore.Expr.var "stuckPropose")
                  (GoLean.GoCore.Expr.intLit 3 (GoLean.GoCore.IntKind.int)))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.addr
                            (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                          (GoLean.GoCore.Expr.boolLit true)],
                    GoLean.GoCore.Stmt.call
                      #[]
                      { key := "main.twin.say" }
                      #[GoLean.GoCore.Expr.var "t",
                        GoLean.GoCore.Expr.stringLit
                          { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112, 111, 115, 101, 32,
                                       115, 116, 117, 99, 107, 32, 97, 116, 32, 113, 117, 105, 101, 115, 99, 101, 110,
                                       99, 101, 10] }],
                    GoLean.GoCore.Stmt.breakStmt])
                (GoLean.GoCore.Stmt.seqn #[]),
              GoLean.GoCore.Stmt.continueStmt])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.addr
                (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
              (GoLean.GoCore.Expr.boolLit true)],
        GoLean.GoCore.Stmt.call
          #[]
          { key := "main.twin.say" }
          #[GoLean.GoCore.Expr.var "t",
            GoLean.GoCore.Expr.stringLit
              { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101, 110, 116, 32,
                           119, 105, 116, 104, 111, 117, 116, 32, 83, 52, 10] }],
        GoLean.GoCore.Stmt.breakStmt]]) ([[("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$forFirst", GoLean.Loc.base { id := 6072 })],
 [],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "comp", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "comp")
       (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2245", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2245"]
       { key := "main.twin.complete" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.and
     (GoLean.GoCore.Expr.and
       (GoLean.GoCore.Expr.var "$c2245")
       (GoLean.GoCore.Expr.eqCmp
         (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
         (GoLean.GoCore.Expr.length
           (GoLean.GoCore.Expr.fieldGet
             (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
             { key := "main.twin" }
             "pending")
           (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
     (GoLean.GoCore.Expr.not
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "halt")))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "comp")
             (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "floorOK", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "floorOK")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.or
     (GoLean.GoCore.Expr.lessCmp
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "claims")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))
     (GoLean.GoCore.Expr.lessCmp
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "committed")
       (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "floorOK")
             (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2246", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2246"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "violations"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2247", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2247"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "claims"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2248", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2248"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.fieldGet
           (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
           { key := "main.twin" }
           "committed"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2249", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call #[GoLean.GoCore.Assignee.var "$c2249"] { key := "itoa" } #[GoLean.GoCore.Expr.var "comp"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2250", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2250"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.var "floorOK"]],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2251", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2251"]
       { key := "itoa" }
       #[GoLean.GoCore.Expr.var "round"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add
         (GoLean.GoCore.Expr.add
           (GoLean.GoCore.Expr.add
             (GoLean.GoCore.Expr.add
               (GoLean.GoCore.Expr.add
                 (GoLean.GoCore.Expr.add
                   (GoLean.GoCore.Expr.add
                     (GoLean.GoCore.Expr.add
                       (GoLean.GoCore.Expr.add
                         (GoLean.GoCore.Expr.add
                           (GoLean.GoCore.Expr.add
                             (GoLean.GoCore.Expr.stringLit { bytes := #[101, 110, 100, 32, 118, 105, 111, 108, 61] })
                             (GoLean.GoCore.Expr.var "$c2246"))
                           (GoLean.GoCore.Expr.stringLit { bytes := #[32, 99, 108, 97, 105, 109, 115, 61] }))
                         (GoLean.GoCore.Expr.var "$c2247"))
                       (GoLean.GoCore.Expr.stringLit
                         { bytes := #[32, 99, 111, 109, 109, 105, 116, 116, 101, 100, 61] }))
                     (GoLean.GoCore.Expr.var "$c2248"))
                   (GoLean.GoCore.Expr.stringLit { bytes := #[32, 99, 111, 109, 112, 108, 101, 116, 101, 61] }))
                 (GoLean.GoCore.Expr.var "$c2249"))
               (GoLean.GoCore.Expr.stringLit { bytes := #[32, 102, 108, 111, 111, 114, 61] }))
             (GoLean.GoCore.Expr.var "$c2250"))
           (GoLean.GoCore.Expr.stringLit { bytes := #[32, 114, 111, 117, 110, 100, 115, 61] }))
         (GoLean.GoCore.Expr.var "$c2251"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2252", typ := GoLean.GoCore.Ty.string },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2252"]
       { key := "main.twin.projection" }
       #[GoLean.GoCore.Expr.var "t"]],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "main.twin.say" }
   #[GoLean.GoCore.Expr.var "t",
     GoLean.GoCore.Expr.add
       (GoLean.GoCore.Expr.add
         (GoLean.GoCore.Expr.stringLit { bytes := #[102, 105, 110, 97, 108, 32] })
         (GoLean.GoCore.Expr.var "$c2252"))
       (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "t"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res1") (GoLean.GoCore.Expr.var "comp"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res2") (GoLean.GoCore.Expr.var "floorOK"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("stuckPropose", GoLean.Loc.base { id := 6071 }),
  ("round", GoLean.Loc.base { id := 6070 }),
  ("t", GoLean.Loc.base { id := 110 })],
 [("$res2", GoLean.Loc.base { id := 108 }),
  ("$res1", GoLean.Loc.base { id := 107 }),
  ("$res0", GoLean.Loc.base { id := 106 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "t"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "comp"]),
 (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "floorOK"])]) ([[("floorOK", GoLean.Loc.base { id := 105 }),
  ("comp", GoLean.Loc.base { id := 104 }),
  ("t", GoLean.Loc.base { id := 103 })],
 [("$res4", GoLean.Loc.base { id := 102 }),
  ("$res3", GoLean.Loc.base { id := 101 }),
  ("$res2", GoLean.Loc.base { id := 100 }),
  ("$res1", GoLean.Loc.base { id := 99 }),
  ("$res0", GoLean.Loc.base { id := 98 })]]) ([GoLean.Loc.base { id := 106 }, GoLean.Loc.base { id := 107 }, GoLean.Loc.base { id := 108 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res0")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "violations"),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res1")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "claims"),
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$res2")
       (GoLean.GoCore.Expr.fieldGet
         (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "t") (GoLean.GoCore.Ty.defined { key := "main.twin" }))
         { key := "main.twin" }
         "committed"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res3") (GoLean.GoCore.Expr.var "comp"),
     GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res4") (GoLean.GoCore.Expr.var "floorOK"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("floorOK", GoLean.Loc.base { id := 105 }),
  ("comp", GoLean.Loc.base { id := 104 }),
  ("t", GoLean.Loc.base { id := 103 })],
 [("$res4", GoLean.Loc.base { id := 102 }),
  ("$res3", GoLean.Loc.base { id := 101 }),
  ("$res2", GoLean.Loc.base { id := 100 }),
  ("$res1", GoLean.Loc.base { id := 99 }),
  ("$res0", GoLean.Loc.base { id := 98 })]]) (GoLean.Sym.Cont.frame ([]) ([]) ([]) [] (GoLean.Sym.Cont.stop) false)) false)))))))) false))) false)) false)))))) false)))))) false)) false))))

end GoLean.RaftSeam.RoundVr
