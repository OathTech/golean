import GoLeanProofs.Sym.Mirror

/-! # RingLit1 — GENERATED literals (A4-U21 C2c; generator
`artifacts/probe/MsgAppRingGen.lean` — DO NOT EDIT BY HAND; the W1 assembly window: ring steps 0-3327, crossing X1).

The MsgApp append-family ROUND fixture's harvest-ring segment (ring
step 0 = the `main.twin.harvest` call, 7,425 steps into the round;
13,870 ring steps to the `main.twin.projection` call), pruned to the
ring's own 27-cell read-before-write footprint, MIRROR-PROPAGATED
THROUGH THE CROSSINGS (states carry unreduced SymInt trees — the
mirror does no constant folding; γ evaluates them; crossing posts are
set/append values over the pre-states, so a crossing's untouched
cells are the SAME terms on both sides and its kernel check never
γ-evaluates a tree — the reflect-reset form's tree-vs-literal
comparison measured out at >46 min/crossing). γ-fidelity against the
machine walk was generator-verified at every boundary AND at every
crossing post; the window LINK theorems in `RingEqW*.lean` (kernel
rfl) re-check every literal against the mirror — the drift alarms.
Split into four files for parallel elaboration (4.4 MB total). -/

namespace GoLean.RaftSeam.Ring

open GoLean GoLean.GoCore GoLean.Sym

set_option maxRecDepth 8000000

def maS0 : SymState :=
  (GoLean.Sym.State.mk
  [((GoLean.Loc.base { id := 15 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 57 })))),
  ((GoLean.Loc.base { id := 57 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Commit"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 121 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twin" })) (GoLean.Sym.Value.struct ({ key := "main.twin" }) #[(("nodes"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 1764 }), offset := 0, len := 3, cap := 4 }))),
  (("net"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6077 }), offset := 0, len := 1, cap := 1 }))),
  (("live"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6078 }), offset := 0, len := 1, cap := 1 }))),
  (("leaderOf"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 115 }) }))),
  (("byIndex"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 118 }) }))),
  (("claims"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("violations"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("pending"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 136 }), offset := 0, len := 2, cap := 4 }))),
  (("driven"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("seq"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.int))),
  (("trace"), (GoLean.Sym.Value.string ({ bytes := #[91, 99, 104, 111, 105, 99, 101, 45, 100, 114, 105, 118, 101, 110, 93, 10, 99, 97, 109, 112, 97, 105, 103,
             110, 49, 114, 49, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 51, 45, 62, 50] }))),
  (("halt"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1770 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1767 }) })))]))),
  ((GoLean.Loc.base { id := 1779 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.struct ({ key := "raft.MemoryStorage" }) #[(("Mutex"), (GoLean.Sym.Value.syncData (GoLean.SyncPrim.mutex false))),
  (("hardState"), (GoLean.Sym.Value.nil)),
  (("snapshot"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1858 }))),
  (("ents"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 1900 }), offset := 0, len := 1, cap := 1 }))),
  (("callStats"), (GoLean.Sym.Value.struct ({ key := "raft.inMemStorageCallStats" }) #[(("initialState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("firstIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 4) (GoLean.GoCore.IntKind.int))),
  (("lastIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("entries"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.int))),
  (("snapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))]))]))),
  ((GoLean.Loc.base { id := 1895 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 1898 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1886 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1895 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 1900 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1898 }))]))),
  ((GoLean.Loc.base { id := 1949 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })) (GoLean.Sym.Value.struct ({ key := "raft.raftLog" }) #[(("storage"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 })))),
  (("unstable"), (GoLean.Sym.Value.struct ({ key := "raft.unstable" }) #[(("snapshot"), (GoLean.Sym.Value.nil)),
  (("entries"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 }))),
  (("offset"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("snapshotInProgress"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("offsetInProgress"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 }))))])),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("applying"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("maxApplyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1989 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raft" })) (GoLean.Sym.Value.struct ({ key := "raft.raft" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("Term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("Vote"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("readStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("raftLog"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 }))),
  (("maxMsgSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("maxUncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64))),
  (("trk"), (GoLean.Sym.Value.struct ({ key := "tracker.ProgressTracker" }) #[(("Config"), (GoLean.Sym.Value.struct ({ key := "tracker.Config" }) #[(("Voters"), (GoLean.Sym.Value.array #[(GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 2686 }) })),
  (GoLean.Sym.Value.map ({ base := none }))])),
  (("AutoLeave"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Learners"), (GoLean.Sym.Value.map ({ base := none }))),
  (("LearnersNext"), (GoLean.Sym.Value.map ({ base := none })))])),
  (("Progress"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 2703 }) }))),
  (("Votes"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 3059 }) }))),
  (("MaxInflight"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 256) (GoLean.GoCore.IntKind.int))),
  (("MaxInflightBytes"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64)))])),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("isLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("msgs"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("msgsAfterAppend"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6499 }), offset := 0, len := 1, cap := 4 }))),
  (("lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("leadTransferee"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("pendingConfIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("disableConfChangeValidation"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("uncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("readOnly"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3199 }))),
  (("electionElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("heartbeatElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("checkQuorum"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("preVote"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("heartbeatTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("electionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("randomizedElectionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("disableProposalForwarding"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("stepDownOnRemoval"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("tick"), (GoLean.Sym.Value.funcVal ({ key := "raft.raft.tickElection" }) [(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 }))])),
  (("step"), (GoLean.Sym.Value.funcVal ({ key := "raft.stepFollower" }) [])),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("pendingReadIndexMessages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("traceLogger"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 3342 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })) (GoLean.Sym.Value.struct ({ key := "raft.RawNode" }) #[(("raft"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 }))),
  (("asyncStorageWrites"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("prevSoftSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3344 }))),
  (("prevHardSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 }))),
  (("stepsOnAdvance"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 3344 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 3351 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 3354 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 3357 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 3360 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3351 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3354 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3357 })))]))),
  ((GoLean.Loc.base { id := 6075 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6077 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6076 }))]))),
  ((GoLean.Loc.base { id := 6078 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))]))),
  ((GoLean.Loc.base { id := 6080 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6081 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6082 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6080 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6081 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 6132 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 6138 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1770 })))),
  ((GoLean.Loc.base { id := 6424 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 })),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 6456 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Message" }) #[(("Type"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6449 }))),
  (("To"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6075 }))),
  (("From"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6463 }))),
  (("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6490 }))),
  (("LogTerm"), (GoLean.Sym.Value.nil)),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6453 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Commit"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("Reject"), (GoLean.Sym.Value.nil)),
  (("RejectHint"), (GoLean.Sym.Value.nil)),
  (("Context"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Responses"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 6499 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 })),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)])))]
  6503)

def maC0 : SymConfig :=
  (GoLean.Sym.Config.exec (GoLean.GoCore.Stmt.call
  #[GoLean.GoCore.Assignee.var "$cr0"]
  { key := "main.twin.harvest" }
  #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "to"]) ([[("$cr0", GoLean.Loc.base { id := 6502 }),
  ("to", GoLean.Loc.base { id := 6138 }),
  ("$c2316", GoLean.Loc.base { id := 6135 }),
  ("m", GoLean.Loc.base { id := 6134 })],
 [("i", GoLean.Loc.base { id := 6133 }), ("t", GoLean.Loc.base { id := 6132 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$cr0", GoLean.Loc.base { id := 6502 }),
  ("to", GoLean.Loc.base { id := 6138 }),
  ("$c2316", GoLean.Loc.base { id := 6135 }),
  ("m", GoLean.Loc.base { id := 6134 })],
 [("i", GoLean.Loc.base { id := 6133 }), ("t", GoLean.Loc.base { id := 6132 })]]) (GoLean.Sym.Cont.frame ([]) ([[("$c2241", GoLean.Loc.base { id := 6125 }),
  ("$c2240", GoLean.Loc.base { id := 6122 }),
  ("$c2239", GoLean.Loc.base { id := 6114 }),
  ("$c2238", GoLean.Loc.base { id := 6111 }),
  ("$c2237", GoLean.Loc.base { id := 6105 }),
  ("$c2236", GoLean.Loc.base { id := 6097 }),
  ("m", GoLean.Loc.base { id := 6096 }),
  ("picked", GoLean.Loc.base { id := 6094 })],
 [("live", GoLean.Loc.base { id := 6088 }), ("$c2235", GoLean.Loc.base { id := 6086 })],
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
 GoLean.GoCore.Stmt.continueStmt]) ([[("$c2241", GoLean.Loc.base { id := 6125 }),
  ("$c2240", GoLean.Loc.base { id := 6122 }),
  ("$c2239", GoLean.Loc.base { id := 6114 }),
  ("$c2238", GoLean.Loc.base { id := 6111 }),
  ("$c2237", GoLean.Loc.base { id := 6105 }),
  ("$c2236", GoLean.Loc.base { id := 6097 }),
  ("m", GoLean.Loc.base { id := 6096 }),
  ("picked", GoLean.Loc.base { id := 6094 })],
 [("live", GoLean.Loc.base { id := 6088 }), ("$c2235", GoLean.Loc.base { id := 6086 })],
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
 GoLean.GoCore.Stmt.breakStmt]) ([[("live", GoLean.Loc.base { id := 6088 }), ("$c2235", GoLean.Loc.base { id := 6086 })],
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
  ("$res0", GoLean.Loc.base { id := 98 })]]) (GoLean.Sym.Cont.frame ([]) ([]) ([]) [] (GoLean.Sym.Cont.stop) false)) false)))))))) false)))

def maSP1a : SymState :=
  (GoLean.Sym.State.mk
  [((GoLean.Loc.base { id := 15 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 57 })))),
  ((GoLean.Loc.base { id := 57 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Commit"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 121 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twin" })) (GoLean.Sym.Value.struct ({ key := "main.twin" }) #[(("nodes"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 1764 }), offset := 0, len := 3, cap := 4 }))),
  (("net"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6077 }), offset := 0, len := 1, cap := 1 }))),
  (("live"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6078 }), offset := 0, len := 1, cap := 1 }))),
  (("leaderOf"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 115 }) }))),
  (("byIndex"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 118 }) }))),
  (("claims"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("violations"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("pending"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 136 }), offset := 0, len := 2, cap := 4 }))),
  (("driven"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("seq"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.int))),
  (("trace"), (GoLean.Sym.Value.string ({ bytes := #[91, 99, 104, 111, 105, 99, 101, 45, 100, 114, 105, 118, 101, 110, 93, 10, 99, 97, 109, 112, 97, 105, 103,
             110, 49, 114, 49, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 51, 45, 62, 50] }))),
  (("halt"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1770 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1767 }) })))]))),
  ((GoLean.Loc.base { id := 1779 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.struct ({ key := "raft.MemoryStorage" }) #[(("Mutex"), (GoLean.Sym.Value.syncData (GoLean.SyncPrim.mutex false))),
  (("hardState"), (GoLean.Sym.Value.nil)),
  (("snapshot"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1858 }))),
  (("ents"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 1900 }), offset := 0, len := 1, cap := 1 }))),
  (("callStats"), (GoLean.Sym.Value.struct ({ key := "raft.inMemStorageCallStats" }) #[(("initialState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int))),
  (("firstIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.add
        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 4))
        (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.int))),
  (("lastIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 10)))) (GoLean.GoCore.IntKind.int))),
  (("entries"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.int))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.int))),
  (("snapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.int)))]))]))),
  ((GoLean.Loc.base { id := 1895 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 1898 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1886 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1895 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 1900 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1898 }))]))),
  ((GoLean.Loc.base { id := 1949 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })) (GoLean.Sym.Value.struct ({ key := "raft.raftLog" }) #[(("storage"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 })))),
  (("unstable"), (GoLean.Sym.Value.struct ({ key := "raft.unstable" }) #[(("snapshot"), (GoLean.Sym.Value.nil)),
  (("entries"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 }))),
  (("offset"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("snapshotInProgress"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("offsetInProgress"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 }))))])),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("applying"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("maxApplyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1989 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raft" })) (GoLean.Sym.Value.struct ({ key := "raft.raft" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("Term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("Vote"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("readStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("raftLog"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 }))),
  (("maxMsgSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("maxUncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64))),
  (("trk"), (GoLean.Sym.Value.struct ({ key := "tracker.ProgressTracker" }) #[(("Config"), (GoLean.Sym.Value.struct ({ key := "tracker.Config" }) #[(("Voters"), (GoLean.Sym.Value.array #[(GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 2686 }) })),
  (GoLean.Sym.Value.map ({ base := none }))])),
  (("AutoLeave"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Learners"), (GoLean.Sym.Value.map ({ base := none }))),
  (("LearnersNext"), (GoLean.Sym.Value.map ({ base := none })))])),
  (("Progress"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 2703 }) }))),
  (("Votes"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 3059 }) }))),
  (("MaxInflight"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 256) (GoLean.GoCore.IntKind.int))),
  (("MaxInflightBytes"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64)))])),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("isLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("msgs"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("msgsAfterAppend"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6499 }), offset := 0, len := 1, cap := 4 }))),
  (("lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("leadTransferee"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("pendingConfIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("disableConfChangeValidation"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("uncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("readOnly"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3199 }))),
  (("electionElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("heartbeatElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("checkQuorum"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("preVote"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("heartbeatTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("electionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("randomizedElectionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("disableProposalForwarding"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("stepDownOnRemoval"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("tick"), (GoLean.Sym.Value.funcVal ({ key := "raft.raft.tickElection" }) [(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 }))])),
  (("step"), (GoLean.Sym.Value.funcVal ({ key := "raft.stepFollower" }) [])),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("pendingReadIndexMessages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("traceLogger"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 3342 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })) (GoLean.Sym.Value.struct ({ key := "raft.RawNode" }) #[(("raft"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 }))),
  (("asyncStorageWrites"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("prevSoftSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3344 }))),
  (("prevHardSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 }))),
  (("stepsOnAdvance"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 3344 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 3351 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 3354 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 3357 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 3360 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3351 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3354 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3357 })))]))),
  ((GoLean.Loc.base { id := 6075 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6077 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6076 }))]))),
  ((GoLean.Loc.base { id := 6078 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))]))),
  ((GoLean.Loc.base { id := 6080 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6081 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6082 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6080 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6081 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 6132 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 6138 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1770 })))),
  ((GoLean.Loc.base { id := 6424 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 })),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 6456 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Message" }) #[(("Type"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6449 }))),
  (("To"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6075 }))),
  (("From"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6463 }))),
  (("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6490 }))),
  (("LogTerm"), (GoLean.Sym.Value.nil)),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6453 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Commit"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("Reject"), (GoLean.Sym.Value.nil)),
  (("RejectHint"), (GoLean.Sym.Value.nil)),
  (("Context"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Responses"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 6499 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 })),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 6503 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 6504 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1770 })))),
  ((GoLean.Loc.base { id := 6505 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6506 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6507 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6508 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6509 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 })))),
  ((GoLean.Loc.base { id := 6510 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6511 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6512 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6513 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6514 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6515 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6516 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6512 })))),
  ((GoLean.Loc.base { id := 6517 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3344 })))),
  ((GoLean.Loc.base { id := 6518 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6519 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.nil)),
  (("HardState"), (GoLean.Sym.Value.nil)),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 6520 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 })))),
  ((GoLean.Loc.base { id := 6521 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.nil)),
  (("HardState"), (GoLean.Sym.Value.nil)),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 6522 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.nil)),
  (("HardState"), (GoLean.Sym.Value.nil)),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 6523 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 })))),
  ((GoLean.Loc.base { id := 6524 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.nil)),
  (("HardState"), (GoLean.Sym.Value.nil)),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 6525 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6526 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6527 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6528 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6529 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6530 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6531 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6532 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.sub (GoLean.Sym.SymInt.lit 2) (GoLean.Sym.SymInt.lit 2))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6533 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6534 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 6535 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 })))),
  ((GoLean.Loc.base { id := 6536 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 6537 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6538 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6539 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 6540 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6541 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit true))))),
  ((GoLean.Loc.base { id := 6542 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6543 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit true))))),
  ((GoLean.Loc.base { id := 6544 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6545 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6546 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 6547 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6548 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6549 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6550 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6551 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.entryEncodingSize" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.sub (GoLean.Sym.SymInt.lit 1048576) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6552 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6553 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6554 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6555 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.add
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
        (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6556 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.entryEncodingSize" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.sub (GoLean.Sym.SymInt.lit 1048576) (GoLean.Sym.SymInt.lit 0))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6557 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6558 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6559 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6560 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6561 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6562 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
          (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6563 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6564 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.uint64)
                  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
                (GoLean.Sym.SymInt.lit 1))))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6565 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6566 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
              (GoLean.Sym.SymInt.lit 1)))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6567 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6568 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6569 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6570 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6571 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6572 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
            (GoLean.Sym.SymInt.lit 1))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6573 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6574 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 })))),
  ((GoLean.Loc.base { id := 6575 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
          (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6576 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6577 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.add
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
        (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6578 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 })))),
  ((GoLean.Loc.base { id := 6579 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6580 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6581 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1898 })))),
  ((GoLean.Loc.base { id := 6582 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6583 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.sync (GoLean.GoCore.SyncKind.mutex)))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1779 }) { key := "raft.MemoryStorage" } "Mutex")))),
  ((GoLean.Loc.base { id := 6584 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.sub
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.lit 2)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.uint64)
                  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
            (GoLean.Sym.SymInt.lit 1))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6585 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6586 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.sub
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.lit 2)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
          (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6587 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.sub
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.lit 2)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
        (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6588 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6589 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6590 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.sub
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.lit 2)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6591 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6592 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6593 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.sub
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.uint64)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.uint64)
                    (GoLean.Sym.SymInt.sub
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.uint64)
                        (GoLean.Sym.SymInt.add
                          (GoLean.Sym.SymInt.lit 2)
                          (GoLean.Sym.SymInt.norm
                            (GoLean.GoCore.IntKind.uint64)
                            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
                      (GoLean.Sym.SymInt.lit 1)))))))
          (GoLean.Sym.SymInt.lit 1)))
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.uint64)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.uint64)
                    (GoLean.Sym.SymInt.add
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.uint64)
                        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
                      (GoLean.Sym.SymInt.lit 1)))))))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6594 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6595 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6596 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6597 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
          (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6598 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6599 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6600 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6601 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
            (GoLean.Sym.SymInt.lit 1))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6602 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.lit 2)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6603 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6604 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6605 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.entryEncodingSize" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.sub (GoLean.Sym.SymInt.lit 1048576) (GoLean.Sym.SymInt.lit 0)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6606 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6607 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.add
                    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.add
                        (GoLean.Sym.SymInt.lit 1)
                        (GoLean.Sym.SymInt.norm
                          (GoLean.GoCore.IntKind.int)
                          (GoLean.Sym.SymInt.norm
                            (GoLean.GoCore.IntKind.int)
                            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.add
                  (GoLean.Sym.SymInt.lit 1)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))))))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6608 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "proto.Message" })) (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 }))))),
  ((GoLean.Loc.base { id := 6609 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.add
                  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.add
                      (GoLean.Sym.SymInt.lit 1)
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.int)
                        (GoLean.Sym.SymInt.norm
                          (GoLean.GoCore.IntKind.int)
                          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.lit 1)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6610 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "proto.Message" })) (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 }))))),
  ((GoLean.Loc.base { id := 6611 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 })))),
  ((GoLean.Loc.base { id := 6612 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6613 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 })))),
  ((GoLean.Loc.base { id := 6614 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.add
                    (GoLean.Sym.SymInt.lit 1)
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.int)
                        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.lit 1)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6615 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 })))),
  ((GoLean.Loc.base { id := 6616 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.add
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.add
                  (GoLean.Sym.SymInt.lit 1)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.lit 1)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6617 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.lit 1)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.lit 1)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6618 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6619 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6620 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6621 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6622 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6623 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6624 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6625 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6626 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6627 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6628 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.entryEncodingSize" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.add
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.add
                        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
                        (GoLean.Sym.SymInt.norm
                          (GoLean.GoCore.IntKind.int)
                          (GoLean.Sym.SymInt.add
                            (GoLean.Sym.SymInt.lit 1)
                            (GoLean.Sym.SymInt.norm
                              (GoLean.GoCore.IntKind.int)
                              (GoLean.Sym.SymInt.norm
                                (GoLean.GoCore.IntKind.int)
                                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.add
                      (GoLean.Sym.SymInt.lit 1)
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.int)
                        (GoLean.Sym.SymInt.norm
                          (GoLean.GoCore.IntKind.int)
                          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))))))))))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6629 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6630 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6631 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6632 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6640 }))),
  (("HardState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 }))),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))]))),
  ((GoLean.Loc.base { id := 6633 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6634 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6635 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6636 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6637 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6633 })))),
  ((GoLean.Loc.base { id := 6638 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3344 })))),
  ((GoLean.Loc.base { id := 6639 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6640 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6641 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6642 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6643 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6644 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6645 })))),
  ((GoLean.Loc.base { id := 6645 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6646 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6645 })))),
  ((GoLean.Loc.base { id := 6647 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6648 })))),
  ((GoLean.Loc.base { id := 6648 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6649 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6648 })))),
  ((GoLean.Loc.base { id := 6650 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6651 })))),
  ((GoLean.Loc.base { id := 6651 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6652 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6651 })))),
  ((GoLean.Loc.base { id := 6653 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6654 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6645 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6648 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6651 })))]))),
  ((GoLean.Loc.base { id := 6655 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.eqI
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))))),
  ((GoLean.Loc.base { id := 6656 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6657 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6658 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.eqI
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))))),
  ((GoLean.Loc.base { id := 6659 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6660 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6661 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6662 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6663 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6664 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6665 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.eqI
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)))
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))))))),
  ((GoLean.Loc.base { id := 6666 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6667 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6668 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6669 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6670 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6671 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6672 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.eqI
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))))),
  ((GoLean.Loc.base { id := 6673 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6674 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6675 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6676 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6677 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6678 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6679 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit true))))),
  ((GoLean.Loc.base { id := 6680 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6681 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit true))))),
  ((GoLean.Loc.base { id := 6682 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" }))) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6683 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6684 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" }))) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6685 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6698 })))),
  ((GoLean.Loc.base { id := 6686 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6687 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6698 })))),
  ((GoLean.Loc.base { id := 6688 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6689 })))),
  ((GoLean.Loc.base { id := 6689 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6690 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6689 })))),
  ((GoLean.Loc.base { id := 6691 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6692 })))),
  ((GoLean.Loc.base { id := 6692 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6693 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6692 })))),
  ((GoLean.Loc.base { id := 6694 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6695 })))),
  ((GoLean.Loc.base { id := 6695 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6696 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6695 })))),
  ((GoLean.Loc.base { id := 6697 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6698 })))),
  ((GoLean.Loc.base { id := 6698 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6689 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6692 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6695 })))]))),
  ((GoLean.Loc.base { id := 6699 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))),
  ((GoLean.Loc.base { id := 6700 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6698 })))),
  ((GoLean.Loc.base { id := 6701 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6702 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6703 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))),
  ((GoLean.Loc.base { id := 6704 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))),
  ((GoLean.Loc.base { id := 6705 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))),
  ((GoLean.Loc.base { id := 6706 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6499 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6707 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6708 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6709 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6710 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 })))),
  ((GoLean.Loc.base { id := 6711 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6712 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 })))),
  ((GoLean.Loc.base { id := 6713 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6714 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6715 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6715 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 }))]))),
  ((GoLean.Loc.base { id := 6716 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))))]
  6717)

def maCP1a : SymConfig :=
  (GoLean.Sym.Config.retV (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6715 }), offset := 0, len := 1, cap := 1 })) (GoLean.Sym.Cont.stmtOpK (GoLean.GoCore.Machine.StmtOp.appendSlice
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) 1 [(GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })),
  (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6716 }))] ([]) ([[("$c1810", GoLean.Loc.base { id := 6716 }), ("$c1809", GoLean.Loc.base { id := 6714 })],
 [("$c1808", GoLean.Loc.base { id := 6711 })],
 [("m", GoLean.Loc.base { id := 6710 })],
 [("$rfirst", GoLean.Loc.base { id := 6709 }),
  ("$ridx", GoLean.Loc.base { id := 6708 }),
  ("$rlen", GoLean.Loc.base { id := 6707 }),
  ("$rcoll", GoLean.Loc.base { id := 6706 })],
 [],
 [("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.ref "rd") { key := "raft.Ready" } "Messages"))
       (GoLean.GoCore.Expr.var "$c1810")]]) ([[("$c1810", GoLean.Loc.base { id := 6716 }), ("$c1809", GoLean.Loc.base { id := 6714 })],
 [("$c1808", GoLean.Loc.base { id := 6711 })],
 [("m", GoLean.Loc.base { id := 6710 })],
 [("$rfirst", GoLean.Loc.base { id := 6709 }),
  ("$ridx", GoLean.Loc.base { id := 6708 }),
  ("$rlen", GoLean.Loc.base { id := 6707 }),
  ("$rcoll", GoLean.Loc.base { id := 6706 })],
 [],
 [("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$c1808", GoLean.Loc.base { id := 6711 })],
 [("m", GoLean.Loc.base { id := 6710 })],
 [("$rfirst", GoLean.Loc.base { id := 6709 }),
  ("$ridx", GoLean.Loc.base { id := 6708 }),
  ("$rlen", GoLean.Loc.base { id := 6707 }),
  ("$rcoll", GoLean.Loc.base { id := 6706 })],
 [],
 [("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.seq ([]) ([[("m", GoLean.Loc.base { id := 6710 })],
 [("$rfirst", GoLean.Loc.base { id := 6709 }),
  ("$ridx", GoLean.Loc.base { id := 6708 }),
  ("$rlen", GoLean.Loc.base { id := 6707 }),
  ("$rcoll", GoLean.Loc.base { id := 6706 })],
 [],
 [("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.loop (GoLean.GoCore.Expr.boolLit true) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "$rfirst")
      (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$rfirst") (GoLean.GoCore.Expr.boolLit false))
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
      { id := "m", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
    GoLean.GoCore.Stmt.assign
      (GoLean.GoCore.Assignee.var "m")
      (GoLean.GoCore.Expr.indexGet (GoLean.GoCore.Expr.var "$rcoll") (GoLean.GoCore.Expr.var "$ridx")),
    GoLean.GoCore.Stmt.block
      #[]
      #[GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization
              { id := "$c1808", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c1808"]
              { key := "raftpb.Message.GetTo" }
              #[GoLean.GoCore.Expr.var "m"]],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.neqCmp
            (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
            (GoLean.GoCore.Expr.var "$c1808")
            (GoLean.GoCore.Expr.fieldGet
              (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "r") (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
              { key := "raft.raft" }
              "id"))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c1809",
                      typ := GoLean.GoCore.Ty.slice
                               (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                  GoLean.GoCore.Stmt.makeSlice
                    (GoLean.GoCore.Assignee.var "$c1809")
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                    (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                    (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.indexAddr
                        (GoLean.GoCore.Expr.var "$c1809")
                        (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                    (GoLean.GoCore.Expr.var "m")],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c1810",
                      typ := GoLean.GoCore.Ty.slice
                               (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                  GoLean.GoCore.Stmt.appendSlice
                    (GoLean.GoCore.Assignee.var "$c1810")
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                    (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Messages")
                    (GoLean.GoCore.Expr.var "$c1809")],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.ref "rd") { key := "raft.Ready" } "Messages"))
                    (GoLean.GoCore.Expr.var "$c1810")]])
          (GoLean.GoCore.Stmt.seqn #[])]]) ([[("$rfirst", GoLean.Loc.base { id := 6709 }),
  ("$ridx", GoLean.Loc.base { id := 6708 }),
  ("$rlen", GoLean.Loc.base { id := 6707 }),
  ("$rcoll", GoLean.Loc.base { id := 6706 })],
 [],
 [("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$rfirst", GoLean.Loc.base { id := 6709 }),
  ("$ridx", GoLean.Loc.base { id := 6708 }),
  ("$rlen", GoLean.Loc.base { id := 6707 }),
  ("$rcoll", GoLean.Loc.base { id := 6706 })],
 [],
 [("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rd"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "rd"])]) ([[("rd", GoLean.Loc.base { id := 6522 })],
 [("$res0", GoLean.Loc.base { id := 6521 }), ("rn", GoLean.Loc.base { id := 6520 })]]) ([GoLean.Loc.base { id := 6524 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.call
   #[]
   { key := "raft.RawNode.acceptReady" }
   #[GoLean.GoCore.Expr.var "rn", GoLean.GoCore.Expr.var "rd"],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rd"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("rd", GoLean.Loc.base { id := 6522 })],
 [("$res0", GoLean.Loc.base { id := 6521 }), ("rn", GoLean.Loc.base { id := 6520 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "rd"])]) ([[("rd", GoLean.Loc.base { id := 6519 })],
 [("$c2284", GoLean.Loc.base { id := 6508 })],
 [("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) ([GoLean.Loc.base { id := 6521 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2285", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2285"]
       { key := "raft.IsEmptyHardState" }
       #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "$c2285"))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$c2286", typ := GoLean.GoCore.Ty.interface { key := "error" } },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2286"]
             { key := "raft.MemoryStorage.SetHardState" }
             #[GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "nd")
                   (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                 { key := "main.twinNode" }
                 "st",
               GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.neqCmp
           (GoLean.GoCore.Ty.interface { key := "error" })
           (GoLean.GoCore.Expr.var "$c2286")
           (GoLean.GoCore.Expr.nil none))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.addr
                     (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                   (GoLean.GoCore.Expr.boolLit true)],
             GoLean.GoCore.Stmt.call
               #[]
               { key := "main.twin.viol" }
               #[GoLean.GoCore.Expr.var "t",
                 GoLean.GoCore.Expr.stringLit
                   { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 83, 101, 116, 72, 97, 114, 100, 83, 116, 97,
                                116, 101, 32, 102, 97, 105, 108, 101, 100] }],
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
                 GoLean.GoCore.Stmt.returnStmt]])
         (GoLean.GoCore.Stmt.seqn #[]),
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$c2287", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2287"]
             { key := "raftpb.HardState.GetTerm" }
             #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.addr
               (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "term"))
             (GoLean.GoCore.Expr.var "$c2287")],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$c2288", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2288"]
             { key := "raftpb.HardState.GetCommit" }
             #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.addr
               (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "commit"))
             (GoLean.GoCore.Expr.var "$c2288")]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.greaterCmp
     (GoLean.GoCore.Expr.length
       (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Entries")
       (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))))
     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$c2289", typ := GoLean.GoCore.Ty.interface { key := "error" } },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2289"]
             { key := "raft.MemoryStorage.Append" }
             #[GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "nd")
                   (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                 { key := "main.twinNode" }
                 "st",
               GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Entries"]],
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.neqCmp
           (GoLean.GoCore.Ty.interface { key := "error" })
           (GoLean.GoCore.Expr.var "$c2289")
           (GoLean.GoCore.Expr.nil none))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.addr
                     (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                   (GoLean.GoCore.Expr.boolLit true)],
             GoLean.GoCore.Stmt.call
               #[]
               { key := "main.twin.viol" }
               #[GoLean.GoCore.Expr.var "t",
                 GoLean.GoCore.Expr.stringLit
                   { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 65, 112, 112, 101, 110, 100, 32, 102, 97, 105,
                                108, 101, 100] }],
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
                 GoLean.GoCore.Stmt.returnStmt]])
         (GoLean.GoCore.Stmt.seqn #[])])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2290", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2290"]
       { key := "raft.IsEmptySnap" }
       #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Snapshot"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "$c2290"))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.addr
               (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
             (GoLean.GoCore.Expr.boolLit true)],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.viol" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.stringLit
             { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32,
                          115, 110, 97, 112, 115, 104, 111, 116] }],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
           GoLean.GoCore.Stmt.returnStmt]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.neqCmp
     (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
     (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
     (GoLean.GoCore.Expr.nil none))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.addr
               (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "state"))
             (GoLean.GoCore.Expr.fieldGet
               (GoLean.GoCore.Expr.deref
                 (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
                 (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
               { key := "raft.SoftState" }
               "RaftState")],
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.eqCmp
           (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
           (GoLean.GoCore.Expr.fieldGet
             (GoLean.GoCore.Expr.deref
               (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
               (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
             { key := "raft.SoftState" }
             "RaftState")
           (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64)))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.assign
               (GoLean.GoCore.Assignee.addr
                 (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "claims"))
               (GoLean.GoCore.Expr.add
                 (GoLean.GoCore.Expr.fieldGet
                   (GoLean.GoCore.Expr.deref
                     (GoLean.GoCore.Expr.var "t")
                     (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                   { key := "main.twin" }
                   "claims")
                 (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.initialization
                   { id := "prev", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                 GoLean.GoCore.Stmt.initialization { id := "ok", typ := GoLean.GoCore.Ty.bool },
                 GoLean.GoCore.Stmt.mapLookup
                   (GoLean.GoCore.Assignee.var "prev")
                   (GoLean.GoCore.Assignee.var "ok")
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "t")
                       (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                     { key := "main.twin" }
                     "leaderOf")
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "nd")
                       (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                     { key := "main.twinNode" }
                     "term")
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))],
             GoLean.GoCore.Stmt.ifThenElse
               (GoLean.GoCore.Expr.and
                 (GoLean.GoCore.Expr.var "ok")
                 (GoLean.GoCore.Expr.neqCmp
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.var "prev")
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "nd")
                       (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                     { key := "main.twinNode" }
                     "id")))
               (GoLean.GoCore.Stmt.block
                 #[]
                 #[GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.initialization { id := "$c2291", typ := GoLean.GoCore.Ty.string },
                       GoLean.GoCore.Stmt.call
                         #[GoLean.GoCore.Assignee.var "$c2291"]
                         { key := "utoa" }
                         #[GoLean.GoCore.Expr.fieldGet
                             (GoLean.GoCore.Expr.deref
                               (GoLean.GoCore.Expr.var "nd")
                               (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                             { key := "main.twinNode" }
                             "term"]],
                   GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.initialization { id := "$c2292", typ := GoLean.GoCore.Ty.string },
                       GoLean.GoCore.Stmt.call
                         #[GoLean.GoCore.Assignee.var "$c2292"]
                         { key := "utoa" }
                         #[GoLean.GoCore.Expr.var "prev"]],
                   GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.initialization { id := "$c2293", typ := GoLean.GoCore.Ty.string },
                       GoLean.GoCore.Stmt.call
                         #[GoLean.GoCore.Assignee.var "$c2293"]
                         { key := "utoa" }
                         #[GoLean.GoCore.Expr.fieldGet
                             (GoLean.GoCore.Expr.deref
                               (GoLean.GoCore.Expr.var "nd")
                               (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                             { key := "main.twinNode" }
                             "id"]],
                   GoLean.GoCore.Stmt.call
                     #[]
                     { key := "main.twin.viol" }
                     #[GoLean.GoCore.Expr.var "t",
                       GoLean.GoCore.Expr.add
                         (GoLean.GoCore.Expr.add
                           (GoLean.GoCore.Expr.add
                             (GoLean.GoCore.Expr.add
                               (GoLean.GoCore.Expr.add
                                 (GoLean.GoCore.Expr.stringLit
                                   { bytes := #[83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102,
                                                101, 116, 121, 58, 32, 116, 101, 114, 109, 32] })
                                 (GoLean.GoCore.Expr.var "$c2291"))
                               (GoLean.GoCore.Expr.stringLit
                                 { bytes := #[32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116, 104,
                                              32, 110, 111, 100, 101, 32] }))
                             (GoLean.GoCore.Expr.var "$c2292"))
                           (GoLean.GoCore.Expr.stringLit { bytes := #[32, 97, 110, 100, 32, 110, 111, 100, 101, 32] }))
                         (GoLean.GoCore.Expr.var "$c2293")]])
               (GoLean.GoCore.Stmt.seqn #[]),
             GoLean.GoCore.Stmt.mapAssign
               (GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "t")
                   (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                 { key := "main.twin" }
                 "leaderOf")
               (GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "nd")
                   (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                 { key := "main.twinNode" }
                 "term")
               (GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "nd")
                   (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                 { key := "main.twinNode" }
                 "id")
               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))])
         (GoLean.GoCore.Stmt.seqn #[])])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.block
   #[]
   #[GoLean.GoCore.Stmt.initialization
       { id := "$rcoll",
         typ := GoLean.GoCore.Ty.slice
                  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$rcoll")
       (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Messages"),
     GoLean.GoCore.Stmt.initialization { id := "$rlen", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$rlen")
       (GoLean.GoCore.Expr.length (GoLean.GoCore.Expr.var "$rcoll") none),
     GoLean.GoCore.Stmt.initialization { id := "$ridx", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
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
             (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$rfirst") (GoLean.GoCore.Expr.boolLit false))
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
             { id := "m", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
           GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "m")
             (GoLean.GoCore.Expr.indexGet (GoLean.GoCore.Expr.var "$rcoll") (GoLean.GoCore.Expr.var "$ridx")),
           GoLean.GoCore.Stmt.block
             #[]
             #[GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.initialization
                     { id := "$c2294",
                       typ := GoLean.GoCore.Ty.slice
                                (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                   GoLean.GoCore.Stmt.makeSlice
                     (GoLean.GoCore.Assignee.var "$c2294")
                     (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                     (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                   GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.addr
                       (GoLean.GoCore.Expr.indexAddr
                         (GoLean.GoCore.Expr.var "$c2294")
                         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                     (GoLean.GoCore.Expr.var "m")],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.initialization
                     { id := "$c2295",
                       typ := GoLean.GoCore.Ty.slice
                                (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                   GoLean.GoCore.Stmt.appendSlice
                     (GoLean.GoCore.Assignee.var "$c2295")
                     (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                     (GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "t")
                         (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                       { key := "main.twin" }
                       "net")
                     (GoLean.GoCore.Expr.var "$c2294")],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.addr
                       (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "net"))
                     (GoLean.GoCore.Expr.var "$c2295")],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.initialization
                     { id := "$c2296", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                   GoLean.GoCore.Stmt.makeSlice
                     (GoLean.GoCore.Assignee.var "$c2296")
                     (GoLean.GoCore.Ty.bool)
                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                     (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                   GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.addr
                       (GoLean.GoCore.Expr.indexAddr
                         (GoLean.GoCore.Expr.var "$c2296")
                         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                     (GoLean.GoCore.Expr.boolLit true)],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.initialization
                     { id := "$c2297", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                   GoLean.GoCore.Stmt.appendSlice
                     (GoLean.GoCore.Assignee.var "$c2297")
                     (GoLean.GoCore.Ty.bool)
                     (GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "t")
                         (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                       { key := "main.twin" }
                       "live")
                     (GoLean.GoCore.Expr.var "$c2296")],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.addr
                       (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "live"))
                     (GoLean.GoCore.Expr.var "$c2297")]]])],
 GoLean.GoCore.Stmt.block
   #[]
   #[GoLean.GoCore.Stmt.initialization
       { id := "$rcoll",
         typ := GoLean.GoCore.Ty.slice
                  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$rcoll")
       (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "CommittedEntries"),
     GoLean.GoCore.Stmt.initialization { id := "$rlen", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$rlen")
       (GoLean.GoCore.Expr.length (GoLean.GoCore.Expr.var "$rcoll") none),
     GoLean.GoCore.Stmt.initialization { id := "$ridx", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
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
             (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$rfirst") (GoLean.GoCore.Expr.boolLit false))
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
             { id := "e", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }) },
           GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "e")
             (GoLean.GoCore.Expr.indexGet (GoLean.GoCore.Expr.var "$rcoll") (GoLean.GoCore.Expr.var "$ridx")),
           GoLean.GoCore.Stmt.block
             #[]
             #[GoLean.GoCore.Stmt.call
                 #[]
                 { key := "main.twin.apply" }
                 #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "nd", GoLean.GoCore.Expr.var "e"]]])],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "raft.RawNode.Advance" }
   #[GoLean.GoCore.Expr.fieldGet
       (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "nd") (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
       { key := "main.twinNode" }
       "rn",
     GoLean.GoCore.Expr.var "rd"]]) ([[("rd", GoLean.Loc.base { id := 6519 })],
 [("$c2284", GoLean.Loc.base { id := 6508 })],
 [("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$c2284", GoLean.Loc.base { id := 6508 })],
 [("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.loop (GoLean.GoCore.Expr.boolLit true) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "$forFirst")
      (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$forFirst") (GoLean.GoCore.Expr.boolLit false))
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.seqn
      #[GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "$c2284", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c2284"]
              { key := "raft.RawNode.HasReady" }
              #[GoLean.GoCore.Expr.fieldGet
                  (GoLean.GoCore.Expr.deref
                    (GoLean.GoCore.Expr.var "nd")
                    (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                  { key := "main.twinNode" }
                  "rn"]]],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "$c2284")
      (GoLean.GoCore.Stmt.seqn #[])
      (GoLean.GoCore.Stmt.breakStmt),
    GoLean.GoCore.Stmt.block
      #[]
      #[GoLean.GoCore.Stmt.assign
          (GoLean.GoCore.Assignee.var "rounds")
          (GoLean.GoCore.Expr.add
            (GoLean.GoCore.Expr.var "rounds")
            (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.var "rounds")
            (GoLean.GoCore.Expr.intLit 64 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                    (GoLean.GoCore.Expr.boolLit true)],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.viol" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.stringLit
                    { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 104, 97, 114, 118, 101, 115, 116, 32, 100,
                                 105, 100, 32, 110, 111, 116, 32, 113, 117, 105, 101, 115, 99, 101, 32, 105, 110, 32,
                                 54, 52, 32, 114, 111, 117, 110, 100, 115] }],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
                  GoLean.GoCore.Stmt.returnStmt]])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "rd", typ := GoLean.GoCore.Ty.defined { key := "raft.Ready" } },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "rd"]
              { key := "raft.RawNode.Ready" }
              #[GoLean.GoCore.Expr.fieldGet
                  (GoLean.GoCore.Expr.deref
                    (GoLean.GoCore.Expr.var "nd")
                    (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                  { key := "main.twinNode" }
                  "rn"]],
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "$c2285", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c2285"]
              { key := "raft.IsEmptyHardState" }
              #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "$c2285"))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2286", typ := GoLean.GoCore.Ty.interface { key := "error" } },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2286"]
                    { key := "raft.MemoryStorage.SetHardState" }
                    #[GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "nd")
                          (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                        { key := "main.twinNode" }
                        "st",
                      GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.neqCmp
                  (GoLean.GoCore.Ty.interface { key := "error" })
                  (GoLean.GoCore.Expr.var "$c2286")
                  (GoLean.GoCore.Expr.nil none))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.addr
                            (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                          (GoLean.GoCore.Expr.boolLit true)],
                    GoLean.GoCore.Stmt.call
                      #[]
                      { key := "main.twin.viol" }
                      #[GoLean.GoCore.Expr.var "t",
                        GoLean.GoCore.Expr.stringLit
                          { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 83, 101, 116, 72, 97, 114, 100, 83,
                                       116, 97, 116, 101, 32, 102, 97, 105, 108, 101, 100] }],
                    GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$res0")
                          (GoLean.GoCore.Expr.var "rounds"),
                        GoLean.GoCore.Stmt.returnStmt]])
                (GoLean.GoCore.Stmt.seqn #[]),
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2287", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2287"]
                    { key := "raftpb.HardState.GetTerm" }
                    #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "term"))
                    (GoLean.GoCore.Expr.var "$c2287")],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2288", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2288"]
                    { key := "raftpb.HardState.GetCommit" }
                    #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "commit"))
                    (GoLean.GoCore.Expr.var "$c2288")]])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.length
              (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Entries")
              (some (GoLean.GoCore.Ty.slice
                 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))))
            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2289", typ := GoLean.GoCore.Ty.interface { key := "error" } },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2289"]
                    { key := "raft.MemoryStorage.Append" }
                    #[GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "nd")
                          (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                        { key := "main.twinNode" }
                        "st",
                      GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Entries"]],
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.neqCmp
                  (GoLean.GoCore.Ty.interface { key := "error" })
                  (GoLean.GoCore.Expr.var "$c2289")
                  (GoLean.GoCore.Expr.nil none))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.addr
                            (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                          (GoLean.GoCore.Expr.boolLit true)],
                    GoLean.GoCore.Stmt.call
                      #[]
                      { key := "main.twin.viol" }
                      #[GoLean.GoCore.Expr.var "t",
                        GoLean.GoCore.Expr.stringLit
                          { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 65, 112, 112, 101, 110, 100, 32, 102,
                                       97, 105, 108, 101, 100] }],
                    GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$res0")
                          (GoLean.GoCore.Expr.var "rounds"),
                        GoLean.GoCore.Stmt.returnStmt]])
                (GoLean.GoCore.Stmt.seqn #[])])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "$c2290", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c2290"]
              { key := "raft.IsEmptySnap" }
              #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Snapshot"]],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "$c2290"))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                    (GoLean.GoCore.Expr.boolLit true)],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.viol" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.stringLit
                    { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101,
                                 100, 32, 115, 110, 97, 112, 115, 104, 111, 116] }],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
                  GoLean.GoCore.Stmt.returnStmt]])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.neqCmp
            (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
            (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
            (GoLean.GoCore.Expr.nil none))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "state"))
                    (GoLean.GoCore.Expr.fieldGet
                      (GoLean.GoCore.Expr.deref
                        (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
                        (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
                      { key := "raft.SoftState" }
                      "RaftState")],
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.eqCmp
                  (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
                  (GoLean.GoCore.Expr.fieldGet
                    (GoLean.GoCore.Expr.deref
                      (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
                      (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
                    { key := "raft.SoftState" }
                    "RaftState")
                  (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64)))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.addr
                        (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "claims"))
                      (GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.fieldGet
                          (GoLean.GoCore.Expr.deref
                            (GoLean.GoCore.Expr.var "t")
                            (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                          { key := "main.twin" }
                          "claims")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                    GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "prev", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                        GoLean.GoCore.Stmt.initialization { id := "ok", typ := GoLean.GoCore.Ty.bool },
                        GoLean.GoCore.Stmt.mapLookup
                          (GoLean.GoCore.Assignee.var "prev")
                          (GoLean.GoCore.Assignee.var "ok")
                          (GoLean.GoCore.Expr.fieldGet
                            (GoLean.GoCore.Expr.deref
                              (GoLean.GoCore.Expr.var "t")
                              (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                            { key := "main.twin" }
                            "leaderOf")
                          (GoLean.GoCore.Expr.fieldGet
                            (GoLean.GoCore.Expr.deref
                              (GoLean.GoCore.Expr.var "nd")
                              (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                            { key := "main.twinNode" }
                            "term")
                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))],
                    GoLean.GoCore.Stmt.ifThenElse
                      (GoLean.GoCore.Expr.and
                        (GoLean.GoCore.Expr.var "ok")
                        (GoLean.GoCore.Expr.neqCmp
                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                          (GoLean.GoCore.Expr.var "prev")
                          (GoLean.GoCore.Expr.fieldGet
                            (GoLean.GoCore.Expr.deref
                              (GoLean.GoCore.Expr.var "nd")
                              (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                            { key := "main.twinNode" }
                            "id")))
                      (GoLean.GoCore.Stmt.block
                        #[]
                        #[GoLean.GoCore.Stmt.seqn
                            #[GoLean.GoCore.Stmt.initialization { id := "$c2291", typ := GoLean.GoCore.Ty.string },
                              GoLean.GoCore.Stmt.call
                                #[GoLean.GoCore.Assignee.var "$c2291"]
                                { key := "utoa" }
                                #[GoLean.GoCore.Expr.fieldGet
                                    (GoLean.GoCore.Expr.deref
                                      (GoLean.GoCore.Expr.var "nd")
                                      (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                                    { key := "main.twinNode" }
                                    "term"]],
                          GoLean.GoCore.Stmt.seqn
                            #[GoLean.GoCore.Stmt.initialization { id := "$c2292", typ := GoLean.GoCore.Ty.string },
                              GoLean.GoCore.Stmt.call
                                #[GoLean.GoCore.Assignee.var "$c2292"]
                                { key := "utoa" }
                                #[GoLean.GoCore.Expr.var "prev"]],
                          GoLean.GoCore.Stmt.seqn
                            #[GoLean.GoCore.Stmt.initialization { id := "$c2293", typ := GoLean.GoCore.Ty.string },
                              GoLean.GoCore.Stmt.call
                                #[GoLean.GoCore.Assignee.var "$c2293"]
                                { key := "utoa" }
                                #[GoLean.GoCore.Expr.fieldGet
                                    (GoLean.GoCore.Expr.deref
                                      (GoLean.GoCore.Expr.var "nd")
                                      (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                                    { key := "main.twinNode" }
                                    "id"]],
                          GoLean.GoCore.Stmt.call
                            #[]
                            { key := "main.twin.viol" }
                            #[GoLean.GoCore.Expr.var "t",
                              GoLean.GoCore.Expr.add
                                (GoLean.GoCore.Expr.add
                                  (GoLean.GoCore.Expr.add
                                    (GoLean.GoCore.Expr.add
                                      (GoLean.GoCore.Expr.add
                                        (GoLean.GoCore.Expr.stringLit
                                          { bytes := #[83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97,
                                                       102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32] })
                                        (GoLean.GoCore.Expr.var "$c2291"))
                                      (GoLean.GoCore.Expr.stringLit
                                        { bytes := #[32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116,
                                                     104, 32, 110, 111, 100, 101, 32] }))
                                    (GoLean.GoCore.Expr.var "$c2292"))
                                  (GoLean.GoCore.Expr.stringLit
                                    { bytes := #[32, 97, 110, 100, 32, 110, 111, 100, 101, 32] }))
                                (GoLean.GoCore.Expr.var "$c2293")]])
                      (GoLean.GoCore.Stmt.seqn #[]),
                    GoLean.GoCore.Stmt.mapAssign
                      (GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "t")
                          (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                        { key := "main.twin" }
                        "leaderOf")
                      (GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "nd")
                          (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                        { key := "main.twinNode" }
                        "term")
                      (GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "nd")
                          (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                        { key := "main.twinNode" }
                        "id")
                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))])
                (GoLean.GoCore.Stmt.seqn #[])])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.block
          #[]
          #[GoLean.GoCore.Stmt.initialization
              { id := "$rcoll",
                typ := GoLean.GoCore.Ty.slice
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rcoll")
              (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Messages"),
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
                    { id := "m",
                      typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "m")
                    (GoLean.GoCore.Expr.indexGet (GoLean.GoCore.Expr.var "$rcoll") (GoLean.GoCore.Expr.var "$ridx")),
                  GoLean.GoCore.Stmt.block
                    #[]
                    #[GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.initialization
                            { id := "$c2294",
                              typ := GoLean.GoCore.Ty.slice
                                       (GoLean.GoCore.Ty.pointer
                                         (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                          GoLean.GoCore.Stmt.makeSlice
                            (GoLean.GoCore.Assignee.var "$c2294")
                            (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                            (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                            (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                          GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.addr
                              (GoLean.GoCore.Expr.indexAddr
                                (GoLean.GoCore.Expr.var "$c2294")
                                (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                            (GoLean.GoCore.Expr.var "m")],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.initialization
                            { id := "$c2295",
                              typ := GoLean.GoCore.Ty.slice
                                       (GoLean.GoCore.Ty.pointer
                                         (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                          GoLean.GoCore.Stmt.appendSlice
                            (GoLean.GoCore.Assignee.var "$c2295")
                            (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                            (GoLean.GoCore.Expr.fieldGet
                              (GoLean.GoCore.Expr.deref
                                (GoLean.GoCore.Expr.var "t")
                                (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                              { key := "main.twin" }
                              "net")
                            (GoLean.GoCore.Expr.var "$c2294")],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.addr
                              (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "net"))
                            (GoLean.GoCore.Expr.var "$c2295")],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.initialization
                            { id := "$c2296", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                          GoLean.GoCore.Stmt.makeSlice
                            (GoLean.GoCore.Assignee.var "$c2296")
                            (GoLean.GoCore.Ty.bool)
                            (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                            (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                          GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.addr
                              (GoLean.GoCore.Expr.indexAddr
                                (GoLean.GoCore.Expr.var "$c2296")
                                (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                            (GoLean.GoCore.Expr.boolLit true)],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.initialization
                            { id := "$c2297", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                          GoLean.GoCore.Stmt.appendSlice
                            (GoLean.GoCore.Assignee.var "$c2297")
                            (GoLean.GoCore.Ty.bool)
                            (GoLean.GoCore.Expr.fieldGet
                              (GoLean.GoCore.Expr.deref
                                (GoLean.GoCore.Expr.var "t")
                                (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                              { key := "main.twin" }
                              "live")
                            (GoLean.GoCore.Expr.var "$c2296")],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.addr
                              (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "live"))
                            (GoLean.GoCore.Expr.var "$c2297")]]])],
        GoLean.GoCore.Stmt.block
          #[]
          #[GoLean.GoCore.Stmt.initialization
              { id := "$rcoll",
                typ := GoLean.GoCore.Ty.slice
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rcoll")
              (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "CommittedEntries"),
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
                    { id := "e", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "e")
                    (GoLean.GoCore.Expr.indexGet (GoLean.GoCore.Expr.var "$rcoll") (GoLean.GoCore.Expr.var "$ridx")),
                  GoLean.GoCore.Stmt.block
                    #[]
                    #[GoLean.GoCore.Stmt.call
                        #[]
                        { key := "main.twin.apply" }
                        #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "nd", GoLean.GoCore.Expr.var "e"]]])],
        GoLean.GoCore.Stmt.call
          #[]
          { key := "raft.RawNode.Advance" }
          #[GoLean.GoCore.Expr.fieldGet
              (GoLean.GoCore.Expr.deref
                (GoLean.GoCore.Expr.var "nd")
                (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
              { key := "main.twinNode" }
              "rn",
            GoLean.GoCore.Expr.var "rd"]]]) ([[("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$cr0"])]) ([[("$cr0", GoLean.Loc.base { id := 6502 }),
  ("to", GoLean.Loc.base { id := 6138 }),
  ("$c2316", GoLean.Loc.base { id := 6135 }),
  ("m", GoLean.Loc.base { id := 6134 })],
 [("i", GoLean.Loc.base { id := 6133 }), ("t", GoLean.Loc.base { id := 6132 })]]) ([GoLean.Loc.base { id := 6505 }]) [] (GoLean.Sym.Cont.seq ([]) ([[("$cr0", GoLean.Loc.base { id := 6502 }),
  ("to", GoLean.Loc.base { id := 6138 }),
  ("$c2316", GoLean.Loc.base { id := 6135 }),
  ("m", GoLean.Loc.base { id := 6134 })],
 [("i", GoLean.Loc.base { id := 6133 }), ("t", GoLean.Loc.base { id := 6132 })]]) (GoLean.Sym.Cont.frame ([]) ([[("$c2241", GoLean.Loc.base { id := 6125 }),
  ("$c2240", GoLean.Loc.base { id := 6122 }),
  ("$c2239", GoLean.Loc.base { id := 6114 }),
  ("$c2238", GoLean.Loc.base { id := 6111 }),
  ("$c2237", GoLean.Loc.base { id := 6105 }),
  ("$c2236", GoLean.Loc.base { id := 6097 }),
  ("m", GoLean.Loc.base { id := 6096 }),
  ("picked", GoLean.Loc.base { id := 6094 })],
 [("live", GoLean.Loc.base { id := 6088 }), ("$c2235", GoLean.Loc.base { id := 6086 })],
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
 GoLean.GoCore.Stmt.continueStmt]) ([[("$c2241", GoLean.Loc.base { id := 6125 }),
  ("$c2240", GoLean.Loc.base { id := 6122 }),
  ("$c2239", GoLean.Loc.base { id := 6114 }),
  ("$c2238", GoLean.Loc.base { id := 6111 }),
  ("$c2237", GoLean.Loc.base { id := 6105 }),
  ("$c2236", GoLean.Loc.base { id := 6097 }),
  ("m", GoLean.Loc.base { id := 6096 }),
  ("picked", GoLean.Loc.base { id := 6094 })],
 [("live", GoLean.Loc.base { id := 6088 }), ("$c2235", GoLean.Loc.base { id := 6086 })],
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
 GoLean.GoCore.Stmt.breakStmt]) ([[("live", GoLean.Loc.base { id := 6088 }), ("$c2235", GoLean.Loc.base { id := 6086 })],
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
  ("$res0", GoLean.Loc.base { id := 98 })]]) (GoLean.Sym.Cont.frame ([]) ([]) ([]) [] (GoLean.Sym.Cont.stop) false)) false)))))))) false)) false)))))) false)) false))))))))))

def maSP1b : SymState :=
  (GoLean.Sym.State.mk
  [((GoLean.Loc.base { id := 15 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 57 })))),
  ((GoLean.Loc.base { id := 57 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Commit"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 121 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twin" })) (GoLean.Sym.Value.struct ({ key := "main.twin" }) #[(("nodes"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 1764 }), offset := 0, len := 3, cap := 4 }))),
  (("net"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6077 }), offset := 0, len := 1, cap := 1 }))),
  (("live"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6078 }), offset := 0, len := 1, cap := 1 }))),
  (("leaderOf"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 115 }) }))),
  (("byIndex"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 118 }) }))),
  (("claims"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("violations"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("pending"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 136 }), offset := 0, len := 2, cap := 4 }))),
  (("driven"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("seq"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.int))),
  (("trace"), (GoLean.Sym.Value.string ({ bytes := #[91, 99, 104, 111, 105, 99, 101, 45, 100, 114, 105, 118, 101, 110, 93, 10, 99, 97, 109, 112, 97, 105, 103,
             110, 49, 114, 49, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 51, 45, 62, 50] }))),
  (("halt"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1770 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1767 }) })))]))),
  ((GoLean.Loc.base { id := 1779 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.struct ({ key := "raft.MemoryStorage" }) #[(("Mutex"), (GoLean.Sym.Value.syncData (GoLean.SyncPrim.mutex false))),
  (("hardState"), (GoLean.Sym.Value.nil)),
  (("snapshot"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1858 }))),
  (("ents"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 1900 }), offset := 0, len := 1, cap := 1 }))),
  (("callStats"), (GoLean.Sym.Value.struct ({ key := "raft.inMemStorageCallStats" }) #[(("initialState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int))),
  (("firstIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.add
        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 4))
        (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.int))),
  (("lastIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 10)))) (GoLean.GoCore.IntKind.int))),
  (("entries"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.int))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.int))),
  (("snapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.int)))]))]))),
  ((GoLean.Loc.base { id := 1895 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 1898 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1886 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1895 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 1900 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1898 }))]))),
  ((GoLean.Loc.base { id := 1949 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })) (GoLean.Sym.Value.struct ({ key := "raft.raftLog" }) #[(("storage"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 })))),
  (("unstable"), (GoLean.Sym.Value.struct ({ key := "raft.unstable" }) #[(("snapshot"), (GoLean.Sym.Value.nil)),
  (("entries"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 }))),
  (("offset"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("snapshotInProgress"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("offsetInProgress"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 }))))])),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("applying"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("maxApplyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1989 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raft" })) (GoLean.Sym.Value.struct ({ key := "raft.raft" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("Term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("Vote"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("readStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("raftLog"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 }))),
  (("maxMsgSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("maxUncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64))),
  (("trk"), (GoLean.Sym.Value.struct ({ key := "tracker.ProgressTracker" }) #[(("Config"), (GoLean.Sym.Value.struct ({ key := "tracker.Config" }) #[(("Voters"), (GoLean.Sym.Value.array #[(GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 2686 }) })),
  (GoLean.Sym.Value.map ({ base := none }))])),
  (("AutoLeave"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Learners"), (GoLean.Sym.Value.map ({ base := none }))),
  (("LearnersNext"), (GoLean.Sym.Value.map ({ base := none })))])),
  (("Progress"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 2703 }) }))),
  (("Votes"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 3059 }) }))),
  (("MaxInflight"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 256) (GoLean.GoCore.IntKind.int))),
  (("MaxInflightBytes"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64)))])),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("isLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("msgs"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("msgsAfterAppend"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6499 }), offset := 0, len := 1, cap := 4 }))),
  (("lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("leadTransferee"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("pendingConfIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("disableConfChangeValidation"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("uncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("readOnly"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3199 }))),
  (("electionElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("heartbeatElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("checkQuorum"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("preVote"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("heartbeatTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("electionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("randomizedElectionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("disableProposalForwarding"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("stepDownOnRemoval"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("tick"), (GoLean.Sym.Value.funcVal ({ key := "raft.raft.tickElection" }) [(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 }))])),
  (("step"), (GoLean.Sym.Value.funcVal ({ key := "raft.stepFollower" }) [])),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("pendingReadIndexMessages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("traceLogger"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 3342 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })) (GoLean.Sym.Value.struct ({ key := "raft.RawNode" }) #[(("raft"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 }))),
  (("asyncStorageWrites"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("prevSoftSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3344 }))),
  (("prevHardSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 }))),
  (("stepsOnAdvance"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 3344 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 3351 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 3354 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 3357 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 3360 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3351 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3354 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3357 })))]))),
  ((GoLean.Loc.base { id := 6075 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6077 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6076 }))]))),
  ((GoLean.Loc.base { id := 6078 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))]))),
  ((GoLean.Loc.base { id := 6080 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6081 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6082 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6080 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6081 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 6132 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 6138 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1770 })))),
  ((GoLean.Loc.base { id := 6424 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 })),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 6456 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Message" }) #[(("Type"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6449 }))),
  (("To"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6075 }))),
  (("From"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6463 }))),
  (("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6490 }))),
  (("LogTerm"), (GoLean.Sym.Value.nil)),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6453 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Commit"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("Reject"), (GoLean.Sym.Value.nil)),
  (("RejectHint"), (GoLean.Sym.Value.nil)),
  (("Context"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Responses"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 6499 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 })),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 6503 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 6504 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1770 })))),
  ((GoLean.Loc.base { id := 6505 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6506 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6507 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6508 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6509 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 })))),
  ((GoLean.Loc.base { id := 6510 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6511 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6512 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6513 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6514 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6515 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6516 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6512 })))),
  ((GoLean.Loc.base { id := 6517 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3344 })))),
  ((GoLean.Loc.base { id := 6518 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6519 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.nil)),
  (("HardState"), (GoLean.Sym.Value.nil)),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 6520 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 })))),
  ((GoLean.Loc.base { id := 6521 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.nil)),
  (("HardState"), (GoLean.Sym.Value.nil)),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 6522 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.nil)),
  (("HardState"), (GoLean.Sym.Value.nil)),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 6523 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 })))),
  ((GoLean.Loc.base { id := 6524 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.nil)),
  (("HardState"), (GoLean.Sym.Value.nil)),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 6525 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6526 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6527 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6528 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6529 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6530 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6531 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6532 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.sub (GoLean.Sym.SymInt.lit 2) (GoLean.Sym.SymInt.lit 2))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6533 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6534 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 6535 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 })))),
  ((GoLean.Loc.base { id := 6536 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 6537 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6538 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6539 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 6540 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6541 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit true))))),
  ((GoLean.Loc.base { id := 6542 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6543 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit true))))),
  ((GoLean.Loc.base { id := 6544 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6545 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6546 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 6547 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6548 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6549 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6550 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6551 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.entryEncodingSize" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.sub (GoLean.Sym.SymInt.lit 1048576) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6552 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6553 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6554 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6555 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.add
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
        (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6556 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.entryEncodingSize" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.sub (GoLean.Sym.SymInt.lit 1048576) (GoLean.Sym.SymInt.lit 0))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6557 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6558 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6559 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6560 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6561 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6562 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
          (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6563 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6564 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.uint64)
                  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
                (GoLean.Sym.SymInt.lit 1))))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6565 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6566 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
              (GoLean.Sym.SymInt.lit 1)))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6567 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6568 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6569 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6570 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6571 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6572 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
            (GoLean.Sym.SymInt.lit 1))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6573 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6574 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 })))),
  ((GoLean.Loc.base { id := 6575 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
          (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6576 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6577 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.add
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
        (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6578 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 })))),
  ((GoLean.Loc.base { id := 6579 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6580 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6581 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1898 })))),
  ((GoLean.Loc.base { id := 6582 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6583 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.sync (GoLean.GoCore.SyncKind.mutex)))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1779 }) { key := "raft.MemoryStorage" } "Mutex")))),
  ((GoLean.Loc.base { id := 6584 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.sub
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.lit 2)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.uint64)
                  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
            (GoLean.Sym.SymInt.lit 1))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6585 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6586 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.sub
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.lit 2)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
          (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6587 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.sub
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.lit 2)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
        (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6588 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6589 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6590 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.sub
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.lit 2)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6591 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6592 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6593 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.sub
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.uint64)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.uint64)
                    (GoLean.Sym.SymInt.sub
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.uint64)
                        (GoLean.Sym.SymInt.add
                          (GoLean.Sym.SymInt.lit 2)
                          (GoLean.Sym.SymInt.norm
                            (GoLean.GoCore.IntKind.uint64)
                            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
                      (GoLean.Sym.SymInt.lit 1)))))))
          (GoLean.Sym.SymInt.lit 1)))
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.uint64)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.uint64)
                    (GoLean.Sym.SymInt.add
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.uint64)
                        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
                      (GoLean.Sym.SymInt.lit 1)))))))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6594 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6595 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6596 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6597 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
          (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6598 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6599 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6600 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6601 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
            (GoLean.Sym.SymInt.lit 1))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6602 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.lit 2)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6603 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6604 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6605 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.entryEncodingSize" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.sub (GoLean.Sym.SymInt.lit 1048576) (GoLean.Sym.SymInt.lit 0)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6606 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6607 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.add
                    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.add
                        (GoLean.Sym.SymInt.lit 1)
                        (GoLean.Sym.SymInt.norm
                          (GoLean.GoCore.IntKind.int)
                          (GoLean.Sym.SymInt.norm
                            (GoLean.GoCore.IntKind.int)
                            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.add
                  (GoLean.Sym.SymInt.lit 1)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))))))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6608 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "proto.Message" })) (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 }))))),
  ((GoLean.Loc.base { id := 6609 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.add
                  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.add
                      (GoLean.Sym.SymInt.lit 1)
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.int)
                        (GoLean.Sym.SymInt.norm
                          (GoLean.GoCore.IntKind.int)
                          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.lit 1)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6610 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "proto.Message" })) (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 }))))),
  ((GoLean.Loc.base { id := 6611 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 })))),
  ((GoLean.Loc.base { id := 6612 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6613 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 })))),
  ((GoLean.Loc.base { id := 6614 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.add
                    (GoLean.Sym.SymInt.lit 1)
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.int)
                        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.lit 1)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6615 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 })))),
  ((GoLean.Loc.base { id := 6616 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.add
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.add
                  (GoLean.Sym.SymInt.lit 1)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.lit 1)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6617 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.lit 1)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.lit 1)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6618 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6619 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6620 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6621 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6622 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6623 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6624 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6625 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6626 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6627 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6628 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.entryEncodingSize" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.add
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.add
                        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
                        (GoLean.Sym.SymInt.norm
                          (GoLean.GoCore.IntKind.int)
                          (GoLean.Sym.SymInt.add
                            (GoLean.Sym.SymInt.lit 1)
                            (GoLean.Sym.SymInt.norm
                              (GoLean.GoCore.IntKind.int)
                              (GoLean.Sym.SymInt.norm
                                (GoLean.GoCore.IntKind.int)
                                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.add
                      (GoLean.Sym.SymInt.lit 1)
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.int)
                        (GoLean.Sym.SymInt.norm
                          (GoLean.GoCore.IntKind.int)
                          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))))))))))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6629 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6630 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6631 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6632 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6640 }))),
  (("HardState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 }))),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))]))),
  ((GoLean.Loc.base { id := 6633 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6634 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6635 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6636 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6637 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6633 })))),
  ((GoLean.Loc.base { id := 6638 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3344 })))),
  ((GoLean.Loc.base { id := 6639 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6640 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6641 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6642 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6643 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6644 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6645 })))),
  ((GoLean.Loc.base { id := 6645 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6646 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6645 })))),
  ((GoLean.Loc.base { id := 6647 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6648 })))),
  ((GoLean.Loc.base { id := 6648 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6649 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6648 })))),
  ((GoLean.Loc.base { id := 6650 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6651 })))),
  ((GoLean.Loc.base { id := 6651 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6652 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6651 })))),
  ((GoLean.Loc.base { id := 6653 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6654 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6645 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6648 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6651 })))]))),
  ((GoLean.Loc.base { id := 6655 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.eqI
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))))),
  ((GoLean.Loc.base { id := 6656 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6657 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6658 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.eqI
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))))),
  ((GoLean.Loc.base { id := 6659 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6660 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6661 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6662 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6663 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6664 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6665 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.eqI
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)))
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))))))),
  ((GoLean.Loc.base { id := 6666 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6667 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6668 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6669 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6670 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6671 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6672 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.eqI
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))))),
  ((GoLean.Loc.base { id := 6673 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6674 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6675 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6676 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6677 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6678 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6679 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit true))))),
  ((GoLean.Loc.base { id := 6680 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6681 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit true))))),
  ((GoLean.Loc.base { id := 6682 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" }))) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6683 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6684 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" }))) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6685 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6698 })))),
  ((GoLean.Loc.base { id := 6686 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6687 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6698 })))),
  ((GoLean.Loc.base { id := 6688 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6689 })))),
  ((GoLean.Loc.base { id := 6689 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6690 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6689 })))),
  ((GoLean.Loc.base { id := 6691 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6692 })))),
  ((GoLean.Loc.base { id := 6692 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6693 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6692 })))),
  ((GoLean.Loc.base { id := 6694 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6695 })))),
  ((GoLean.Loc.base { id := 6695 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6696 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6695 })))),
  ((GoLean.Loc.base { id := 6697 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6698 })))),
  ((GoLean.Loc.base { id := 6698 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6689 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6692 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6695 })))]))),
  ((GoLean.Loc.base { id := 6699 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))),
  ((GoLean.Loc.base { id := 6700 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6698 })))),
  ((GoLean.Loc.base { id := 6701 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6702 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6703 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))),
  ((GoLean.Loc.base { id := 6704 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))),
  ((GoLean.Loc.base { id := 6705 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))),
  ((GoLean.Loc.base { id := 6706 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6499 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6707 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6708 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6709 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6710 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 })))),
  ((GoLean.Loc.base { id := 6711 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6712 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 })))),
  ((GoLean.Loc.base { id := 6713 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6714 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6715 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6715 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 }))]))),
  ((GoLean.Loc.base { id := 6716 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6717 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6717 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 })),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)])))]
  6718)

def maCP1b : SymConfig :=
  (GoLean.Sym.Config.next (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.addr
         (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.ref "rd") { key := "raft.Ready" } "Messages"))
       (GoLean.GoCore.Expr.var "$c1810")]]) ([[("$c1810", GoLean.Loc.base { id := 6716 }), ("$c1809", GoLean.Loc.base { id := 6714 })],
 [("$c1808", GoLean.Loc.base { id := 6711 })],
 [("m", GoLean.Loc.base { id := 6710 })],
 [("$rfirst", GoLean.Loc.base { id := 6709 }),
  ("$ridx", GoLean.Loc.base { id := 6708 }),
  ("$rlen", GoLean.Loc.base { id := 6707 }),
  ("$rcoll", GoLean.Loc.base { id := 6706 })],
 [],
 [("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$c1808", GoLean.Loc.base { id := 6711 })],
 [("m", GoLean.Loc.base { id := 6710 })],
 [("$rfirst", GoLean.Loc.base { id := 6709 }),
  ("$ridx", GoLean.Loc.base { id := 6708 }),
  ("$rlen", GoLean.Loc.base { id := 6707 }),
  ("$rcoll", GoLean.Loc.base { id := 6706 })],
 [],
 [("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.seq ([]) ([[("m", GoLean.Loc.base { id := 6710 })],
 [("$rfirst", GoLean.Loc.base { id := 6709 }),
  ("$ridx", GoLean.Loc.base { id := 6708 }),
  ("$rlen", GoLean.Loc.base { id := 6707 }),
  ("$rcoll", GoLean.Loc.base { id := 6706 })],
 [],
 [("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.loop (GoLean.GoCore.Expr.boolLit true) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "$rfirst")
      (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$rfirst") (GoLean.GoCore.Expr.boolLit false))
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
      { id := "m", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
    GoLean.GoCore.Stmt.assign
      (GoLean.GoCore.Assignee.var "m")
      (GoLean.GoCore.Expr.indexGet (GoLean.GoCore.Expr.var "$rcoll") (GoLean.GoCore.Expr.var "$ridx")),
    GoLean.GoCore.Stmt.block
      #[]
      #[GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization
              { id := "$c1808", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c1808"]
              { key := "raftpb.Message.GetTo" }
              #[GoLean.GoCore.Expr.var "m"]],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.neqCmp
            (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
            (GoLean.GoCore.Expr.var "$c1808")
            (GoLean.GoCore.Expr.fieldGet
              (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "r") (GoLean.GoCore.Ty.defined { key := "raft.raft" }))
              { key := "raft.raft" }
              "id"))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c1809",
                      typ := GoLean.GoCore.Ty.slice
                               (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                  GoLean.GoCore.Stmt.makeSlice
                    (GoLean.GoCore.Assignee.var "$c1809")
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                    (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                    (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.indexAddr
                        (GoLean.GoCore.Expr.var "$c1809")
                        (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                    (GoLean.GoCore.Expr.var "m")],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c1810",
                      typ := GoLean.GoCore.Ty.slice
                               (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                  GoLean.GoCore.Stmt.appendSlice
                    (GoLean.GoCore.Assignee.var "$c1810")
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                    (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Messages")
                    (GoLean.GoCore.Expr.var "$c1809")],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.ref "rd") { key := "raft.Ready" } "Messages"))
                    (GoLean.GoCore.Expr.var "$c1810")]])
          (GoLean.GoCore.Stmt.seqn #[])]]) ([[("$rfirst", GoLean.Loc.base { id := 6709 }),
  ("$ridx", GoLean.Loc.base { id := 6708 }),
  ("$rlen", GoLean.Loc.base { id := 6707 }),
  ("$rcoll", GoLean.Loc.base { id := 6706 })],
 [],
 [("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$rfirst", GoLean.Loc.base { id := 6709 }),
  ("$ridx", GoLean.Loc.base { id := 6708 }),
  ("$rlen", GoLean.Loc.base { id := 6707 }),
  ("$rcoll", GoLean.Loc.base { id := 6706 })],
 [],
 [("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.seq ([]) ([[],
 [("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rd"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("$c1801", GoLean.Loc.base { id := 6699 }),
  ("$c1800", GoLean.Loc.base { id := 6685 }),
  ("$c1798", GoLean.Loc.base { id := 6679 }),
  ("rd", GoLean.Loc.base { id := 6632 }),
  ("$c1795", GoLean.Loc.base { id := 6631 }),
  ("$c1794", GoLean.Loc.base { id := 6537 }),
  ("$c1793", GoLean.Loc.base { id := 6534 }),
  ("$c1792", GoLean.Loc.base { id := 6533 }),
  ("$c1791", GoLean.Loc.base { id := 6526 }),
  ("r", GoLean.Loc.base { id := 6525 })],
 [("$res0", GoLean.Loc.base { id := 6524 }), ("rn", GoLean.Loc.base { id := 6523 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "rd"])]) ([[("rd", GoLean.Loc.base { id := 6522 })],
 [("$res0", GoLean.Loc.base { id := 6521 }), ("rn", GoLean.Loc.base { id := 6520 })]]) ([GoLean.Loc.base { id := 6524 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.call
   #[]
   { key := "raft.RawNode.acceptReady" }
   #[GoLean.GoCore.Expr.var "rn", GoLean.GoCore.Expr.var "rd"],
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rd"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("rd", GoLean.Loc.base { id := 6522 })],
 [("$res0", GoLean.Loc.base { id := 6521 }), ("rn", GoLean.Loc.base { id := 6520 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "rd"])]) ([[("rd", GoLean.Loc.base { id := 6519 })],
 [("$c2284", GoLean.Loc.base { id := 6508 })],
 [("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) ([GoLean.Loc.base { id := 6521 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2285", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2285"]
       { key := "raft.IsEmptyHardState" }
       #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "$c2285"))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$c2286", typ := GoLean.GoCore.Ty.interface { key := "error" } },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2286"]
             { key := "raft.MemoryStorage.SetHardState" }
             #[GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "nd")
                   (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                 { key := "main.twinNode" }
                 "st",
               GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.neqCmp
           (GoLean.GoCore.Ty.interface { key := "error" })
           (GoLean.GoCore.Expr.var "$c2286")
           (GoLean.GoCore.Expr.nil none))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.addr
                     (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                   (GoLean.GoCore.Expr.boolLit true)],
             GoLean.GoCore.Stmt.call
               #[]
               { key := "main.twin.viol" }
               #[GoLean.GoCore.Expr.var "t",
                 GoLean.GoCore.Expr.stringLit
                   { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 83, 101, 116, 72, 97, 114, 100, 83, 116, 97,
                                116, 101, 32, 102, 97, 105, 108, 101, 100] }],
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
                 GoLean.GoCore.Stmt.returnStmt]])
         (GoLean.GoCore.Stmt.seqn #[]),
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$c2287", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2287"]
             { key := "raftpb.HardState.GetTerm" }
             #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.addr
               (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "term"))
             (GoLean.GoCore.Expr.var "$c2287")],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$c2288", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2288"]
             { key := "raftpb.HardState.GetCommit" }
             #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.addr
               (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "commit"))
             (GoLean.GoCore.Expr.var "$c2288")]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.greaterCmp
     (GoLean.GoCore.Expr.length
       (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Entries")
       (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))))
     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$c2289", typ := GoLean.GoCore.Ty.interface { key := "error" } },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2289"]
             { key := "raft.MemoryStorage.Append" }
             #[GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "nd")
                   (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                 { key := "main.twinNode" }
                 "st",
               GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Entries"]],
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.neqCmp
           (GoLean.GoCore.Ty.interface { key := "error" })
           (GoLean.GoCore.Expr.var "$c2289")
           (GoLean.GoCore.Expr.nil none))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.addr
                     (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                   (GoLean.GoCore.Expr.boolLit true)],
             GoLean.GoCore.Stmt.call
               #[]
               { key := "main.twin.viol" }
               #[GoLean.GoCore.Expr.var "t",
                 GoLean.GoCore.Expr.stringLit
                   { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 65, 112, 112, 101, 110, 100, 32, 102, 97, 105,
                                108, 101, 100] }],
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
                 GoLean.GoCore.Stmt.returnStmt]])
         (GoLean.GoCore.Stmt.seqn #[])])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2290", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2290"]
       { key := "raft.IsEmptySnap" }
       #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Snapshot"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "$c2290"))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.addr
               (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
             (GoLean.GoCore.Expr.boolLit true)],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.viol" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.stringLit
             { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32,
                          115, 110, 97, 112, 115, 104, 111, 116] }],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
           GoLean.GoCore.Stmt.returnStmt]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.neqCmp
     (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
     (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
     (GoLean.GoCore.Expr.nil none))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.addr
               (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "state"))
             (GoLean.GoCore.Expr.fieldGet
               (GoLean.GoCore.Expr.deref
                 (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
                 (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
               { key := "raft.SoftState" }
               "RaftState")],
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.eqCmp
           (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
           (GoLean.GoCore.Expr.fieldGet
             (GoLean.GoCore.Expr.deref
               (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
               (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
             { key := "raft.SoftState" }
             "RaftState")
           (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64)))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.assign
               (GoLean.GoCore.Assignee.addr
                 (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "claims"))
               (GoLean.GoCore.Expr.add
                 (GoLean.GoCore.Expr.fieldGet
                   (GoLean.GoCore.Expr.deref
                     (GoLean.GoCore.Expr.var "t")
                     (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                   { key := "main.twin" }
                   "claims")
                 (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.initialization
                   { id := "prev", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                 GoLean.GoCore.Stmt.initialization { id := "ok", typ := GoLean.GoCore.Ty.bool },
                 GoLean.GoCore.Stmt.mapLookup
                   (GoLean.GoCore.Assignee.var "prev")
                   (GoLean.GoCore.Assignee.var "ok")
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "t")
                       (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                     { key := "main.twin" }
                     "leaderOf")
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "nd")
                       (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                     { key := "main.twinNode" }
                     "term")
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))],
             GoLean.GoCore.Stmt.ifThenElse
               (GoLean.GoCore.Expr.and
                 (GoLean.GoCore.Expr.var "ok")
                 (GoLean.GoCore.Expr.neqCmp
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.var "prev")
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "nd")
                       (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                     { key := "main.twinNode" }
                     "id")))
               (GoLean.GoCore.Stmt.block
                 #[]
                 #[GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.initialization { id := "$c2291", typ := GoLean.GoCore.Ty.string },
                       GoLean.GoCore.Stmt.call
                         #[GoLean.GoCore.Assignee.var "$c2291"]
                         { key := "utoa" }
                         #[GoLean.GoCore.Expr.fieldGet
                             (GoLean.GoCore.Expr.deref
                               (GoLean.GoCore.Expr.var "nd")
                               (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                             { key := "main.twinNode" }
                             "term"]],
                   GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.initialization { id := "$c2292", typ := GoLean.GoCore.Ty.string },
                       GoLean.GoCore.Stmt.call
                         #[GoLean.GoCore.Assignee.var "$c2292"]
                         { key := "utoa" }
                         #[GoLean.GoCore.Expr.var "prev"]],
                   GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.initialization { id := "$c2293", typ := GoLean.GoCore.Ty.string },
                       GoLean.GoCore.Stmt.call
                         #[GoLean.GoCore.Assignee.var "$c2293"]
                         { key := "utoa" }
                         #[GoLean.GoCore.Expr.fieldGet
                             (GoLean.GoCore.Expr.deref
                               (GoLean.GoCore.Expr.var "nd")
                               (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                             { key := "main.twinNode" }
                             "id"]],
                   GoLean.GoCore.Stmt.call
                     #[]
                     { key := "main.twin.viol" }
                     #[GoLean.GoCore.Expr.var "t",
                       GoLean.GoCore.Expr.add
                         (GoLean.GoCore.Expr.add
                           (GoLean.GoCore.Expr.add
                             (GoLean.GoCore.Expr.add
                               (GoLean.GoCore.Expr.add
                                 (GoLean.GoCore.Expr.stringLit
                                   { bytes := #[83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102,
                                                101, 116, 121, 58, 32, 116, 101, 114, 109, 32] })
                                 (GoLean.GoCore.Expr.var "$c2291"))
                               (GoLean.GoCore.Expr.stringLit
                                 { bytes := #[32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116, 104,
                                              32, 110, 111, 100, 101, 32] }))
                             (GoLean.GoCore.Expr.var "$c2292"))
                           (GoLean.GoCore.Expr.stringLit { bytes := #[32, 97, 110, 100, 32, 110, 111, 100, 101, 32] }))
                         (GoLean.GoCore.Expr.var "$c2293")]])
               (GoLean.GoCore.Stmt.seqn #[]),
             GoLean.GoCore.Stmt.mapAssign
               (GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "t")
                   (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                 { key := "main.twin" }
                 "leaderOf")
               (GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "nd")
                   (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                 { key := "main.twinNode" }
                 "term")
               (GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "nd")
                   (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                 { key := "main.twinNode" }
                 "id")
               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))])
         (GoLean.GoCore.Stmt.seqn #[])])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.block
   #[]
   #[GoLean.GoCore.Stmt.initialization
       { id := "$rcoll",
         typ := GoLean.GoCore.Ty.slice
                  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$rcoll")
       (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Messages"),
     GoLean.GoCore.Stmt.initialization { id := "$rlen", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$rlen")
       (GoLean.GoCore.Expr.length (GoLean.GoCore.Expr.var "$rcoll") none),
     GoLean.GoCore.Stmt.initialization { id := "$ridx", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
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
             (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$rfirst") (GoLean.GoCore.Expr.boolLit false))
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
             { id := "m", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
           GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "m")
             (GoLean.GoCore.Expr.indexGet (GoLean.GoCore.Expr.var "$rcoll") (GoLean.GoCore.Expr.var "$ridx")),
           GoLean.GoCore.Stmt.block
             #[]
             #[GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.initialization
                     { id := "$c2294",
                       typ := GoLean.GoCore.Ty.slice
                                (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                   GoLean.GoCore.Stmt.makeSlice
                     (GoLean.GoCore.Assignee.var "$c2294")
                     (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                     (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                   GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.addr
                       (GoLean.GoCore.Expr.indexAddr
                         (GoLean.GoCore.Expr.var "$c2294")
                         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                     (GoLean.GoCore.Expr.var "m")],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.initialization
                     { id := "$c2295",
                       typ := GoLean.GoCore.Ty.slice
                                (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                   GoLean.GoCore.Stmt.appendSlice
                     (GoLean.GoCore.Assignee.var "$c2295")
                     (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                     (GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "t")
                         (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                       { key := "main.twin" }
                       "net")
                     (GoLean.GoCore.Expr.var "$c2294")],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.addr
                       (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "net"))
                     (GoLean.GoCore.Expr.var "$c2295")],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.initialization
                     { id := "$c2296", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                   GoLean.GoCore.Stmt.makeSlice
                     (GoLean.GoCore.Assignee.var "$c2296")
                     (GoLean.GoCore.Ty.bool)
                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                     (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                   GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.addr
                       (GoLean.GoCore.Expr.indexAddr
                         (GoLean.GoCore.Expr.var "$c2296")
                         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                     (GoLean.GoCore.Expr.boolLit true)],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.initialization
                     { id := "$c2297", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                   GoLean.GoCore.Stmt.appendSlice
                     (GoLean.GoCore.Assignee.var "$c2297")
                     (GoLean.GoCore.Ty.bool)
                     (GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "t")
                         (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                       { key := "main.twin" }
                       "live")
                     (GoLean.GoCore.Expr.var "$c2296")],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.addr
                       (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "live"))
                     (GoLean.GoCore.Expr.var "$c2297")]]])],
 GoLean.GoCore.Stmt.block
   #[]
   #[GoLean.GoCore.Stmt.initialization
       { id := "$rcoll",
         typ := GoLean.GoCore.Ty.slice
                  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$rcoll")
       (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "CommittedEntries"),
     GoLean.GoCore.Stmt.initialization { id := "$rlen", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$rlen")
       (GoLean.GoCore.Expr.length (GoLean.GoCore.Expr.var "$rcoll") none),
     GoLean.GoCore.Stmt.initialization { id := "$ridx", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
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
             (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$rfirst") (GoLean.GoCore.Expr.boolLit false))
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
             { id := "e", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }) },
           GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "e")
             (GoLean.GoCore.Expr.indexGet (GoLean.GoCore.Expr.var "$rcoll") (GoLean.GoCore.Expr.var "$ridx")),
           GoLean.GoCore.Stmt.block
             #[]
             #[GoLean.GoCore.Stmt.call
                 #[]
                 { key := "main.twin.apply" }
                 #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "nd", GoLean.GoCore.Expr.var "e"]]])],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "raft.RawNode.Advance" }
   #[GoLean.GoCore.Expr.fieldGet
       (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "nd") (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
       { key := "main.twinNode" }
       "rn",
     GoLean.GoCore.Expr.var "rd"]]) ([[("rd", GoLean.Loc.base { id := 6519 })],
 [("$c2284", GoLean.Loc.base { id := 6508 })],
 [("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$c2284", GoLean.Loc.base { id := 6508 })],
 [("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.loop (GoLean.GoCore.Expr.boolLit true) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "$forFirst")
      (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$forFirst") (GoLean.GoCore.Expr.boolLit false))
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.seqn
      #[GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "$c2284", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c2284"]
              { key := "raft.RawNode.HasReady" }
              #[GoLean.GoCore.Expr.fieldGet
                  (GoLean.GoCore.Expr.deref
                    (GoLean.GoCore.Expr.var "nd")
                    (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                  { key := "main.twinNode" }
                  "rn"]]],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "$c2284")
      (GoLean.GoCore.Stmt.seqn #[])
      (GoLean.GoCore.Stmt.breakStmt),
    GoLean.GoCore.Stmt.block
      #[]
      #[GoLean.GoCore.Stmt.assign
          (GoLean.GoCore.Assignee.var "rounds")
          (GoLean.GoCore.Expr.add
            (GoLean.GoCore.Expr.var "rounds")
            (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.var "rounds")
            (GoLean.GoCore.Expr.intLit 64 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                    (GoLean.GoCore.Expr.boolLit true)],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.viol" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.stringLit
                    { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 104, 97, 114, 118, 101, 115, 116, 32, 100,
                                 105, 100, 32, 110, 111, 116, 32, 113, 117, 105, 101, 115, 99, 101, 32, 105, 110, 32,
                                 54, 52, 32, 114, 111, 117, 110, 100, 115] }],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
                  GoLean.GoCore.Stmt.returnStmt]])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "rd", typ := GoLean.GoCore.Ty.defined { key := "raft.Ready" } },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "rd"]
              { key := "raft.RawNode.Ready" }
              #[GoLean.GoCore.Expr.fieldGet
                  (GoLean.GoCore.Expr.deref
                    (GoLean.GoCore.Expr.var "nd")
                    (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                  { key := "main.twinNode" }
                  "rn"]],
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "$c2285", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c2285"]
              { key := "raft.IsEmptyHardState" }
              #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "$c2285"))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2286", typ := GoLean.GoCore.Ty.interface { key := "error" } },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2286"]
                    { key := "raft.MemoryStorage.SetHardState" }
                    #[GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "nd")
                          (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                        { key := "main.twinNode" }
                        "st",
                      GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.neqCmp
                  (GoLean.GoCore.Ty.interface { key := "error" })
                  (GoLean.GoCore.Expr.var "$c2286")
                  (GoLean.GoCore.Expr.nil none))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.addr
                            (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                          (GoLean.GoCore.Expr.boolLit true)],
                    GoLean.GoCore.Stmt.call
                      #[]
                      { key := "main.twin.viol" }
                      #[GoLean.GoCore.Expr.var "t",
                        GoLean.GoCore.Expr.stringLit
                          { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 83, 101, 116, 72, 97, 114, 100, 83,
                                       116, 97, 116, 101, 32, 102, 97, 105, 108, 101, 100] }],
                    GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$res0")
                          (GoLean.GoCore.Expr.var "rounds"),
                        GoLean.GoCore.Stmt.returnStmt]])
                (GoLean.GoCore.Stmt.seqn #[]),
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2287", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2287"]
                    { key := "raftpb.HardState.GetTerm" }
                    #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "term"))
                    (GoLean.GoCore.Expr.var "$c2287")],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2288", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2288"]
                    { key := "raftpb.HardState.GetCommit" }
                    #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "commit"))
                    (GoLean.GoCore.Expr.var "$c2288")]])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.length
              (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Entries")
              (some (GoLean.GoCore.Ty.slice
                 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))))
            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2289", typ := GoLean.GoCore.Ty.interface { key := "error" } },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2289"]
                    { key := "raft.MemoryStorage.Append" }
                    #[GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "nd")
                          (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                        { key := "main.twinNode" }
                        "st",
                      GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Entries"]],
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.neqCmp
                  (GoLean.GoCore.Ty.interface { key := "error" })
                  (GoLean.GoCore.Expr.var "$c2289")
                  (GoLean.GoCore.Expr.nil none))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.addr
                            (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                          (GoLean.GoCore.Expr.boolLit true)],
                    GoLean.GoCore.Stmt.call
                      #[]
                      { key := "main.twin.viol" }
                      #[GoLean.GoCore.Expr.var "t",
                        GoLean.GoCore.Expr.stringLit
                          { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 65, 112, 112, 101, 110, 100, 32, 102,
                                       97, 105, 108, 101, 100] }],
                    GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$res0")
                          (GoLean.GoCore.Expr.var "rounds"),
                        GoLean.GoCore.Stmt.returnStmt]])
                (GoLean.GoCore.Stmt.seqn #[])])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "$c2290", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c2290"]
              { key := "raft.IsEmptySnap" }
              #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Snapshot"]],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "$c2290"))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                    (GoLean.GoCore.Expr.boolLit true)],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.viol" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.stringLit
                    { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101,
                                 100, 32, 115, 110, 97, 112, 115, 104, 111, 116] }],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
                  GoLean.GoCore.Stmt.returnStmt]])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.neqCmp
            (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
            (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
            (GoLean.GoCore.Expr.nil none))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "state"))
                    (GoLean.GoCore.Expr.fieldGet
                      (GoLean.GoCore.Expr.deref
                        (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
                        (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
                      { key := "raft.SoftState" }
                      "RaftState")],
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.eqCmp
                  (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
                  (GoLean.GoCore.Expr.fieldGet
                    (GoLean.GoCore.Expr.deref
                      (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
                      (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
                    { key := "raft.SoftState" }
                    "RaftState")
                  (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64)))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.addr
                        (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "claims"))
                      (GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.fieldGet
                          (GoLean.GoCore.Expr.deref
                            (GoLean.GoCore.Expr.var "t")
                            (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                          { key := "main.twin" }
                          "claims")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                    GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "prev", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                        GoLean.GoCore.Stmt.initialization { id := "ok", typ := GoLean.GoCore.Ty.bool },
                        GoLean.GoCore.Stmt.mapLookup
                          (GoLean.GoCore.Assignee.var "prev")
                          (GoLean.GoCore.Assignee.var "ok")
                          (GoLean.GoCore.Expr.fieldGet
                            (GoLean.GoCore.Expr.deref
                              (GoLean.GoCore.Expr.var "t")
                              (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                            { key := "main.twin" }
                            "leaderOf")
                          (GoLean.GoCore.Expr.fieldGet
                            (GoLean.GoCore.Expr.deref
                              (GoLean.GoCore.Expr.var "nd")
                              (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                            { key := "main.twinNode" }
                            "term")
                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))],
                    GoLean.GoCore.Stmt.ifThenElse
                      (GoLean.GoCore.Expr.and
                        (GoLean.GoCore.Expr.var "ok")
                        (GoLean.GoCore.Expr.neqCmp
                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                          (GoLean.GoCore.Expr.var "prev")
                          (GoLean.GoCore.Expr.fieldGet
                            (GoLean.GoCore.Expr.deref
                              (GoLean.GoCore.Expr.var "nd")
                              (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                            { key := "main.twinNode" }
                            "id")))
                      (GoLean.GoCore.Stmt.block
                        #[]
                        #[GoLean.GoCore.Stmt.seqn
                            #[GoLean.GoCore.Stmt.initialization { id := "$c2291", typ := GoLean.GoCore.Ty.string },
                              GoLean.GoCore.Stmt.call
                                #[GoLean.GoCore.Assignee.var "$c2291"]
                                { key := "utoa" }
                                #[GoLean.GoCore.Expr.fieldGet
                                    (GoLean.GoCore.Expr.deref
                                      (GoLean.GoCore.Expr.var "nd")
                                      (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                                    { key := "main.twinNode" }
                                    "term"]],
                          GoLean.GoCore.Stmt.seqn
                            #[GoLean.GoCore.Stmt.initialization { id := "$c2292", typ := GoLean.GoCore.Ty.string },
                              GoLean.GoCore.Stmt.call
                                #[GoLean.GoCore.Assignee.var "$c2292"]
                                { key := "utoa" }
                                #[GoLean.GoCore.Expr.var "prev"]],
                          GoLean.GoCore.Stmt.seqn
                            #[GoLean.GoCore.Stmt.initialization { id := "$c2293", typ := GoLean.GoCore.Ty.string },
                              GoLean.GoCore.Stmt.call
                                #[GoLean.GoCore.Assignee.var "$c2293"]
                                { key := "utoa" }
                                #[GoLean.GoCore.Expr.fieldGet
                                    (GoLean.GoCore.Expr.deref
                                      (GoLean.GoCore.Expr.var "nd")
                                      (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                                    { key := "main.twinNode" }
                                    "id"]],
                          GoLean.GoCore.Stmt.call
                            #[]
                            { key := "main.twin.viol" }
                            #[GoLean.GoCore.Expr.var "t",
                              GoLean.GoCore.Expr.add
                                (GoLean.GoCore.Expr.add
                                  (GoLean.GoCore.Expr.add
                                    (GoLean.GoCore.Expr.add
                                      (GoLean.GoCore.Expr.add
                                        (GoLean.GoCore.Expr.stringLit
                                          { bytes := #[83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97,
                                                       102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32] })
                                        (GoLean.GoCore.Expr.var "$c2291"))
                                      (GoLean.GoCore.Expr.stringLit
                                        { bytes := #[32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116,
                                                     104, 32, 110, 111, 100, 101, 32] }))
                                    (GoLean.GoCore.Expr.var "$c2292"))
                                  (GoLean.GoCore.Expr.stringLit
                                    { bytes := #[32, 97, 110, 100, 32, 110, 111, 100, 101, 32] }))
                                (GoLean.GoCore.Expr.var "$c2293")]])
                      (GoLean.GoCore.Stmt.seqn #[]),
                    GoLean.GoCore.Stmt.mapAssign
                      (GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "t")
                          (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                        { key := "main.twin" }
                        "leaderOf")
                      (GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "nd")
                          (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                        { key := "main.twinNode" }
                        "term")
                      (GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "nd")
                          (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                        { key := "main.twinNode" }
                        "id")
                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))])
                (GoLean.GoCore.Stmt.seqn #[])])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.block
          #[]
          #[GoLean.GoCore.Stmt.initialization
              { id := "$rcoll",
                typ := GoLean.GoCore.Ty.slice
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rcoll")
              (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Messages"),
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
                    { id := "m",
                      typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "m")
                    (GoLean.GoCore.Expr.indexGet (GoLean.GoCore.Expr.var "$rcoll") (GoLean.GoCore.Expr.var "$ridx")),
                  GoLean.GoCore.Stmt.block
                    #[]
                    #[GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.initialization
                            { id := "$c2294",
                              typ := GoLean.GoCore.Ty.slice
                                       (GoLean.GoCore.Ty.pointer
                                         (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                          GoLean.GoCore.Stmt.makeSlice
                            (GoLean.GoCore.Assignee.var "$c2294")
                            (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                            (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                            (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                          GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.addr
                              (GoLean.GoCore.Expr.indexAddr
                                (GoLean.GoCore.Expr.var "$c2294")
                                (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                            (GoLean.GoCore.Expr.var "m")],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.initialization
                            { id := "$c2295",
                              typ := GoLean.GoCore.Ty.slice
                                       (GoLean.GoCore.Ty.pointer
                                         (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                          GoLean.GoCore.Stmt.appendSlice
                            (GoLean.GoCore.Assignee.var "$c2295")
                            (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                            (GoLean.GoCore.Expr.fieldGet
                              (GoLean.GoCore.Expr.deref
                                (GoLean.GoCore.Expr.var "t")
                                (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                              { key := "main.twin" }
                              "net")
                            (GoLean.GoCore.Expr.var "$c2294")],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.addr
                              (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "net"))
                            (GoLean.GoCore.Expr.var "$c2295")],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.initialization
                            { id := "$c2296", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                          GoLean.GoCore.Stmt.makeSlice
                            (GoLean.GoCore.Assignee.var "$c2296")
                            (GoLean.GoCore.Ty.bool)
                            (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                            (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                          GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.addr
                              (GoLean.GoCore.Expr.indexAddr
                                (GoLean.GoCore.Expr.var "$c2296")
                                (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                            (GoLean.GoCore.Expr.boolLit true)],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.initialization
                            { id := "$c2297", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                          GoLean.GoCore.Stmt.appendSlice
                            (GoLean.GoCore.Assignee.var "$c2297")
                            (GoLean.GoCore.Ty.bool)
                            (GoLean.GoCore.Expr.fieldGet
                              (GoLean.GoCore.Expr.deref
                                (GoLean.GoCore.Expr.var "t")
                                (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                              { key := "main.twin" }
                              "live")
                            (GoLean.GoCore.Expr.var "$c2296")],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.addr
                              (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "live"))
                            (GoLean.GoCore.Expr.var "$c2297")]]])],
        GoLean.GoCore.Stmt.block
          #[]
          #[GoLean.GoCore.Stmt.initialization
              { id := "$rcoll",
                typ := GoLean.GoCore.Ty.slice
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rcoll")
              (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "CommittedEntries"),
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
                    { id := "e", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "e")
                    (GoLean.GoCore.Expr.indexGet (GoLean.GoCore.Expr.var "$rcoll") (GoLean.GoCore.Expr.var "$ridx")),
                  GoLean.GoCore.Stmt.block
                    #[]
                    #[GoLean.GoCore.Stmt.call
                        #[]
                        { key := "main.twin.apply" }
                        #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "nd", GoLean.GoCore.Expr.var "e"]]])],
        GoLean.GoCore.Stmt.call
          #[]
          { key := "raft.RawNode.Advance" }
          #[GoLean.GoCore.Expr.fieldGet
              (GoLean.GoCore.Expr.deref
                (GoLean.GoCore.Expr.var "nd")
                (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
              { key := "main.twinNode" }
              "rn",
            GoLean.GoCore.Expr.var "rd"]]]) ([[("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$cr0"])]) ([[("$cr0", GoLean.Loc.base { id := 6502 }),
  ("to", GoLean.Loc.base { id := 6138 }),
  ("$c2316", GoLean.Loc.base { id := 6135 }),
  ("m", GoLean.Loc.base { id := 6134 })],
 [("i", GoLean.Loc.base { id := 6133 }), ("t", GoLean.Loc.base { id := 6132 })]]) ([GoLean.Loc.base { id := 6505 }]) [] (GoLean.Sym.Cont.seq ([]) ([[("$cr0", GoLean.Loc.base { id := 6502 }),
  ("to", GoLean.Loc.base { id := 6138 }),
  ("$c2316", GoLean.Loc.base { id := 6135 }),
  ("m", GoLean.Loc.base { id := 6134 })],
 [("i", GoLean.Loc.base { id := 6133 }), ("t", GoLean.Loc.base { id := 6132 })]]) (GoLean.Sym.Cont.frame ([]) ([[("$c2241", GoLean.Loc.base { id := 6125 }),
  ("$c2240", GoLean.Loc.base { id := 6122 }),
  ("$c2239", GoLean.Loc.base { id := 6114 }),
  ("$c2238", GoLean.Loc.base { id := 6111 }),
  ("$c2237", GoLean.Loc.base { id := 6105 }),
  ("$c2236", GoLean.Loc.base { id := 6097 }),
  ("m", GoLean.Loc.base { id := 6096 }),
  ("picked", GoLean.Loc.base { id := 6094 })],
 [("live", GoLean.Loc.base { id := 6088 }), ("$c2235", GoLean.Loc.base { id := 6086 })],
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
 GoLean.GoCore.Stmt.continueStmt]) ([[("$c2241", GoLean.Loc.base { id := 6125 }),
  ("$c2240", GoLean.Loc.base { id := 6122 }),
  ("$c2239", GoLean.Loc.base { id := 6114 }),
  ("$c2238", GoLean.Loc.base { id := 6111 }),
  ("$c2237", GoLean.Loc.base { id := 6105 }),
  ("$c2236", GoLean.Loc.base { id := 6097 }),
  ("m", GoLean.Loc.base { id := 6096 }),
  ("picked", GoLean.Loc.base { id := 6094 })],
 [("live", GoLean.Loc.base { id := 6088 }), ("$c2235", GoLean.Loc.base { id := 6086 })],
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
 GoLean.GoCore.Stmt.breakStmt]) ([[("live", GoLean.Loc.base { id := 6088 }), ("$c2235", GoLean.Loc.base { id := 6086 })],
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
  ("$res0", GoLean.Loc.base { id := 98 })]]) (GoLean.Sym.Cont.frame ([]) ([]) ([]) [] (GoLean.Sym.Cont.stop) false)) false)))))))) false)) false)))))) false)) false)))))))))

def maS1 : SymState :=
  (GoLean.Sym.State.mk
  [((GoLean.Loc.base { id := 15 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 57 })))),
  ((GoLean.Loc.base { id := 57 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Commit"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 121 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twin" })) (GoLean.Sym.Value.struct ({ key := "main.twin" }) #[(("nodes"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 1764 }), offset := 0, len := 3, cap := 4 }))),
  (("net"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6077 }), offset := 0, len := 1, cap := 1 }))),
  (("live"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6078 }), offset := 0, len := 1, cap := 1 }))),
  (("leaderOf"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 115 }) }))),
  (("byIndex"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 118 }) }))),
  (("claims"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("violations"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("pending"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 136 }), offset := 0, len := 2, cap := 4 }))),
  (("driven"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("seq"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.int))),
  (("trace"), (GoLean.Sym.Value.string ({ bytes := #[91, 99, 104, 111, 105, 99, 101, 45, 100, 114, 105, 118, 101, 110, 93, 10, 99, 97, 109, 112, 97, 105, 103,
             110, 49, 114, 49, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 51, 45, 62, 50] }))),
  (("halt"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1770 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "main.twinNode" })) (GoLean.Sym.Value.struct ({ key := "main.twinNode" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("rn"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 }))),
  (("st"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 }))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("commit"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("lastTrm"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("got"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 1767 }) })))]))),
  ((GoLean.Loc.base { id := 1779 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.struct ({ key := "raft.MemoryStorage" }) #[(("Mutex"), (GoLean.Sym.Value.syncData (GoLean.SyncPrim.mutex false))),
  (("hardState"), (GoLean.Sym.Value.nil)),
  (("snapshot"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1858 }))),
  (("ents"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 1900 }), offset := 0, len := 1, cap := 1 }))),
  (("callStats"), (GoLean.Sym.Value.struct ({ key := "raft.inMemStorageCallStats" }) #[(("initialState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int))),
  (("firstIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.add
        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 4))
        (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.int))),
  (("lastIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 10)))) (GoLean.GoCore.IntKind.int))),
  (("entries"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.int))),
  (("term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.int))),
  (("snapshot"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.int)))]))]))),
  ((GoLean.Loc.base { id := 1895 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 1898 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1886 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1895 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 1900 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1898 }))]))),
  ((GoLean.Loc.base { id := 1949 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })) (GoLean.Sym.Value.struct ({ key := "raft.raftLog" }) #[(("storage"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 })))),
  (("unstable"), (GoLean.Sym.Value.struct ({ key := "raft.unstable" }) #[(("snapshot"), (GoLean.Sym.Value.nil)),
  (("entries"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 }))),
  (("offset"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("snapshotInProgress"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("offsetInProgress"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 }))))])),
  (("committed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("applying"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("applied"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("maxApplyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("applyingEntsPaused"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 1989 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.raft" })) (GoLean.Sym.Value.struct ({ key := "raft.raft" }) #[(("id"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64))),
  (("Term"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("Vote"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("readStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("raftLog"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 }))),
  (("maxMsgSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1048576) (GoLean.GoCore.IntKind.uint64))),
  (("maxUncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64))),
  (("trk"), (GoLean.Sym.Value.struct ({ key := "tracker.ProgressTracker" }) #[(("Config"), (GoLean.Sym.Value.struct ({ key := "tracker.Config" }) #[(("Voters"), (GoLean.Sym.Value.array #[(GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 2686 }) })),
  (GoLean.Sym.Value.map ({ base := none }))])),
  (("AutoLeave"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("Learners"), (GoLean.Sym.Value.map ({ base := none }))),
  (("LearnersNext"), (GoLean.Sym.Value.map ({ base := none })))])),
  (("Progress"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 2703 }) }))),
  (("Votes"), (GoLean.Sym.Value.map ({ base := some (GoLean.Loc.base { id := 3059 }) }))),
  (("MaxInflight"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 256) (GoLean.GoCore.IntKind.int))),
  (("MaxInflightBytes"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 18446744073709551615) (GoLean.GoCore.IntKind.uint64)))])),
  (("state"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("isLearner"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("msgs"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("msgsAfterAppend"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6499 }), offset := 0, len := 1, cap := 4 }))),
  (("lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64))),
  (("leadTransferee"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("pendingConfIndex"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("disableConfChangeValidation"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("uncommittedSize"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("readOnly"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3199 }))),
  (("electionElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("heartbeatElapsed"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int))),
  (("checkQuorum"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("preVote"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("heartbeatTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.int))),
  (("electionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("randomizedElectionTimeout"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 10) (GoLean.GoCore.IntKind.int))),
  (("disableProposalForwarding"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("stepDownOnRemoval"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("tick"), (GoLean.Sym.Value.funcVal ({ key := "raft.raft.tickElection" }) [(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 }))])),
  (("step"), (GoLean.Sym.Value.funcVal ({ key := "raft.stepFollower" }) [])),
  (("logger"), (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 97 })))),
  (("pendingReadIndexMessages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("traceLogger"), (GoLean.Sym.Value.nil))]))),
  ((GoLean.Loc.base { id := 3342 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })) (GoLean.Sym.Value.struct ({ key := "raft.RawNode" }) #[(("raft"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 }))),
  (("asyncStorageWrites"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))),
  (("prevSoftSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3344 }))),
  (("prevHardSt"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 }))),
  (("stepsOnAdvance"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 3344 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 3351 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 3354 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 3357 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 3360 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3351 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3354 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3357 })))]))),
  ((GoLean.Loc.base { id := 6075 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6077 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6076 }))]))),
  ((GoLean.Loc.base { id := 6078 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.bool))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false))]))),
  ((GoLean.Loc.base { id := 6080 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 1) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6081 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6082 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Entry" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6080 }))),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6081 }))),
  (("Type"), (GoLean.Sym.Value.nil)),
  (("Data"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 6132 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 6138 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1770 })))),
  ((GoLean.Loc.base { id := 6424 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 })),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 6456 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) (GoLean.Sym.Value.struct ({ key := "raftpb.Message" }) #[(("Type"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6449 }))),
  (("To"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6075 }))),
  (("From"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6463 }))),
  (("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6490 }))),
  (("LogTerm"), (GoLean.Sym.Value.nil)),
  (("Index"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6453 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Commit"), (GoLean.Sym.Value.nil)),
  (("Vote"), (GoLean.Sym.Value.nil)),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("Reject"), (GoLean.Sym.Value.nil)),
  (("RejectHint"), (GoLean.Sym.Value.nil)),
  (("Context"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Responses"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 })))]))),
  ((GoLean.Loc.base { id := 6499 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 })),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)]))),
  ((GoLean.Loc.base { id := 6503 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 121 })))),
  ((GoLean.Loc.base { id := 6504 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1770 })))),
  ((GoLean.Loc.base { id := 6505 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6506 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6507 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6508 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6509 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 })))),
  ((GoLean.Loc.base { id := 6510 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6511 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6512 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6513 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6514 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6515 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6516 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6512 })))),
  ((GoLean.Loc.base { id := 6517 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3344 })))),
  ((GoLean.Loc.base { id := 6518 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6519 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.nil)),
  (("HardState"), (GoLean.Sym.Value.nil)),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 6520 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 })))),
  ((GoLean.Loc.base { id := 6521 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.nil)),
  (("HardState"), (GoLean.Sym.Value.nil)),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))]))),
  ((GoLean.Loc.base { id := 6522 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6640 }))),
  (("HardState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 }))),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6717 }), offset := 0, len := 1, cap := 4 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))]))),
  ((GoLean.Loc.base { id := 6523 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 })))),
  ((GoLean.Loc.base { id := 6524 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6640 }))),
  (("HardState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 }))),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6717 }), offset := 0, len := 1, cap := 4 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))]))),
  ((GoLean.Loc.base { id := 6525 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6526 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6527 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6528 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6529 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6530 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6531 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6532 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.sub (GoLean.Sym.SymInt.lit 2) (GoLean.Sym.SymInt.lit 2))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6533 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6534 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 6535 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3342 })))),
  ((GoLean.Loc.base { id := 6536 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 6537 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6538 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6539 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 6540 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6541 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit true))))),
  ((GoLean.Loc.base { id := 6542 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6543 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit true))))),
  ((GoLean.Loc.base { id := 6544 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6545 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6546 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit false))))),
  ((GoLean.Loc.base { id := 6547 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6548 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6549 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6550 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6551 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.entryEncodingSize" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.sub (GoLean.Sym.SymInt.lit 1048576) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6552 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6553 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6554 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6555 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.add
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
        (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6556 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.entryEncodingSize" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.sub (GoLean.Sym.SymInt.lit 1048576) (GoLean.Sym.SymInt.lit 0))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6557 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6558 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6559 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6560 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6561 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6562 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
          (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6563 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6564 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.uint64)
                  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
                (GoLean.Sym.SymInt.lit 1))))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6565 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6566 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
              (GoLean.Sym.SymInt.lit 1)))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6567 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6568 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6569 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6570 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6571 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6572 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
            (GoLean.Sym.SymInt.lit 1))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6573 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6574 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 })))),
  ((GoLean.Loc.base { id := 6575 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
          (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6576 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "error" })) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6577 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.add
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
        (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6578 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1779 })))),
  ((GoLean.Loc.base { id := 6579 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6580 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6581 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1898 })))),
  ((GoLean.Loc.base { id := 6582 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6583 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.sync (GoLean.GoCore.SyncKind.mutex)))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1779 }) { key := "raft.MemoryStorage" } "Mutex")))),
  ((GoLean.Loc.base { id := 6584 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.sub
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.lit 2)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.uint64)
                  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
            (GoLean.Sym.SymInt.lit 1))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6585 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6586 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.sub
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.lit 2)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
          (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6587 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.sub
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.lit 2)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
        (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6588 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6589 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6590 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.sub
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.lit 2)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6591 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6592 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6593 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.sub
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.uint64)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.uint64)
                    (GoLean.Sym.SymInt.sub
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.uint64)
                        (GoLean.Sym.SymInt.add
                          (GoLean.Sym.SymInt.lit 2)
                          (GoLean.Sym.SymInt.norm
                            (GoLean.GoCore.IntKind.uint64)
                            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))
                      (GoLean.Sym.SymInt.lit 1)))))))
          (GoLean.Sym.SymInt.lit 1)))
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.uint64)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.uint64)
                    (GoLean.Sym.SymInt.add
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.uint64)
                        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))
                      (GoLean.Sym.SymInt.lit 1)))))))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6594 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6595 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6596 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6597 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.uint64)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
          (GoLean.Sym.SymInt.lit 1)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6598 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6599 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6600 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.add (GoLean.Sym.SymInt.lit 1) (GoLean.Sym.SymInt.lit 1))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6601 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.uint64)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.uint64)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.uint64)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))))
            (GoLean.Sym.SymInt.lit 1))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6602 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.lit 2)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6603 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6604 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6605 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.entryEncodingSize" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.uint64)
        (GoLean.Sym.SymInt.sub (GoLean.Sym.SymInt.lit 1048576) (GoLean.Sym.SymInt.lit 0)))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6606 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6607 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.add
                    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.add
                        (GoLean.Sym.SymInt.lit 1)
                        (GoLean.Sym.SymInt.norm
                          (GoLean.GoCore.IntKind.int)
                          (GoLean.Sym.SymInt.norm
                            (GoLean.GoCore.IntKind.int)
                            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.add
                  (GoLean.Sym.SymInt.lit 1)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))))))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6608 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "proto.Message" })) (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 }))))),
  ((GoLean.Loc.base { id := 6609 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.add
                  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.add
                      (GoLean.Sym.SymInt.lit 1)
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.int)
                        (GoLean.Sym.SymInt.norm
                          (GoLean.GoCore.IntKind.int)
                          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.lit 1)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6610 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.interface { key := "proto.Message" })) (GoLean.Sym.Value.interface (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 }))))),
  ((GoLean.Loc.base { id := 6611 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 })))),
  ((GoLean.Loc.base { id := 6612 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit true)))),
  ((GoLean.Loc.base { id := 6613 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 })))),
  ((GoLean.Loc.base { id := 6614 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.add
                    (GoLean.Sym.SymInt.lit 1)
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.int)
                        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.lit 1)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6615 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6082 })))),
  ((GoLean.Loc.base { id := 6616 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.add
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.add
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.add
                  (GoLean.Sym.SymInt.lit 1)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.lit 1)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6617 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.add
            (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.add
                (GoLean.Sym.SymInt.lit 1)
                (GoLean.Sym.SymInt.norm
                  (GoLean.GoCore.IntKind.int)
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.add
          (GoLean.Sym.SymInt.lit 1)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))))))))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6618 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6619 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6620 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6621 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6622 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6623 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6624 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6625 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6626 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6627 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6628 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.entryEncodingSize" })) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.int)
      (GoLean.Sym.SymInt.norm
        (GoLean.GoCore.IntKind.int)
        (GoLean.Sym.SymInt.norm
          (GoLean.GoCore.IntKind.int)
          (GoLean.Sym.SymInt.norm
            (GoLean.GoCore.IntKind.int)
            (GoLean.Sym.SymInt.norm
              (GoLean.GoCore.IntKind.int)
              (GoLean.Sym.SymInt.norm
                (GoLean.GoCore.IntKind.int)
                (GoLean.Sym.SymInt.add
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.norm
                      (GoLean.GoCore.IntKind.int)
                      (GoLean.Sym.SymInt.add
                        (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
                        (GoLean.Sym.SymInt.norm
                          (GoLean.GoCore.IntKind.int)
                          (GoLean.Sym.SymInt.add
                            (GoLean.Sym.SymInt.lit 1)
                            (GoLean.Sym.SymInt.norm
                              (GoLean.GoCore.IntKind.int)
                              (GoLean.Sym.SymInt.norm
                                (GoLean.GoCore.IntKind.int)
                                (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)))))))))
                  (GoLean.Sym.SymInt.norm
                    (GoLean.GoCore.IntKind.int)
                    (GoLean.Sym.SymInt.add
                      (GoLean.Sym.SymInt.lit 1)
                      (GoLean.Sym.SymInt.norm
                        (GoLean.GoCore.IntKind.int)
                        (GoLean.Sym.SymInt.norm
                          (GoLean.GoCore.IntKind.int)
                          (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))))))))))))))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6629 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6630 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6631 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6632 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.Ready" })) (GoLean.Sym.Value.struct ({ key := "raft.Ready" }) #[(("SoftState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6640 }))),
  (("HardState"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 }))),
  (("ReadStates"), (GoLean.Sym.Value.slice ({ base := none, offset := 0, len := 0, cap := 0 }))),
  (("Entries"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 4 }))),
  (("Snapshot"), (GoLean.Sym.Value.nil)),
  (("CommittedEntries"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6424 }), offset := 0, len := 1, cap := 1 }))),
  (("Messages"), (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6717 }), offset := 0, len := 1, cap := 4 }))),
  (("MustSync"), (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))]))),
  ((GoLean.Loc.base { id := 6633 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6634 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6635 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6636 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6637 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6633 })))),
  ((GoLean.Loc.base { id := 6638 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3344 })))),
  ((GoLean.Loc.base { id := 6639 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6640 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })) (GoLean.Sym.Value.struct ({ key := "raft.SoftState" }) #[(("Lead"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))) (GoLean.GoCore.IntKind.uint64))),
  (("RaftState"), (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm
      (GoLean.GoCore.IntKind.uint64)
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))))) (GoLean.GoCore.IntKind.uint64)))]))),
  ((GoLean.Loc.base { id := 6641 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6642 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6643 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6644 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6645 })))),
  ((GoLean.Loc.base { id := 6645 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6646 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6645 })))),
  ((GoLean.Loc.base { id := 6647 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6648 })))),
  ((GoLean.Loc.base { id := 6648 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6649 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6648 })))),
  ((GoLean.Loc.base { id := 6650 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6651 })))),
  ((GoLean.Loc.base { id := 6651 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6652 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6651 })))),
  ((GoLean.Loc.base { id := 6653 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6654 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6645 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6648 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6651 })))]))),
  ((GoLean.Loc.base { id := 6655 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.eqI
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))))),
  ((GoLean.Loc.base { id := 6656 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6657 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6658 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.eqI
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))))),
  ((GoLean.Loc.base { id := 6659 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6660 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6661 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6662 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6663 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6664 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6665 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.eqI
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)))
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))))))),
  ((GoLean.Loc.base { id := 6666 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6667 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6668 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6669 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6670 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6671 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 0)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6672 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.eqI
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)))
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.uint64)
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))))))),
  ((GoLean.Loc.base { id := 6673 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6674 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6654 })))),
  ((GoLean.Loc.base { id := 6675 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 2)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6676 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6677 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6678 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6679 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit true))))),
  ((GoLean.Loc.base { id := 6680 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1949 })))),
  ((GoLean.Loc.base { id := 6681 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not (GoLean.Sym.SymBool.lit true))))),
  ((GoLean.Loc.base { id := 6682 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" }))) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6683 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" }))) (GoLean.Sym.Value.addr (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable")))),
  ((GoLean.Loc.base { id := 6684 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" }))) (GoLean.Sym.Value.nil))),
  ((GoLean.Loc.base { id := 6685 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6698 })))),
  ((GoLean.Loc.base { id := 6686 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 1989 })))),
  ((GoLean.Loc.base { id := 6687 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6698 })))),
  ((GoLean.Loc.base { id := 6688 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6689 })))),
  ((GoLean.Loc.base { id := 6689 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6690 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6689 })))),
  ((GoLean.Loc.base { id := 6691 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6692 })))),
  ((GoLean.Loc.base { id := 6692 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 0) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6693 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6692 })))),
  ((GoLean.Loc.base { id := 6694 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6695 })))),
  ((GoLean.Loc.base { id := 6695 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.lit 2) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6696 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6695 })))),
  ((GoLean.Loc.base { id := 6697 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6698 })))),
  ((GoLean.Loc.base { id := 6698 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })) (GoLean.Sym.Value.struct ({ key := "raftpb.HardState" }) #[(("Term"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6689 }))),
  (("Vote"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6692 }))),
  (("Commit"), (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6695 })))]))),
  ((GoLean.Loc.base { id := 6699 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))),
  ((GoLean.Loc.base { id := 6700 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6698 })))),
  ((GoLean.Loc.base { id := 6701 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 3360 })))),
  ((GoLean.Loc.base { id := 6702 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6703 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))),
  ((GoLean.Loc.base { id := 6704 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))),
  ((GoLean.Loc.base { id := 6705 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.not
  (GoLean.Sym.SymBool.eqI
    (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1))
    (GoLean.Sym.SymInt.lit 0)))))),
  ((GoLean.Loc.base { id := 6706 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6499 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6707 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6708 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.int)
  (GoLean.Sym.SymInt.norm
    (GoLean.GoCore.IntKind.int)
    (GoLean.Sym.SymInt.add
      (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.int) (GoLean.Sym.SymInt.lit 0))
      (GoLean.Sym.SymInt.lit 1)))) (GoLean.GoCore.IntKind.int)))),
  ((GoLean.Loc.base { id := 6709 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.bool)) (GoLean.Sym.Value.bool (GoLean.Sym.SymBool.lit false)))),
  ((GoLean.Loc.base { id := 6710 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 })))),
  ((GoLean.Loc.base { id := 6711 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm
  (GoLean.GoCore.IntKind.uint64)
  (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1))) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6712 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))) (GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 })))),
  ((GoLean.Loc.base { id := 6713 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) (GoLean.Sym.Value.int (GoLean.Sym.SymInt.norm (GoLean.GoCore.IntKind.uint64) (GoLean.Sym.SymInt.lit 1)) (GoLean.GoCore.IntKind.uint64)))),
  ((GoLean.Loc.base { id := 6714 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6715 }), offset := 0, len := 1, cap := 1 })))),
  ((GoLean.Loc.base { id := 6715 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 }))]))),
  ((GoLean.Loc.base { id := 6716 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.slice ({ base := some (GoLean.Loc.base { id := 6717 }), offset := 0, len := 1, cap := 4 })))),
  ((GoLean.Loc.base { id := 6717 }), (GoLean.Sym.HeapCell.mk (some (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })))) (GoLean.Sym.Value.array #[(GoLean.Sym.Value.addr (GoLean.Loc.base { id := 6456 })),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil),
  (GoLean.Sym.Value.nil)])))]
  6718)

def maC1 : SymConfig :=
  (GoLean.Sym.Config.exec (GoLean.GoCore.Stmt.call
  #[]
  { key := "raft.RawNode.acceptReady" }
  #[GoLean.GoCore.Expr.var "rn", GoLean.GoCore.Expr.var "rd"]) ([[("rd", GoLean.Loc.base { id := 6522 })],
 [("$res0", GoLean.Loc.base { id := 6521 }), ("rn", GoLean.Loc.base { id := 6520 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rd"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("rd", GoLean.Loc.base { id := 6522 })],
 [("$res0", GoLean.Loc.base { id := 6521 }), ("rn", GoLean.Loc.base { id := 6520 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "rd"])]) ([[("rd", GoLean.Loc.base { id := 6519 })],
 [("$c2284", GoLean.Loc.base { id := 6508 })],
 [("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) ([GoLean.Loc.base { id := 6521 }]) [] (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2285", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2285"]
       { key := "raft.IsEmptyHardState" }
       #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "$c2285"))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$c2286", typ := GoLean.GoCore.Ty.interface { key := "error" } },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2286"]
             { key := "raft.MemoryStorage.SetHardState" }
             #[GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "nd")
                   (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                 { key := "main.twinNode" }
                 "st",
               GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.neqCmp
           (GoLean.GoCore.Ty.interface { key := "error" })
           (GoLean.GoCore.Expr.var "$c2286")
           (GoLean.GoCore.Expr.nil none))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.addr
                     (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                   (GoLean.GoCore.Expr.boolLit true)],
             GoLean.GoCore.Stmt.call
               #[]
               { key := "main.twin.viol" }
               #[GoLean.GoCore.Expr.var "t",
                 GoLean.GoCore.Expr.stringLit
                   { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 83, 101, 116, 72, 97, 114, 100, 83, 116, 97,
                                116, 101, 32, 102, 97, 105, 108, 101, 100] }],
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
                 GoLean.GoCore.Stmt.returnStmt]])
         (GoLean.GoCore.Stmt.seqn #[]),
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$c2287", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2287"]
             { key := "raftpb.HardState.GetTerm" }
             #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.addr
               (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "term"))
             (GoLean.GoCore.Expr.var "$c2287")],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization
             { id := "$c2288", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2288"]
             { key := "raftpb.HardState.GetCommit" }
             #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.addr
               (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "commit"))
             (GoLean.GoCore.Expr.var "$c2288")]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.greaterCmp
     (GoLean.GoCore.Expr.length
       (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Entries")
       (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))))
     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.initialization { id := "$c2289", typ := GoLean.GoCore.Ty.interface { key := "error" } },
           GoLean.GoCore.Stmt.call
             #[GoLean.GoCore.Assignee.var "$c2289"]
             { key := "raft.MemoryStorage.Append" }
             #[GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "nd")
                   (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                 { key := "main.twinNode" }
                 "st",
               GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Entries"]],
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.neqCmp
           (GoLean.GoCore.Ty.interface { key := "error" })
           (GoLean.GoCore.Expr.var "$c2289")
           (GoLean.GoCore.Expr.nil none))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.addr
                     (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                   (GoLean.GoCore.Expr.boolLit true)],
             GoLean.GoCore.Stmt.call
               #[]
               { key := "main.twin.viol" }
               #[GoLean.GoCore.Expr.var "t",
                 GoLean.GoCore.Expr.stringLit
                   { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 65, 112, 112, 101, 110, 100, 32, 102, 97, 105,
                                108, 101, 100] }],
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
                 GoLean.GoCore.Stmt.returnStmt]])
         (GoLean.GoCore.Stmt.seqn #[])])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.initialization { id := "$c2290", typ := GoLean.GoCore.Ty.bool },
     GoLean.GoCore.Stmt.call
       #[GoLean.GoCore.Assignee.var "$c2290"]
       { key := "raft.IsEmptySnap" }
       #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Snapshot"]],
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "$c2290"))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.addr
               (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
             (GoLean.GoCore.Expr.boolLit true)],
       GoLean.GoCore.Stmt.call
         #[]
         { key := "main.twin.viol" }
         #[GoLean.GoCore.Expr.var "t",
           GoLean.GoCore.Expr.stringLit
             { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32,
                          115, 110, 97, 112, 115, 104, 111, 116] }],
       GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
           GoLean.GoCore.Stmt.returnStmt]])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.ifThenElse
   (GoLean.GoCore.Expr.neqCmp
     (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
     (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
     (GoLean.GoCore.Expr.nil none))
   (GoLean.GoCore.Stmt.block
     #[]
     #[GoLean.GoCore.Stmt.seqn
         #[GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.addr
               (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "state"))
             (GoLean.GoCore.Expr.fieldGet
               (GoLean.GoCore.Expr.deref
                 (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
                 (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
               { key := "raft.SoftState" }
               "RaftState")],
       GoLean.GoCore.Stmt.ifThenElse
         (GoLean.GoCore.Expr.eqCmp
           (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
           (GoLean.GoCore.Expr.fieldGet
             (GoLean.GoCore.Expr.deref
               (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
               (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
             { key := "raft.SoftState" }
             "RaftState")
           (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64)))
         (GoLean.GoCore.Stmt.block
           #[]
           #[GoLean.GoCore.Stmt.assign
               (GoLean.GoCore.Assignee.addr
                 (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "claims"))
               (GoLean.GoCore.Expr.add
                 (GoLean.GoCore.Expr.fieldGet
                   (GoLean.GoCore.Expr.deref
                     (GoLean.GoCore.Expr.var "t")
                     (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                   { key := "main.twin" }
                   "claims")
                 (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.initialization
                   { id := "prev", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                 GoLean.GoCore.Stmt.initialization { id := "ok", typ := GoLean.GoCore.Ty.bool },
                 GoLean.GoCore.Stmt.mapLookup
                   (GoLean.GoCore.Assignee.var "prev")
                   (GoLean.GoCore.Assignee.var "ok")
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "t")
                       (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                     { key := "main.twin" }
                     "leaderOf")
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "nd")
                       (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                     { key := "main.twinNode" }
                     "term")
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))],
             GoLean.GoCore.Stmt.ifThenElse
               (GoLean.GoCore.Expr.and
                 (GoLean.GoCore.Expr.var "ok")
                 (GoLean.GoCore.Expr.neqCmp
                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                   (GoLean.GoCore.Expr.var "prev")
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "nd")
                       (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                     { key := "main.twinNode" }
                     "id")))
               (GoLean.GoCore.Stmt.block
                 #[]
                 #[GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.initialization { id := "$c2291", typ := GoLean.GoCore.Ty.string },
                       GoLean.GoCore.Stmt.call
                         #[GoLean.GoCore.Assignee.var "$c2291"]
                         { key := "utoa" }
                         #[GoLean.GoCore.Expr.fieldGet
                             (GoLean.GoCore.Expr.deref
                               (GoLean.GoCore.Expr.var "nd")
                               (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                             { key := "main.twinNode" }
                             "term"]],
                   GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.initialization { id := "$c2292", typ := GoLean.GoCore.Ty.string },
                       GoLean.GoCore.Stmt.call
                         #[GoLean.GoCore.Assignee.var "$c2292"]
                         { key := "utoa" }
                         #[GoLean.GoCore.Expr.var "prev"]],
                   GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.initialization { id := "$c2293", typ := GoLean.GoCore.Ty.string },
                       GoLean.GoCore.Stmt.call
                         #[GoLean.GoCore.Assignee.var "$c2293"]
                         { key := "utoa" }
                         #[GoLean.GoCore.Expr.fieldGet
                             (GoLean.GoCore.Expr.deref
                               (GoLean.GoCore.Expr.var "nd")
                               (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                             { key := "main.twinNode" }
                             "id"]],
                   GoLean.GoCore.Stmt.call
                     #[]
                     { key := "main.twin.viol" }
                     #[GoLean.GoCore.Expr.var "t",
                       GoLean.GoCore.Expr.add
                         (GoLean.GoCore.Expr.add
                           (GoLean.GoCore.Expr.add
                             (GoLean.GoCore.Expr.add
                               (GoLean.GoCore.Expr.add
                                 (GoLean.GoCore.Expr.stringLit
                                   { bytes := #[83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97, 102,
                                                101, 116, 121, 58, 32, 116, 101, 114, 109, 32] })
                                 (GoLean.GoCore.Expr.var "$c2291"))
                               (GoLean.GoCore.Expr.stringLit
                                 { bytes := #[32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116, 104,
                                              32, 110, 111, 100, 101, 32] }))
                             (GoLean.GoCore.Expr.var "$c2292"))
                           (GoLean.GoCore.Expr.stringLit { bytes := #[32, 97, 110, 100, 32, 110, 111, 100, 101, 32] }))
                         (GoLean.GoCore.Expr.var "$c2293")]])
               (GoLean.GoCore.Stmt.seqn #[]),
             GoLean.GoCore.Stmt.mapAssign
               (GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "t")
                   (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                 { key := "main.twin" }
                 "leaderOf")
               (GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "nd")
                   (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                 { key := "main.twinNode" }
                 "term")
               (GoLean.GoCore.Expr.fieldGet
                 (GoLean.GoCore.Expr.deref
                   (GoLean.GoCore.Expr.var "nd")
                   (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                 { key := "main.twinNode" }
                 "id")
               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))])
         (GoLean.GoCore.Stmt.seqn #[])])
   (GoLean.GoCore.Stmt.seqn #[]),
 GoLean.GoCore.Stmt.block
   #[]
   #[GoLean.GoCore.Stmt.initialization
       { id := "$rcoll",
         typ := GoLean.GoCore.Ty.slice
                  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$rcoll")
       (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Messages"),
     GoLean.GoCore.Stmt.initialization { id := "$rlen", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$rlen")
       (GoLean.GoCore.Expr.length (GoLean.GoCore.Expr.var "$rcoll") none),
     GoLean.GoCore.Stmt.initialization { id := "$ridx", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
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
             (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$rfirst") (GoLean.GoCore.Expr.boolLit false))
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
             { id := "m", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
           GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "m")
             (GoLean.GoCore.Expr.indexGet (GoLean.GoCore.Expr.var "$rcoll") (GoLean.GoCore.Expr.var "$ridx")),
           GoLean.GoCore.Stmt.block
             #[]
             #[GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.initialization
                     { id := "$c2294",
                       typ := GoLean.GoCore.Ty.slice
                                (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                   GoLean.GoCore.Stmt.makeSlice
                     (GoLean.GoCore.Assignee.var "$c2294")
                     (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                     (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                   GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.addr
                       (GoLean.GoCore.Expr.indexAddr
                         (GoLean.GoCore.Expr.var "$c2294")
                         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                     (GoLean.GoCore.Expr.var "m")],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.initialization
                     { id := "$c2295",
                       typ := GoLean.GoCore.Ty.slice
                                (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                   GoLean.GoCore.Stmt.appendSlice
                     (GoLean.GoCore.Assignee.var "$c2295")
                     (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                     (GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "t")
                         (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                       { key := "main.twin" }
                       "net")
                     (GoLean.GoCore.Expr.var "$c2294")],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.addr
                       (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "net"))
                     (GoLean.GoCore.Expr.var "$c2295")],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.initialization
                     { id := "$c2296", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                   GoLean.GoCore.Stmt.makeSlice
                     (GoLean.GoCore.Assignee.var "$c2296")
                     (GoLean.GoCore.Ty.bool)
                     (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                     (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                   GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.addr
                       (GoLean.GoCore.Expr.indexAddr
                         (GoLean.GoCore.Expr.var "$c2296")
                         (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                     (GoLean.GoCore.Expr.boolLit true)],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.initialization
                     { id := "$c2297", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                   GoLean.GoCore.Stmt.appendSlice
                     (GoLean.GoCore.Assignee.var "$c2297")
                     (GoLean.GoCore.Ty.bool)
                     (GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "t")
                         (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                       { key := "main.twin" }
                       "live")
                     (GoLean.GoCore.Expr.var "$c2296")],
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.addr
                       (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "live"))
                     (GoLean.GoCore.Expr.var "$c2297")]]])],
 GoLean.GoCore.Stmt.block
   #[]
   #[GoLean.GoCore.Stmt.initialization
       { id := "$rcoll",
         typ := GoLean.GoCore.Ty.slice
                  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$rcoll")
       (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "CommittedEntries"),
     GoLean.GoCore.Stmt.initialization { id := "$rlen", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
     GoLean.GoCore.Stmt.assign
       (GoLean.GoCore.Assignee.var "$rlen")
       (GoLean.GoCore.Expr.length (GoLean.GoCore.Expr.var "$rcoll") none),
     GoLean.GoCore.Stmt.initialization { id := "$ridx", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
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
             (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$rfirst") (GoLean.GoCore.Expr.boolLit false))
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
             { id := "e", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }) },
           GoLean.GoCore.Stmt.assign
             (GoLean.GoCore.Assignee.var "e")
             (GoLean.GoCore.Expr.indexGet (GoLean.GoCore.Expr.var "$rcoll") (GoLean.GoCore.Expr.var "$ridx")),
           GoLean.GoCore.Stmt.block
             #[]
             #[GoLean.GoCore.Stmt.call
                 #[]
                 { key := "main.twin.apply" }
                 #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "nd", GoLean.GoCore.Expr.var "e"]]])],
 GoLean.GoCore.Stmt.call
   #[]
   { key := "raft.RawNode.Advance" }
   #[GoLean.GoCore.Expr.fieldGet
       (GoLean.GoCore.Expr.deref (GoLean.GoCore.Expr.var "nd") (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
       { key := "main.twinNode" }
       "rn",
     GoLean.GoCore.Expr.var "rd"]]) ([[("rd", GoLean.Loc.base { id := 6519 })],
 [("$c2284", GoLean.Loc.base { id := 6508 })],
 [("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$c2284", GoLean.Loc.base { id := 6508 })],
 [("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.loop (GoLean.GoCore.Expr.boolLit true) (GoLean.GoCore.Stmt.block
  #[]
  #[GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "$forFirst")
      (GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$forFirst") (GoLean.GoCore.Expr.boolLit false))
      (GoLean.GoCore.Stmt.seqn #[]),
    GoLean.GoCore.Stmt.seqn
      #[GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "$c2284", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c2284"]
              { key := "raft.RawNode.HasReady" }
              #[GoLean.GoCore.Expr.fieldGet
                  (GoLean.GoCore.Expr.deref
                    (GoLean.GoCore.Expr.var "nd")
                    (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                  { key := "main.twinNode" }
                  "rn"]]],
    GoLean.GoCore.Stmt.ifThenElse
      (GoLean.GoCore.Expr.var "$c2284")
      (GoLean.GoCore.Stmt.seqn #[])
      (GoLean.GoCore.Stmt.breakStmt),
    GoLean.GoCore.Stmt.block
      #[]
      #[GoLean.GoCore.Stmt.assign
          (GoLean.GoCore.Assignee.var "rounds")
          (GoLean.GoCore.Expr.add
            (GoLean.GoCore.Expr.var "rounds")
            (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.var "rounds")
            (GoLean.GoCore.Expr.intLit 64 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                    (GoLean.GoCore.Expr.boolLit true)],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.viol" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.stringLit
                    { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 104, 97, 114, 118, 101, 115, 116, 32, 100,
                                 105, 100, 32, 110, 111, 116, 32, 113, 117, 105, 101, 115, 99, 101, 32, 105, 110, 32,
                                 54, 52, 32, 114, 111, 117, 110, 100, 115] }],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
                  GoLean.GoCore.Stmt.returnStmt]])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "rd", typ := GoLean.GoCore.Ty.defined { key := "raft.Ready" } },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "rd"]
              { key := "raft.RawNode.Ready" }
              #[GoLean.GoCore.Expr.fieldGet
                  (GoLean.GoCore.Expr.deref
                    (GoLean.GoCore.Expr.var "nd")
                    (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                  { key := "main.twinNode" }
                  "rn"]],
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "$c2285", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c2285"]
              { key := "raft.IsEmptyHardState" }
              #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "$c2285"))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2286", typ := GoLean.GoCore.Ty.interface { key := "error" } },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2286"]
                    { key := "raft.MemoryStorage.SetHardState" }
                    #[GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "nd")
                          (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                        { key := "main.twinNode" }
                        "st",
                      GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.neqCmp
                  (GoLean.GoCore.Ty.interface { key := "error" })
                  (GoLean.GoCore.Expr.var "$c2286")
                  (GoLean.GoCore.Expr.nil none))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.addr
                            (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                          (GoLean.GoCore.Expr.boolLit true)],
                    GoLean.GoCore.Stmt.call
                      #[]
                      { key := "main.twin.viol" }
                      #[GoLean.GoCore.Expr.var "t",
                        GoLean.GoCore.Expr.stringLit
                          { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 83, 101, 116, 72, 97, 114, 100, 83,
                                       116, 97, 116, 101, 32, 102, 97, 105, 108, 101, 100] }],
                    GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$res0")
                          (GoLean.GoCore.Expr.var "rounds"),
                        GoLean.GoCore.Stmt.returnStmt]])
                (GoLean.GoCore.Stmt.seqn #[]),
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2287", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2287"]
                    { key := "raftpb.HardState.GetTerm" }
                    #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "term"))
                    (GoLean.GoCore.Expr.var "$c2287")],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2288", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2288"]
                    { key := "raftpb.HardState.GetCommit" }
                    #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "HardState"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "commit"))
                    (GoLean.GoCore.Expr.var "$c2288")]])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.greaterCmp
            (GoLean.GoCore.Expr.length
              (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Entries")
              (some (GoLean.GoCore.Ty.slice
                 (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })))))
            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2289", typ := GoLean.GoCore.Ty.interface { key := "error" } },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2289"]
                    { key := "raft.MemoryStorage.Append" }
                    #[GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "nd")
                          (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                        { key := "main.twinNode" }
                        "st",
                      GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Entries"]],
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.neqCmp
                  (GoLean.GoCore.Ty.interface { key := "error" })
                  (GoLean.GoCore.Expr.var "$c2289")
                  (GoLean.GoCore.Expr.nil none))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.addr
                            (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                          (GoLean.GoCore.Expr.boolLit true)],
                    GoLean.GoCore.Stmt.call
                      #[]
                      { key := "main.twin.viol" }
                      #[GoLean.GoCore.Expr.var "t",
                        GoLean.GoCore.Expr.stringLit
                          { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 65, 112, 112, 101, 110, 100, 32, 102,
                                       97, 105, 108, 101, 100] }],
                    GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$res0")
                          (GoLean.GoCore.Expr.var "rounds"),
                        GoLean.GoCore.Stmt.returnStmt]])
                (GoLean.GoCore.Stmt.seqn #[])])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.seqn
          #[GoLean.GoCore.Stmt.initialization { id := "$c2290", typ := GoLean.GoCore.Ty.bool },
            GoLean.GoCore.Stmt.call
              #[GoLean.GoCore.Assignee.var "$c2290"]
              { key := "raft.IsEmptySnap" }
              #[GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Snapshot"]],
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.not (GoLean.GoCore.Expr.var "$c2290"))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "halt"))
                    (GoLean.GoCore.Expr.boolLit true)],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.viol" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.stringLit
                    { bytes := #[104, 97, 114, 110, 101, 115, 115, 58, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101,
                                 100, 32, 115, 110, 97, 112, 115, 104, 111, 116] }],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
                  GoLean.GoCore.Stmt.returnStmt]])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.ifThenElse
          (GoLean.GoCore.Expr.neqCmp
            (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
            (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
            (GoLean.GoCore.Expr.nil none))
          (GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "nd") { key := "main.twinNode" } "state"))
                    (GoLean.GoCore.Expr.fieldGet
                      (GoLean.GoCore.Expr.deref
                        (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
                        (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
                      { key := "raft.SoftState" }
                      "RaftState")],
              GoLean.GoCore.Stmt.ifThenElse
                (GoLean.GoCore.Expr.eqCmp
                  (GoLean.GoCore.Ty.defined { key := "raft.StateType" })
                  (GoLean.GoCore.Expr.fieldGet
                    (GoLean.GoCore.Expr.deref
                      (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "SoftState")
                      (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }))
                    { key := "raft.SoftState" }
                    "RaftState")
                  (GoLean.GoCore.Expr.intLit 2 (GoLean.GoCore.IntKind.uint64)))
                (GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.addr
                        (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "claims"))
                      (GoLean.GoCore.Expr.add
                        (GoLean.GoCore.Expr.fieldGet
                          (GoLean.GoCore.Expr.deref
                            (GoLean.GoCore.Expr.var "t")
                            (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                          { key := "main.twin" }
                          "claims")
                        (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                    GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "prev", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                        GoLean.GoCore.Stmt.initialization { id := "ok", typ := GoLean.GoCore.Ty.bool },
                        GoLean.GoCore.Stmt.mapLookup
                          (GoLean.GoCore.Assignee.var "prev")
                          (GoLean.GoCore.Assignee.var "ok")
                          (GoLean.GoCore.Expr.fieldGet
                            (GoLean.GoCore.Expr.deref
                              (GoLean.GoCore.Expr.var "t")
                              (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                            { key := "main.twin" }
                            "leaderOf")
                          (GoLean.GoCore.Expr.fieldGet
                            (GoLean.GoCore.Expr.deref
                              (GoLean.GoCore.Expr.var "nd")
                              (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                            { key := "main.twinNode" }
                            "term")
                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))],
                    GoLean.GoCore.Stmt.ifThenElse
                      (GoLean.GoCore.Expr.and
                        (GoLean.GoCore.Expr.var "ok")
                        (GoLean.GoCore.Expr.neqCmp
                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                          (GoLean.GoCore.Expr.var "prev")
                          (GoLean.GoCore.Expr.fieldGet
                            (GoLean.GoCore.Expr.deref
                              (GoLean.GoCore.Expr.var "nd")
                              (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                            { key := "main.twinNode" }
                            "id")))
                      (GoLean.GoCore.Stmt.block
                        #[]
                        #[GoLean.GoCore.Stmt.seqn
                            #[GoLean.GoCore.Stmt.initialization { id := "$c2291", typ := GoLean.GoCore.Ty.string },
                              GoLean.GoCore.Stmt.call
                                #[GoLean.GoCore.Assignee.var "$c2291"]
                                { key := "utoa" }
                                #[GoLean.GoCore.Expr.fieldGet
                                    (GoLean.GoCore.Expr.deref
                                      (GoLean.GoCore.Expr.var "nd")
                                      (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                                    { key := "main.twinNode" }
                                    "term"]],
                          GoLean.GoCore.Stmt.seqn
                            #[GoLean.GoCore.Stmt.initialization { id := "$c2292", typ := GoLean.GoCore.Ty.string },
                              GoLean.GoCore.Stmt.call
                                #[GoLean.GoCore.Assignee.var "$c2292"]
                                { key := "utoa" }
                                #[GoLean.GoCore.Expr.var "prev"]],
                          GoLean.GoCore.Stmt.seqn
                            #[GoLean.GoCore.Stmt.initialization { id := "$c2293", typ := GoLean.GoCore.Ty.string },
                              GoLean.GoCore.Stmt.call
                                #[GoLean.GoCore.Assignee.var "$c2293"]
                                { key := "utoa" }
                                #[GoLean.GoCore.Expr.fieldGet
                                    (GoLean.GoCore.Expr.deref
                                      (GoLean.GoCore.Expr.var "nd")
                                      (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                                    { key := "main.twinNode" }
                                    "id"]],
                          GoLean.GoCore.Stmt.call
                            #[]
                            { key := "main.twin.viol" }
                            #[GoLean.GoCore.Expr.var "t",
                              GoLean.GoCore.Expr.add
                                (GoLean.GoCore.Expr.add
                                  (GoLean.GoCore.Expr.add
                                    (GoLean.GoCore.Expr.add
                                      (GoLean.GoCore.Expr.add
                                        (GoLean.GoCore.Expr.stringLit
                                          { bytes := #[83, 49, 32, 101, 108, 101, 99, 116, 105, 111, 110, 32, 115, 97,
                                                       102, 101, 116, 121, 58, 32, 116, 101, 114, 109, 32] })
                                        (GoLean.GoCore.Expr.var "$c2291"))
                                      (GoLean.GoCore.Expr.stringLit
                                        { bytes := #[32, 99, 108, 97, 105, 109, 101, 100, 32, 98, 121, 32, 98, 111, 116,
                                                     104, 32, 110, 111, 100, 101, 32] }))
                                    (GoLean.GoCore.Expr.var "$c2292"))
                                  (GoLean.GoCore.Expr.stringLit
                                    { bytes := #[32, 97, 110, 100, 32, 110, 111, 100, 101, 32] }))
                                (GoLean.GoCore.Expr.var "$c2293")]])
                      (GoLean.GoCore.Stmt.seqn #[]),
                    GoLean.GoCore.Stmt.mapAssign
                      (GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "t")
                          (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                        { key := "main.twin" }
                        "leaderOf")
                      (GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "nd")
                          (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                        { key := "main.twinNode" }
                        "term")
                      (GoLean.GoCore.Expr.fieldGet
                        (GoLean.GoCore.Expr.deref
                          (GoLean.GoCore.Expr.var "nd")
                          (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
                        { key := "main.twinNode" }
                        "id")
                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))])
                (GoLean.GoCore.Stmt.seqn #[])])
          (GoLean.GoCore.Stmt.seqn #[]),
        GoLean.GoCore.Stmt.block
          #[]
          #[GoLean.GoCore.Stmt.initialization
              { id := "$rcoll",
                typ := GoLean.GoCore.Ty.slice
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rcoll")
              (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "Messages"),
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
                    { id := "m",
                      typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "m")
                    (GoLean.GoCore.Expr.indexGet (GoLean.GoCore.Expr.var "$rcoll") (GoLean.GoCore.Expr.var "$ridx")),
                  GoLean.GoCore.Stmt.block
                    #[]
                    #[GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.initialization
                            { id := "$c2294",
                              typ := GoLean.GoCore.Ty.slice
                                       (GoLean.GoCore.Ty.pointer
                                         (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                          GoLean.GoCore.Stmt.makeSlice
                            (GoLean.GoCore.Assignee.var "$c2294")
                            (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                            (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                            (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                          GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.addr
                              (GoLean.GoCore.Expr.indexAddr
                                (GoLean.GoCore.Expr.var "$c2294")
                                (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                            (GoLean.GoCore.Expr.var "m")],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.initialization
                            { id := "$c2295",
                              typ := GoLean.GoCore.Ty.slice
                                       (GoLean.GoCore.Ty.pointer
                                         (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
                          GoLean.GoCore.Stmt.appendSlice
                            (GoLean.GoCore.Assignee.var "$c2295")
                            (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))
                            (GoLean.GoCore.Expr.fieldGet
                              (GoLean.GoCore.Expr.deref
                                (GoLean.GoCore.Expr.var "t")
                                (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                              { key := "main.twin" }
                              "net")
                            (GoLean.GoCore.Expr.var "$c2294")],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.addr
                              (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "net"))
                            (GoLean.GoCore.Expr.var "$c2295")],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.initialization
                            { id := "$c2296", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                          GoLean.GoCore.Stmt.makeSlice
                            (GoLean.GoCore.Assignee.var "$c2296")
                            (GoLean.GoCore.Ty.bool)
                            (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))
                            (some (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))),
                          GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.addr
                              (GoLean.GoCore.Expr.indexAddr
                                (GoLean.GoCore.Expr.var "$c2296")
                                (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                            (GoLean.GoCore.Expr.boolLit true)],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.initialization
                            { id := "$c2297", typ := GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool) },
                          GoLean.GoCore.Stmt.appendSlice
                            (GoLean.GoCore.Assignee.var "$c2297")
                            (GoLean.GoCore.Ty.bool)
                            (GoLean.GoCore.Expr.fieldGet
                              (GoLean.GoCore.Expr.deref
                                (GoLean.GoCore.Expr.var "t")
                                (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                              { key := "main.twin" }
                              "live")
                            (GoLean.GoCore.Expr.var "$c2296")],
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.addr
                              (GoLean.GoCore.Expr.fieldAddr (GoLean.GoCore.Expr.var "t") { key := "main.twin" } "live"))
                            (GoLean.GoCore.Expr.var "$c2297")]]])],
        GoLean.GoCore.Stmt.block
          #[]
          #[GoLean.GoCore.Stmt.initialization
              { id := "$rcoll",
                typ := GoLean.GoCore.Ty.slice
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })) },
            GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$rcoll")
              (GoLean.GoCore.Expr.fieldGet (GoLean.GoCore.Expr.var "rd") { key := "raft.Ready" } "CommittedEntries"),
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
                    { id := "e", typ := GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }) },
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "e")
                    (GoLean.GoCore.Expr.indexGet (GoLean.GoCore.Expr.var "$rcoll") (GoLean.GoCore.Expr.var "$ridx")),
                  GoLean.GoCore.Stmt.block
                    #[]
                    #[GoLean.GoCore.Stmt.call
                        #[]
                        { key := "main.twin.apply" }
                        #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "nd", GoLean.GoCore.Expr.var "e"]]])],
        GoLean.GoCore.Stmt.call
          #[]
          { key := "raft.RawNode.Advance" }
          #[GoLean.GoCore.Expr.fieldGet
              (GoLean.GoCore.Expr.deref
                (GoLean.GoCore.Expr.var "nd")
                (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))
              { key := "main.twinNode" }
              "rn",
            GoLean.GoCore.Expr.var "rd"]]]) ([[("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.seq ([]) ([[("$forFirst", GoLean.Loc.base { id := 6507 })],
 [("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.seq ([GoLean.GoCore.Stmt.seqn
   #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "rounds"),
     GoLean.GoCore.Stmt.returnStmt]]) ([[("rounds", GoLean.Loc.base { id := 6506 })],
 [("$res0", GoLean.Loc.base { id := 6505 }),
  ("nd", GoLean.Loc.base { id := 6504 }),
  ("t", GoLean.Loc.base { id := 6503 })]]) (GoLean.Sym.Cont.frame ([(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$cr0"])]) ([[("$cr0", GoLean.Loc.base { id := 6502 }),
  ("to", GoLean.Loc.base { id := 6138 }),
  ("$c2316", GoLean.Loc.base { id := 6135 }),
  ("m", GoLean.Loc.base { id := 6134 })],
 [("i", GoLean.Loc.base { id := 6133 }), ("t", GoLean.Loc.base { id := 6132 })]]) ([GoLean.Loc.base { id := 6505 }]) [] (GoLean.Sym.Cont.seq ([]) ([[("$cr0", GoLean.Loc.base { id := 6502 }),
  ("to", GoLean.Loc.base { id := 6138 }),
  ("$c2316", GoLean.Loc.base { id := 6135 }),
  ("m", GoLean.Loc.base { id := 6134 })],
 [("i", GoLean.Loc.base { id := 6133 }), ("t", GoLean.Loc.base { id := 6132 })]]) (GoLean.Sym.Cont.frame ([]) ([[("$c2241", GoLean.Loc.base { id := 6125 }),
  ("$c2240", GoLean.Loc.base { id := 6122 }),
  ("$c2239", GoLean.Loc.base { id := 6114 }),
  ("$c2238", GoLean.Loc.base { id := 6111 }),
  ("$c2237", GoLean.Loc.base { id := 6105 }),
  ("$c2236", GoLean.Loc.base { id := 6097 }),
  ("m", GoLean.Loc.base { id := 6096 }),
  ("picked", GoLean.Loc.base { id := 6094 })],
 [("live", GoLean.Loc.base { id := 6088 }), ("$c2235", GoLean.Loc.base { id := 6086 })],
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
 GoLean.GoCore.Stmt.continueStmt]) ([[("$c2241", GoLean.Loc.base { id := 6125 }),
  ("$c2240", GoLean.Loc.base { id := 6122 }),
  ("$c2239", GoLean.Loc.base { id := 6114 }),
  ("$c2238", GoLean.Loc.base { id := 6111 }),
  ("$c2237", GoLean.Loc.base { id := 6105 }),
  ("$c2236", GoLean.Loc.base { id := 6097 }),
  ("m", GoLean.Loc.base { id := 6096 }),
  ("picked", GoLean.Loc.base { id := 6094 })],
 [("live", GoLean.Loc.base { id := 6088 }), ("$c2235", GoLean.Loc.base { id := 6086 })],
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
 GoLean.GoCore.Stmt.breakStmt]) ([[("live", GoLean.Loc.base { id := 6088 }), ("$c2235", GoLean.Loc.base { id := 6086 })],
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
  ("$res0", GoLean.Loc.base { id := 98 })]]) (GoLean.Sym.Cont.frame ([]) ([]) ([]) [] (GoLean.Sym.Cont.stop) false)) false)))))))) false)) false)))))) false)))

end GoLean.RaftSeam.Ring
