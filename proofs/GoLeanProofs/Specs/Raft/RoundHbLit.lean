import GoLeanProofs.Specs.Raft.BecomeFollowerWitness

/-! # RoundHbLit — GENERATED literals (A4-U18 C1; generator
`artifacts/probe/RoundFixDump.lean` — DO NOT EDIT BY HAND).

The deliver-heartbeat ROUND-witness fixture: the twin's real
first loop-head state (runProgramSetupM + 100553 steps, all-zero
stream), net/live DOCTORED to one live MsgHeartbeat (Type 8,
From 1, To 2, Term 0, Commit 0 — the Hh no-advance family),
PRUNED to the round's 26-cell read-before-write set (fail-closed
discovery; writes recreate pruned cells soundly), plus boundary
states at steps 100 and 300 of the 10,964-step round walk and
the final loop-head state. The [0,100) and [100,300) slivers are
kernel-replayed in RoundStatement.lean; the full-round replay is
generator-computed (compiled stepFn) with its kernel form
measured-blocked (the U18 heap-linear kernel wall) — see the
RoundStatement docstrings for exactly what is and is not
kernel-checked. -/

namespace GoLean.RaftSeam

open GoLean.GoCore GoLean.GoCore.Machine

set_option maxRecDepth 4000000

def rhbNa0 : Nat := 6079

def rhbHeap0 : GoLean.GoCore.Heap :=
  [(GoLean.Loc.base { id := 15 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 57 }) }),
 (GoLean.Loc.base { id := 27 },
  { declaredTy := some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.array
               #[GoLean.GoValue.bool true, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool true,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool true,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool true] }),
 (GoLean.Loc.base { id := 28 },
  { declaredTy := some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.array
               #[GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool false, GoLean.GoValue.bool true,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true] }),
 (GoLean.Loc.base { id := 57 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.HardState" }
               #[("Term", GoLean.GoValue.nil), ("Vote", GoLean.GoValue.nil),
                 ("Commit", GoLean.GoValue.nil)] }),
 (GoLean.Loc.base { id := 110 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 121 }) }),
 (GoLean.Loc.base { id := 121 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twin" }),
    value := GoLean.GoValue.struct
               { key := "main.twin" }
               #[("nodes",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 1764 }), offset := 0, len := 3, cap := 4 }),
                 ("net",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6077 }), offset := 0, len := 1, cap := 1 }),
                 ("live",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6078 }), offset := 0, len := 1, cap := 1 }),
                 ("leaderOf", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 115 }) }),
                 ("byIndex", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 118 }) }),
                 ("claims", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("committed", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("violations", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("pending",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 136 }), offset := 0, len := 2, cap := 4 }),
                 ("driven", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("seq", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.int)),
                 ("trace",
                  GoLean.GoValue.string
                    { bytes := #[91, 99, 104, 111, 105, 99, 101, 45, 100, 114, 105, 118, 101, 110, 93, 10, 99,
                                 97, 109, 112, 97, 105, 103, 110, 49] }),
                 ("halt", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 170 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
    value := GoLean.GoValue.struct
               { key := "main.twinNode" }
               #[("id", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("rn", GoLean.GoValue.addr (GoLean.Loc.base { id := 1742 })),
                 ("st", GoLean.GoValue.addr (GoLean.Loc.base { id := 179 })),
                 ("term", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("commit", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("state", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("lastTrm", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("got", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 167 }) })] }),
 (GoLean.Loc.base { id := 1764 },
  { declaredTy := some (GoLean.GoCore.Ty.array
                    4
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))),
    value := GoLean.GoValue.array
               #[GoLean.GoValue.addr (GoLean.Loc.base { id := 170 }),
                 GoLean.GoValue.addr (GoLean.Loc.base { id := 1770 }),
                 GoLean.GoValue.addr (GoLean.Loc.base { id := 3369 }), GoLean.GoValue.nil] }),
 (GoLean.Loc.base { id := 1770 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
    value := GoLean.GoValue.struct
               { key := "main.twinNode" }
               #[("id", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                 ("rn", GoLean.GoValue.addr (GoLean.Loc.base { id := 3342 })),
                 ("st", GoLean.GoValue.addr (GoLean.Loc.base { id := 1779 })),
                 ("term", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("commit", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("state", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("lastTrm", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("got", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 1767 }) })] }),
 (GoLean.Loc.base { id := 1949 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }),
    value := GoLean.GoValue.struct
               { key := "raft.raftLog" }
               #[("storage",
                  GoLean.GoValue.interface
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }))
                    (GoLean.GoValue.addr (GoLean.Loc.base { id := 1779 }))),
                 ("unstable",
                  GoLean.GoValue.struct
                    { key := "raft.unstable" }
                    #[("snapshot", GoLean.GoValue.nil),
                      ("entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                      ("offset", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                      ("snapshotInProgress", GoLean.GoValue.bool false),
                      ("offsetInProgress", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                      ("logger",
                       GoLean.GoValue.interface
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
                         (GoLean.GoValue.addr (GoLean.Loc.base { id := 97 })))]),
                 ("committed", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("applying", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("logger",
                  GoLean.GoValue.interface
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
                    (GoLean.GoValue.addr (GoLean.Loc.base { id := 97 }))),
                 ("maxApplyingEntsSize", GoLean.GoValue.int 1048576 (GoLean.GoCore.IntKind.uint64)),
                 ("applyingEntsSize", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("applyingEntsPaused", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 1989 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.raft" }),
    value := GoLean.GoValue.struct
               { key := "raft.raft" }
               #[("id", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                 ("Term", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("Vote", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("readStates", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("raftLog", GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 })),
                 ("maxMsgSize", GoLean.GoValue.int 1048576 (GoLean.GoCore.IntKind.uint64)),
                 ("maxUncommittedSize",
                  GoLean.GoValue.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
                 ("trk",
                  GoLean.GoValue.struct
                    { key := "tracker.ProgressTracker" }
                    #[("Config",
                       GoLean.GoValue.struct
                         { key := "tracker.Config" }
                         #[("Voters",
                            GoLean.GoValue.array
                              #[GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 2686 }) },
                                GoLean.GoValue.map { base := none }]),
                           ("AutoLeave", GoLean.GoValue.bool false),
                           ("Learners", GoLean.GoValue.map { base := none }),
                           ("LearnersNext", GoLean.GoValue.map { base := none })]),
                      ("Progress", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 2703 }) }),
                      ("Votes", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 3059 }) }),
                      ("MaxInflight", GoLean.GoValue.int 256 (GoLean.GoCore.IntKind.int)),
                      ("MaxInflightBytes",
                       GoLean.GoValue.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64))]),
                 ("state", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("isLearner", GoLean.GoValue.bool false),
                 ("msgs", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("msgsAfterAppend", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("lead", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("leadTransferee", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("pendingConfIndex", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("disableConfChangeValidation", GoLean.GoValue.bool false),
                 ("uncommittedSize", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("readOnly", GoLean.GoValue.addr (GoLean.Loc.base { id := 3199 })),
                 ("electionElapsed", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("heartbeatElapsed", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("checkQuorum", GoLean.GoValue.bool false), ("preVote", GoLean.GoValue.bool false),
                 ("heartbeatTimeout", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int)),
                 ("electionTimeout", GoLean.GoValue.int 10 (GoLean.GoCore.IntKind.int)),
                 ("randomizedElectionTimeout", GoLean.GoValue.int 10 (GoLean.GoCore.IntKind.int)),
                 ("disableProposalForwarding", GoLean.GoValue.bool false),
                 ("stepDownOnRemoval", GoLean.GoValue.bool false),
                 ("tick",
                  GoLean.GoValue.funcVal
                    { key := "raft.raft.tickElection" }
                    [GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 })]),
                 ("step", GoLean.GoValue.funcVal { key := "raft.stepFollower" } []),
                 ("logger",
                  GoLean.GoValue.interface
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
                    (GoLean.GoValue.addr (GoLean.Loc.base { id := 97 }))),
                 ("pendingReadIndexMessages",
                  GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("traceLogger", GoLean.GoValue.nil)] }),
 (GoLean.Loc.base { id := 3342 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }),
    value := GoLean.GoValue.struct
               { key := "raft.RawNode" }
               #[("raft", GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 })),
                 ("asyncStorageWrites", GoLean.GoValue.bool false),
                 ("prevSoftSt", GoLean.GoValue.addr (GoLean.Loc.base { id := 3344 })),
                 ("prevHardSt", GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 })),
                 ("stepsOnAdvance",
                  GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 })] }),
 (GoLean.Loc.base { id := 3344 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }),
    value := GoLean.GoValue.struct
               { key := "raft.SoftState" }
               #[("Lead", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("RaftState", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64))] }),
 (GoLean.Loc.base { id := 3351 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 3354 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 3357 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 3360 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.HardState" }
               #[("Term", GoLean.GoValue.addr (GoLean.Loc.base { id := 3351 })),
                 ("Vote", GoLean.GoValue.addr (GoLean.Loc.base { id := 3354 })),
                 ("Commit", GoLean.GoValue.addr (GoLean.Loc.base { id := 3357 }))] }),
 (GoLean.Loc.base { id := 3369 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
    value := GoLean.GoValue.struct
               { key := "main.twinNode" }
               #[("id", GoLean.GoValue.int 3 (GoLean.GoCore.IntKind.uint64)),
                 ("rn", GoLean.GoValue.addr (GoLean.Loc.base { id := 4941 })),
                 ("st", GoLean.GoValue.addr (GoLean.Loc.base { id := 3378 })),
                 ("term", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("commit", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("state", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("lastTrm", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("got", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 3366 }) })] }),
 (GoLean.Loc.base { id := 6070 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6072 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6073 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32)),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6074 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6075 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6076 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.Message" }
               #[("Type", GoLean.GoValue.addr (GoLean.Loc.base { id := 6073 })),
                 ("To", GoLean.GoValue.addr (GoLean.Loc.base { id := 6074 })),
                 ("From", GoLean.GoValue.addr (GoLean.Loc.base { id := 6075 })), ("Term", GoLean.GoValue.nil),
                 ("LogTerm", GoLean.GoValue.nil), ("Index", GoLean.GoValue.nil),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Commit", GoLean.GoValue.nil), ("Vote", GoLean.GoValue.nil),
                 ("Snapshot", GoLean.GoValue.nil), ("Reject", GoLean.GoValue.nil),
                 ("RejectHint", GoLean.GoValue.nil),
                 ("Context", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Responses", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 })] }),
 (GoLean.Loc.base { id := 6077 },
  { declaredTy := some (GoLean.GoCore.Ty.array
                    1
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.array #[GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 })] }),
 (GoLean.Loc.base { id := 6078 },
  { declaredTy := some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.array #[GoLean.GoValue.bool true] })]

def rhbC0 : GoLean.GoCore.Machine.Config :=
  GoLean.GoCore.Machine.Config.exec
  (GoLean.GoCore.Stmt.ifThenElse
    (GoLean.GoCore.Expr.lessCmp
      (GoLean.GoCore.Expr.var "round")
      (GoLean.GoCore.Expr.intLit 400 (GoLean.GoCore.IntKind.int)))
    (GoLean.GoCore.Stmt.seqn #[])
    (GoLean.GoCore.Stmt.breakStmt))
  [[],
   [("$forFirst", GoLean.Loc.base { id := 6072 })],
   [],
   [("stuckPropose", GoLean.Loc.base { id := 6071 }),
    ("round", GoLean.Loc.base { id := 6070 }),
    ("t", GoLean.Loc.base { id := 110 })],
   [("$res2", GoLean.Loc.base { id := 108 }),
    ("$res1", GoLean.Loc.base { id := 107 }),
    ("$res0", GoLean.Loc.base { id := 106 })]]
  (GoLean.GoCore.Machine.Cont.seq
    [GoLean.GoCore.Stmt.block
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
             GoLean.GoCore.Stmt.assign
               (GoLean.GoCore.Assignee.var "$rfirst")
               (GoLean.GoCore.Expr.boolLit true),
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
                     (GoLean.GoCore.Expr.atLeastCmp
                       (GoLean.GoCore.Expr.var "$ridx")
                       (GoLean.GoCore.Expr.var "$rlen"))
                     (GoLean.GoCore.Stmt.breakStmt)
                     (GoLean.GoCore.Stmt.seqn #[]),
                   GoLean.GoCore.Stmt.initialization
                     { id := "j", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                   GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.var "j")
                     (GoLean.GoCore.Expr.var "$ridx"),
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
               (some (GoLean.GoCore.Ty.map
                  (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                  (GoLean.GoCore.Ty.bool))))
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
                       #[GoLean.GoCore.Stmt.assign
                           (GoLean.GoCore.Assignee.var "picked")
                           (GoLean.GoCore.Expr.var "j")],
                     GoLean.GoCore.Stmt.breakStmt]),
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.initialization
                     { id := "m",
                       typ := GoLean.GoCore.Ty.pointer
                                (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
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
                             (GoLean.GoCore.Expr.fieldAddr
                               (GoLean.GoCore.Expr.var "t")
                               { key := "main.twin" }
                               "halt"))
                           (GoLean.GoCore.Expr.boolLit true)],
                     GoLean.GoCore.Stmt.call
                       #[]
                       { key := "main.twin.say" }
                       #[GoLean.GoCore.Expr.var "t",
                         GoLean.GoCore.Expr.stringLit
                           { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112, 111,
                                        115, 101, 32, 115, 116, 117, 99, 107, 32, 97, 116, 32, 113, 117, 105,
                                        101, 115, 99, 101, 110, 99, 101, 10] }],
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
               { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101, 110,
                            116, 32, 119, 105, 116, 104, 111, 117, 116, 32, 83, 52, 10] }],
         GoLean.GoCore.Stmt.breakStmt]]
    [[],
     [("$forFirst", GoLean.Loc.base { id := 6072 })],
     [],
     [("stuckPropose", GoLean.Loc.base { id := 6071 }),
      ("round", GoLean.Loc.base { id := 6070 }),
      ("t", GoLean.Loc.base { id := 110 })],
     [("$res2", GoLean.Loc.base { id := 108 }),
      ("$res1", GoLean.Loc.base { id := 107 }),
      ("$res0", GoLean.Loc.base { id := 106 })]]
    (GoLean.GoCore.Machine.Cont.loop
      (GoLean.GoCore.Expr.boolLit true)
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.ifThenElse
            (GoLean.GoCore.Expr.var "$forFirst")
            (GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$forFirst")
              (GoLean.GoCore.Expr.boolLit false))
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
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "live")
                    (GoLean.GoCore.Expr.var "$c2235")],
              GoLean.GoCore.Stmt.block
                #[]
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$rcoll",
                      typ := GoLean.GoCore.Ty.slice
                               (GoLean.GoCore.Ty.pointer
                                 (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
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
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$rfirst")
                    (GoLean.GoCore.Expr.boolLit true),
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
                          (GoLean.GoCore.Expr.atLeastCmp
                            (GoLean.GoCore.Expr.var "$ridx")
                            (GoLean.GoCore.Expr.var "$rlen"))
                          (GoLean.GoCore.Stmt.breakStmt)
                          (GoLean.GoCore.Stmt.seqn #[]),
                        GoLean.GoCore.Stmt.initialization
                          { id := "j", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "j")
                          (GoLean.GoCore.Expr.var "$ridx"),
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
                    (some (GoLean.GoCore.Ty.map
                       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                       (GoLean.GoCore.Ty.bool))))
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
                            #[GoLean.GoCore.Stmt.assign
                                (GoLean.GoCore.Assignee.var "picked")
                                (GoLean.GoCore.Expr.var "j")],
                          GoLean.GoCore.Stmt.breakStmt]),
                    GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "m",
                            typ := GoLean.GoCore.Ty.pointer
                                     (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
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
                            GoLean.GoCore.Expr.defaultValue
                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
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
                                  (GoLean.GoCore.Expr.fieldAddr
                                    (GoLean.GoCore.Expr.var "t")
                                    { key := "main.twin" }
                                    "halt"))
                                (GoLean.GoCore.Expr.boolLit true)],
                          GoLean.GoCore.Stmt.call
                            #[]
                            { key := "main.twin.say" }
                            #[GoLean.GoCore.Expr.var "t",
                              GoLean.GoCore.Expr.stringLit
                                { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112,
                                             111, 115, 101, 32, 115, 116, 117, 99, 107, 32, 97, 116, 32, 113,
                                             117, 105, 101, 115, 99, 101, 110, 99, 101, 10] }],
                          GoLean.GoCore.Stmt.breakStmt])
                      (GoLean.GoCore.Stmt.seqn #[]),
                    GoLean.GoCore.Stmt.continueStmt])
                (GoLean.GoCore.Stmt.seqn #[]),
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr
                        (GoLean.GoCore.Expr.var "t")
                        { key := "main.twin" }
                        "halt"))
                    (GoLean.GoCore.Expr.boolLit true)],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.stringLit
                    { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101,
                                 110, 116, 32, 119, 105, 116, 104, 111, 117, 116, 32, 83, 52, 10] }],
              GoLean.GoCore.Stmt.breakStmt]])
      [[("$forFirst", GoLean.Loc.base { id := 6072 })],
       [],
       [("stuckPropose", GoLean.Loc.base { id := 6071 }),
        ("round", GoLean.Loc.base { id := 6070 }),
        ("t", GoLean.Loc.base { id := 110 })],
       [("$res2", GoLean.Loc.base { id := 108 }),
        ("$res1", GoLean.Loc.base { id := 107 }),
        ("$res0", GoLean.Loc.base { id := 106 })]]
      (GoLean.GoCore.Machine.Cont.seq
        []
        [[("$forFirst", GoLean.Loc.base { id := 6072 })],
         [],
         [("stuckPropose", GoLean.Loc.base { id := 6071 }),
          ("round", GoLean.Loc.base { id := 6070 }),
          ("t", GoLean.Loc.base { id := 110 })],
         [("$res2", GoLean.Loc.base { id := 108 }),
          ("$res1", GoLean.Loc.base { id := 107 }),
          ("$res0", GoLean.Loc.base { id := 106 })]]
        (GoLean.GoCore.Machine.Cont.seq
          []
          [[],
           [("stuckPropose", GoLean.Loc.base { id := 6071 }),
            ("round", GoLean.Loc.base { id := 6070 }),
            ("t", GoLean.Loc.base { id := 110 })],
           [("$res2", GoLean.Loc.base { id := 108 }),
            ("$res1", GoLean.Loc.base { id := 107 }),
            ("$res0", GoLean.Loc.base { id := 106 })]]
          (GoLean.GoCore.Machine.Cont.seq
            [GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.initialization
                   { id := "comp", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
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
                         (GoLean.GoCore.Expr.deref
                           (GoLean.GoCore.Expr.var "t")
                           (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                         { key := "main.twin" }
                         "pending")
                       (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.not
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "t")
                       (GoLean.GoCore.Ty.defined { key := "main.twin" }))
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
               #[GoLean.GoCore.Stmt.initialization
                   { id := "floorOK", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                 GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.var "floorOK")
                   (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))],
             GoLean.GoCore.Stmt.ifThenElse
               (GoLean.GoCore.Expr.or
                 (GoLean.GoCore.Expr.lessCmp
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "t")
                       (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                     { key := "main.twin" }
                     "claims")
                   (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))
                 (GoLean.GoCore.Expr.lessCmp
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "t")
                       (GoLean.GoCore.Ty.defined { key := "main.twin" }))
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
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "t")
                         (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                       { key := "main.twin" }
                       "violations"]],
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.initialization { id := "$c2247", typ := GoLean.GoCore.Ty.string },
                 GoLean.GoCore.Stmt.call
                   #[GoLean.GoCore.Assignee.var "$c2247"]
                   { key := "itoa" }
                   #[GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "t")
                         (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                       { key := "main.twin" }
                       "claims"]],
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.initialization { id := "$c2248", typ := GoLean.GoCore.Ty.string },
                 GoLean.GoCore.Stmt.call
                   #[GoLean.GoCore.Assignee.var "$c2248"]
                   { key := "itoa" }
                   #[GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "t")
                         (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                       { key := "main.twin" }
                       "committed"]],
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.initialization { id := "$c2249", typ := GoLean.GoCore.Ty.string },
                 GoLean.GoCore.Stmt.call
                   #[GoLean.GoCore.Assignee.var "$c2249"]
                   { key := "itoa" }
                   #[GoLean.GoCore.Expr.var "comp"]],
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
                                         (GoLean.GoCore.Expr.stringLit
                                           { bytes := #[101, 110, 100, 32, 118, 105, 111, 108, 61] })
                                         (GoLean.GoCore.Expr.var "$c2246"))
                                       (GoLean.GoCore.Expr.stringLit
                                         { bytes := #[32, 99, 108, 97, 105, 109, 115, 61] }))
                                     (GoLean.GoCore.Expr.var "$c2247"))
                                   (GoLean.GoCore.Expr.stringLit
                                     { bytes := #[32, 99, 111, 109, 109, 105, 116, 116, 101, 100, 61] }))
                                 (GoLean.GoCore.Expr.var "$c2248"))
                               (GoLean.GoCore.Expr.stringLit
                                 { bytes := #[32, 99, 111, 109, 112, 108, 101, 116, 101, 61] }))
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
                 GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.var "$res1")
                   (GoLean.GoCore.Expr.var "comp"),
                 GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.var "$res2")
                   (GoLean.GoCore.Expr.var "floorOK"),
                 GoLean.GoCore.Stmt.returnStmt]]
            [[("stuckPropose", GoLean.Loc.base { id := 6071 }),
              ("round", GoLean.Loc.base { id := 6070 }),
              ("t", GoLean.Loc.base { id := 110 })],
             [("$res2", GoLean.Loc.base { id := 108 }),
              ("$res1", GoLean.Loc.base { id := 107 }),
              ("$res0", GoLean.Loc.base { id := 106 })]]
            (GoLean.GoCore.Machine.Cont.frame
              [(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "t"]),
               (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "comp"]),
               (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "floorOK"])]
              [[("floorOK", GoLean.Loc.base { id := 105 }),
                ("comp", GoLean.Loc.base { id := 104 }),
                ("t", GoLean.Loc.base { id := 103 })],
               [("$res4", GoLean.Loc.base { id := 102 }),
                ("$res3", GoLean.Loc.base { id := 101 }),
                ("$res2", GoLean.Loc.base { id := 100 }),
                ("$res1", GoLean.Loc.base { id := 99 }),
                ("$res0", GoLean.Loc.base { id := 98 })]]
              [GoLean.Loc.base { id := 106 }, GoLean.Loc.base { id := 107 }, GoLean.Loc.base { id := 108 }]
              []
              (GoLean.GoCore.Machine.Cont.seq
                [GoLean.GoCore.Stmt.seqn
                   #[GoLean.GoCore.Stmt.assign
                       (GoLean.GoCore.Assignee.var "$res0")
                       (GoLean.GoCore.Expr.fieldGet
                         (GoLean.GoCore.Expr.deref
                           (GoLean.GoCore.Expr.var "t")
                           (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                         { key := "main.twin" }
                         "violations"),
                     GoLean.GoCore.Stmt.assign
                       (GoLean.GoCore.Assignee.var "$res1")
                       (GoLean.GoCore.Expr.fieldGet
                         (GoLean.GoCore.Expr.deref
                           (GoLean.GoCore.Expr.var "t")
                           (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                         { key := "main.twin" }
                         "claims"),
                     GoLean.GoCore.Stmt.assign
                       (GoLean.GoCore.Assignee.var "$res2")
                       (GoLean.GoCore.Expr.fieldGet
                         (GoLean.GoCore.Expr.deref
                           (GoLean.GoCore.Expr.var "t")
                           (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                         { key := "main.twin" }
                         "committed"),
                     GoLean.GoCore.Stmt.assign
                       (GoLean.GoCore.Assignee.var "$res3")
                       (GoLean.GoCore.Expr.var "comp"),
                     GoLean.GoCore.Stmt.assign
                       (GoLean.GoCore.Assignee.var "$res4")
                       (GoLean.GoCore.Expr.var "floorOK"),
                     GoLean.GoCore.Stmt.returnStmt]]
                [[("floorOK", GoLean.Loc.base { id := 105 }),
                  ("comp", GoLean.Loc.base { id := 104 }),
                  ("t", GoLean.Loc.base { id := 103 })],
                 [("$res4", GoLean.Loc.base { id := 102 }),
                  ("$res3", GoLean.Loc.base { id := 101 }),
                  ("$res2", GoLean.Loc.base { id := 100 }),
                  ("$res1", GoLean.Loc.base { id := 99 }),
                  ("$res0", GoLean.Loc.base { id := 98 })]]
                (GoLean.GoCore.Machine.Cont.frame [] [] [] [] (GoLean.GoCore.Machine.Cont.stop) false))
              false))))))

def rhbCh0 : GoLean.GoCore.Choices := [0, 0, 0, 0]

def rhbNa1 : Nat := 6086

def rhbHeap1 : GoLean.GoCore.Heap :=
  [(GoLean.Loc.base { id := 15 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 57 }) }),
 (GoLean.Loc.base { id := 27 },
  { declaredTy := some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.array
               #[GoLean.GoValue.bool true, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool true,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool true,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool true] }),
 (GoLean.Loc.base { id := 28 },
  { declaredTy := some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.array
               #[GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool false, GoLean.GoValue.bool true,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true] }),
 (GoLean.Loc.base { id := 57 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.HardState" }
               #[("Term", GoLean.GoValue.nil), ("Vote", GoLean.GoValue.nil),
                 ("Commit", GoLean.GoValue.nil)] }),
 (GoLean.Loc.base { id := 110 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 121 }) }),
 (GoLean.Loc.base { id := 121 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twin" }),
    value := GoLean.GoValue.struct
               { key := "main.twin" }
               #[("nodes",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 1764 }), offset := 0, len := 3, cap := 4 }),
                 ("net",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6077 }), offset := 0, len := 1, cap := 1 }),
                 ("live",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6078 }), offset := 0, len := 1, cap := 1 }),
                 ("leaderOf", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 115 }) }),
                 ("byIndex", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 118 }) }),
                 ("claims", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("committed", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("violations", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("pending",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 136 }), offset := 0, len := 2, cap := 4 }),
                 ("driven", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("seq", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.int)),
                 ("trace",
                  GoLean.GoValue.string
                    { bytes := #[91, 99, 104, 111, 105, 99, 101, 45, 100, 114, 105, 118, 101, 110, 93, 10, 99,
                                 97, 109, 112, 97, 105, 103, 110, 49] }),
                 ("halt", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 170 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
    value := GoLean.GoValue.struct
               { key := "main.twinNode" }
               #[("id", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("rn", GoLean.GoValue.addr (GoLean.Loc.base { id := 1742 })),
                 ("st", GoLean.GoValue.addr (GoLean.Loc.base { id := 179 })),
                 ("term", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("commit", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("state", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("lastTrm", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("got", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 167 }) })] }),
 (GoLean.Loc.base { id := 1764 },
  { declaredTy := some (GoLean.GoCore.Ty.array
                    4
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))),
    value := GoLean.GoValue.array
               #[GoLean.GoValue.addr (GoLean.Loc.base { id := 170 }),
                 GoLean.GoValue.addr (GoLean.Loc.base { id := 1770 }),
                 GoLean.GoValue.addr (GoLean.Loc.base { id := 3369 }), GoLean.GoValue.nil] }),
 (GoLean.Loc.base { id := 1770 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
    value := GoLean.GoValue.struct
               { key := "main.twinNode" }
               #[("id", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                 ("rn", GoLean.GoValue.addr (GoLean.Loc.base { id := 3342 })),
                 ("st", GoLean.GoValue.addr (GoLean.Loc.base { id := 1779 })),
                 ("term", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("commit", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("state", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("lastTrm", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("got", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 1767 }) })] }),
 (GoLean.Loc.base { id := 1949 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }),
    value := GoLean.GoValue.struct
               { key := "raft.raftLog" }
               #[("storage",
                  GoLean.GoValue.interface
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }))
                    (GoLean.GoValue.addr (GoLean.Loc.base { id := 1779 }))),
                 ("unstable",
                  GoLean.GoValue.struct
                    { key := "raft.unstable" }
                    #[("snapshot", GoLean.GoValue.nil),
                      ("entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                      ("offset", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                      ("snapshotInProgress", GoLean.GoValue.bool false),
                      ("offsetInProgress", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                      ("logger",
                       GoLean.GoValue.interface
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
                         (GoLean.GoValue.addr (GoLean.Loc.base { id := 97 })))]),
                 ("committed", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("applying", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("logger",
                  GoLean.GoValue.interface
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
                    (GoLean.GoValue.addr (GoLean.Loc.base { id := 97 }))),
                 ("maxApplyingEntsSize", GoLean.GoValue.int 1048576 (GoLean.GoCore.IntKind.uint64)),
                 ("applyingEntsSize", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("applyingEntsPaused", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 1989 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.raft" }),
    value := GoLean.GoValue.struct
               { key := "raft.raft" }
               #[("id", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                 ("Term", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("Vote", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("readStates", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("raftLog", GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 })),
                 ("maxMsgSize", GoLean.GoValue.int 1048576 (GoLean.GoCore.IntKind.uint64)),
                 ("maxUncommittedSize",
                  GoLean.GoValue.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
                 ("trk",
                  GoLean.GoValue.struct
                    { key := "tracker.ProgressTracker" }
                    #[("Config",
                       GoLean.GoValue.struct
                         { key := "tracker.Config" }
                         #[("Voters",
                            GoLean.GoValue.array
                              #[GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 2686 }) },
                                GoLean.GoValue.map { base := none }]),
                           ("AutoLeave", GoLean.GoValue.bool false),
                           ("Learners", GoLean.GoValue.map { base := none }),
                           ("LearnersNext", GoLean.GoValue.map { base := none })]),
                      ("Progress", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 2703 }) }),
                      ("Votes", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 3059 }) }),
                      ("MaxInflight", GoLean.GoValue.int 256 (GoLean.GoCore.IntKind.int)),
                      ("MaxInflightBytes",
                       GoLean.GoValue.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64))]),
                 ("state", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("isLearner", GoLean.GoValue.bool false),
                 ("msgs", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("msgsAfterAppend", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("lead", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("leadTransferee", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("pendingConfIndex", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("disableConfChangeValidation", GoLean.GoValue.bool false),
                 ("uncommittedSize", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("readOnly", GoLean.GoValue.addr (GoLean.Loc.base { id := 3199 })),
                 ("electionElapsed", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("heartbeatElapsed", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("checkQuorum", GoLean.GoValue.bool false), ("preVote", GoLean.GoValue.bool false),
                 ("heartbeatTimeout", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int)),
                 ("electionTimeout", GoLean.GoValue.int 10 (GoLean.GoCore.IntKind.int)),
                 ("randomizedElectionTimeout", GoLean.GoValue.int 10 (GoLean.GoCore.IntKind.int)),
                 ("disableProposalForwarding", GoLean.GoValue.bool false),
                 ("stepDownOnRemoval", GoLean.GoValue.bool false),
                 ("tick",
                  GoLean.GoValue.funcVal
                    { key := "raft.raft.tickElection" }
                    [GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 })]),
                 ("step", GoLean.GoValue.funcVal { key := "raft.stepFollower" } []),
                 ("logger",
                  GoLean.GoValue.interface
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
                    (GoLean.GoValue.addr (GoLean.Loc.base { id := 97 }))),
                 ("pendingReadIndexMessages",
                  GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("traceLogger", GoLean.GoValue.nil)] }),
 (GoLean.Loc.base { id := 3342 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }),
    value := GoLean.GoValue.struct
               { key := "raft.RawNode" }
               #[("raft", GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 })),
                 ("asyncStorageWrites", GoLean.GoValue.bool false),
                 ("prevSoftSt", GoLean.GoValue.addr (GoLean.Loc.base { id := 3344 })),
                 ("prevHardSt", GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 })),
                 ("stepsOnAdvance",
                  GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 })] }),
 (GoLean.Loc.base { id := 3344 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }),
    value := GoLean.GoValue.struct
               { key := "raft.SoftState" }
               #[("Lead", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("RaftState", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64))] }),
 (GoLean.Loc.base { id := 3351 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 3354 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 3357 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 3360 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.HardState" }
               #[("Term", GoLean.GoValue.addr (GoLean.Loc.base { id := 3351 })),
                 ("Vote", GoLean.GoValue.addr (GoLean.Loc.base { id := 3354 })),
                 ("Commit", GoLean.GoValue.addr (GoLean.Loc.base { id := 3357 }))] }),
 (GoLean.Loc.base { id := 3369 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
    value := GoLean.GoValue.struct
               { key := "main.twinNode" }
               #[("id", GoLean.GoValue.int 3 (GoLean.GoCore.IntKind.uint64)),
                 ("rn", GoLean.GoValue.addr (GoLean.Loc.base { id := 4941 })),
                 ("st", GoLean.GoValue.addr (GoLean.Loc.base { id := 3378 })),
                 ("term", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("commit", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("state", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("lastTrm", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("got", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 3366 }) })] }),
 (GoLean.Loc.base { id := 6070 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6072 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6073 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32)),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6074 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6075 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6076 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.Message" }
               #[("Type", GoLean.GoValue.addr (GoLean.Loc.base { id := 6073 })),
                 ("To", GoLean.GoValue.addr (GoLean.Loc.base { id := 6074 })),
                 ("From", GoLean.GoValue.addr (GoLean.Loc.base { id := 6075 })), ("Term", GoLean.GoValue.nil),
                 ("LogTerm", GoLean.GoValue.nil), ("Index", GoLean.GoValue.nil),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Commit", GoLean.GoValue.nil), ("Vote", GoLean.GoValue.nil),
                 ("Snapshot", GoLean.GoValue.nil), ("Reject", GoLean.GoValue.nil),
                 ("RejectHint", GoLean.GoValue.nil),
                 ("Context", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Responses", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 })] }),
 (GoLean.Loc.base { id := 6077 },
  { declaredTy := some (GoLean.GoCore.Ty.array
                    1
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.array #[GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 })] }),
 (GoLean.Loc.base { id := 6078 },
  { declaredTy := some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.array #[GoLean.GoValue.bool true] }),
 (GoLean.Loc.base { id := 6079 },
  { declaredTy := some (GoLean.GoCore.Ty.map
                    (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                    (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 6080 }) } }),
 (GoLean.Loc.base { id := 6080 }, { declaredTy := none, value := GoLean.GoValue.mapData #[] }),
 (GoLean.Loc.base { id := 6081 },
  { declaredTy := some (GoLean.GoCore.Ty.map
                    (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                    (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 6080 }) } }),
 (GoLean.Loc.base { id := 6082 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.slice
               { base := some (GoLean.Loc.base { id := 6077 }), offset := 0, len := 1, cap := 1 } }),
 (GoLean.Loc.base { id := 6083 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6084 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6085 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false })]

def rhbC1 : GoLean.GoCore.Machine.Config :=
  GoLean.GoCore.Machine.Config.next
  (GoLean.GoCore.Machine.Cont.seq
    [GoLean.GoCore.Stmt.ifThenElse
       (GoLean.GoCore.Expr.atLeastCmp (GoLean.GoCore.Expr.var "$ridx") (GoLean.GoCore.Expr.var "$rlen"))
       (GoLean.GoCore.Stmt.breakStmt)
       (GoLean.GoCore.Stmt.seqn #[]),
     GoLean.GoCore.Stmt.initialization { id := "j", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
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
           (GoLean.GoCore.Stmt.seqn #[])]]
    [[],
     [("$rfirst", GoLean.Loc.base { id := 6085 }),
      ("$ridx", GoLean.Loc.base { id := 6084 }),
      ("$rlen", GoLean.Loc.base { id := 6083 }),
      ("$rcoll", GoLean.Loc.base { id := 6082 })],
     [("live", GoLean.Loc.base { id := 6081 }), ("$c2235", GoLean.Loc.base { id := 6079 })],
     [],
     [("$forFirst", GoLean.Loc.base { id := 6072 })],
     [],
     [("stuckPropose", GoLean.Loc.base { id := 6071 }),
      ("round", GoLean.Loc.base { id := 6070 }),
      ("t", GoLean.Loc.base { id := 110 })],
     [("$res2", GoLean.Loc.base { id := 108 }),
      ("$res1", GoLean.Loc.base { id := 107 }),
      ("$res0", GoLean.Loc.base { id := 106 })]]
    (GoLean.GoCore.Machine.Cont.loop
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
                (GoLean.GoCore.Stmt.seqn #[])]])
      [[("$rfirst", GoLean.Loc.base { id := 6085 }),
        ("$ridx", GoLean.Loc.base { id := 6084 }),
        ("$rlen", GoLean.Loc.base { id := 6083 }),
        ("$rcoll", GoLean.Loc.base { id := 6082 })],
       [("live", GoLean.Loc.base { id := 6081 }), ("$c2235", GoLean.Loc.base { id := 6079 })],
       [],
       [("$forFirst", GoLean.Loc.base { id := 6072 })],
       [],
       [("stuckPropose", GoLean.Loc.base { id := 6071 }),
        ("round", GoLean.Loc.base { id := 6070 }),
        ("t", GoLean.Loc.base { id := 110 })],
       [("$res2", GoLean.Loc.base { id := 108 }),
        ("$res1", GoLean.Loc.base { id := 107 }),
        ("$res0", GoLean.Loc.base { id := 106 })]]
      (GoLean.GoCore.Machine.Cont.seq
        []
        [[("$rfirst", GoLean.Loc.base { id := 6085 }),
          ("$ridx", GoLean.Loc.base { id := 6084 }),
          ("$rlen", GoLean.Loc.base { id := 6083 }),
          ("$rcoll", GoLean.Loc.base { id := 6082 })],
         [("live", GoLean.Loc.base { id := 6081 }), ("$c2235", GoLean.Loc.base { id := 6079 })],
         [],
         [("$forFirst", GoLean.Loc.base { id := 6072 })],
         [],
         [("stuckPropose", GoLean.Loc.base { id := 6071 }),
          ("round", GoLean.Loc.base { id := 6070 }),
          ("t", GoLean.Loc.base { id := 110 })],
         [("$res2", GoLean.Loc.base { id := 108 }),
          ("$res1", GoLean.Loc.base { id := 107 }),
          ("$res0", GoLean.Loc.base { id := 106 })]]
        (GoLean.GoCore.Machine.Cont.seq
          [GoLean.GoCore.Stmt.ifThenElse
             (GoLean.GoCore.Expr.greaterCmp
               (GoLean.GoCore.Expr.length
                 (GoLean.GoCore.Expr.var "live")
                 (some (GoLean.GoCore.Ty.map
                    (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                    (GoLean.GoCore.Ty.bool))))
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
                         #[GoLean.GoCore.Stmt.assign
                             (GoLean.GoCore.Assignee.var "picked")
                             (GoLean.GoCore.Expr.var "j")],
                       GoLean.GoCore.Stmt.breakStmt]),
                 GoLean.GoCore.Stmt.seqn
                   #[GoLean.GoCore.Stmt.initialization
                       { id := "m",
                         typ := GoLean.GoCore.Ty.pointer
                                  (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
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
                               (GoLean.GoCore.Expr.fieldAddr
                                 (GoLean.GoCore.Expr.var "t")
                                 { key := "main.twin" }
                                 "halt"))
                             (GoLean.GoCore.Expr.boolLit true)],
                       GoLean.GoCore.Stmt.call
                         #[]
                         { key := "main.twin.say" }
                         #[GoLean.GoCore.Expr.var "t",
                           GoLean.GoCore.Expr.stringLit
                             { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112, 111,
                                          115, 101, 32, 115, 116, 117, 99, 107, 32, 97, 116, 32, 113, 117,
                                          105, 101, 115, 99, 101, 110, 99, 101, 10] }],
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
                 { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101, 110,
                              116, 32, 119, 105, 116, 104, 111, 117, 116, 32, 83, 52, 10] }],
           GoLean.GoCore.Stmt.breakStmt]
          [[("live", GoLean.Loc.base { id := 6081 }), ("$c2235", GoLean.Loc.base { id := 6079 })],
           [],
           [("$forFirst", GoLean.Loc.base { id := 6072 })],
           [],
           [("stuckPropose", GoLean.Loc.base { id := 6071 }),
            ("round", GoLean.Loc.base { id := 6070 }),
            ("t", GoLean.Loc.base { id := 110 })],
           [("$res2", GoLean.Loc.base { id := 108 }),
            ("$res1", GoLean.Loc.base { id := 107 }),
            ("$res0", GoLean.Loc.base { id := 106 })]]
          (GoLean.GoCore.Machine.Cont.seq
            []
            [[],
             [("$forFirst", GoLean.Loc.base { id := 6072 })],
             [],
             [("stuckPropose", GoLean.Loc.base { id := 6071 }),
              ("round", GoLean.Loc.base { id := 6070 }),
              ("t", GoLean.Loc.base { id := 110 })],
             [("$res2", GoLean.Loc.base { id := 108 }),
              ("$res1", GoLean.Loc.base { id := 107 }),
              ("$res0", GoLean.Loc.base { id := 106 })]]
            (GoLean.GoCore.Machine.Cont.loop
              (GoLean.GoCore.Expr.boolLit true)
              (GoLean.GoCore.Stmt.block
                #[]
                #[GoLean.GoCore.Stmt.ifThenElse
                    (GoLean.GoCore.Expr.var "$forFirst")
                    (GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "$forFirst")
                      (GoLean.GoCore.Expr.boolLit false))
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
                          GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.var "live")
                            (GoLean.GoCore.Expr.var "$c2235")],
                      GoLean.GoCore.Stmt.block
                        #[]
                        #[GoLean.GoCore.Stmt.initialization
                            { id := "$rcoll",
                              typ := GoLean.GoCore.Ty.slice
                                       (GoLean.GoCore.Ty.pointer
                                         (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
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
                          GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.var "$rfirst")
                            (GoLean.GoCore.Expr.boolLit true),
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
                                  (GoLean.GoCore.Expr.atLeastCmp
                                    (GoLean.GoCore.Expr.var "$ridx")
                                    (GoLean.GoCore.Expr.var "$rlen"))
                                  (GoLean.GoCore.Stmt.breakStmt)
                                  (GoLean.GoCore.Stmt.seqn #[]),
                                GoLean.GoCore.Stmt.initialization
                                  { id := "j", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "j")
                                  (GoLean.GoCore.Expr.var "$ridx"),
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
                            (some (GoLean.GoCore.Ty.map
                               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                               (GoLean.GoCore.Ty.bool))))
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
                                    #[GoLean.GoCore.Stmt.assign
                                        (GoLean.GoCore.Assignee.var "picked")
                                        (GoLean.GoCore.Expr.var "j")],
                                  GoLean.GoCore.Stmt.breakStmt]),
                            GoLean.GoCore.Stmt.seqn
                              #[GoLean.GoCore.Stmt.initialization
                                  { id := "m",
                                    typ := GoLean.GoCore.Ty.pointer
                                             (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
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
                              #[GoLean.GoCore.Stmt.initialization
                                  { id := "$c2236", typ := GoLean.GoCore.Ty.string },
                                GoLean.GoCore.Stmt.call
                                  #[GoLean.GoCore.Assignee.var "$c2236"]
                                  { key := "itoa" }
                                  #[GoLean.GoCore.Expr.add
                                      (GoLean.GoCore.Expr.var "round")
                                      (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
                            GoLean.GoCore.Stmt.seqn
                              #[GoLean.GoCore.Stmt.initialization
                                  { id := "$c2237", typ := GoLean.GoCore.Ty.string },
                                GoLean.GoCore.Stmt.call
                                  #[GoLean.GoCore.Assignee.var "$c2237"]
                                  { key := "itoa" }
                                  #[GoLean.GoCore.Expr.var "picked"]],
                            GoLean.GoCore.Stmt.seqn
                              #[GoLean.GoCore.Stmt.initialization
                                  { id := "$c2238",
                                    typ := GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" } },
                                GoLean.GoCore.Stmt.call
                                  #[GoLean.GoCore.Assignee.var "$c2238"]
                                  { key := "raftpb.Message.GetType" }
                                  #[GoLean.GoCore.Expr.var "m"]],
                            GoLean.GoCore.Stmt.seqn
                              #[GoLean.GoCore.Stmt.initialization
                                  { id := "$c2239", typ := GoLean.GoCore.Ty.string },
                                GoLean.GoCore.Stmt.call
                                  #[GoLean.GoCore.Assignee.var "$c2239"]
                                  { key := "itoa" }
                                  #[GoLean.GoCore.Expr.convert
                                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                                      (GoLean.GoCore.Expr.var "$c2238")]],
                            GoLean.GoCore.Stmt.seqn
                              #[GoLean.GoCore.Stmt.initialization
                                  { id := "$c2240",
                                    typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                GoLean.GoCore.Stmt.call
                                  #[GoLean.GoCore.Assignee.var "$c2240"]
                                  { key := "raftpb.Message.GetTo" }
                                  #[GoLean.GoCore.Expr.var "m"]],
                            GoLean.GoCore.Stmt.seqn
                              #[GoLean.GoCore.Stmt.initialization
                                  { id := "$c2241", typ := GoLean.GoCore.Ty.string },
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
                                            (GoLean.GoCore.Expr.stringLit
                                              { bytes := #[32, 112, 105, 99, 107, 35] }))
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
                              #[GoLean.GoCore.Stmt.initialization
                                  { id := "$c2242", typ := GoLean.GoCore.Ty.string },
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
                              #[GoLean.GoCore.Stmt.initialization
                                  { id := "$c2244", typ := GoLean.GoCore.Ty.string },
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
                                    GoLean.GoCore.Expr.defaultValue
                                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
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
                                          (GoLean.GoCore.Expr.fieldAddr
                                            (GoLean.GoCore.Expr.var "t")
                                            { key := "main.twin" }
                                            "halt"))
                                        (GoLean.GoCore.Expr.boolLit true)],
                                  GoLean.GoCore.Stmt.call
                                    #[]
                                    { key := "main.twin.say" }
                                    #[GoLean.GoCore.Expr.var "t",
                                      GoLean.GoCore.Expr.stringLit
                                        { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111,
                                                     112, 111, 115, 101, 32, 115, 116, 117, 99, 107, 32, 97,
                                                     116, 32, 113, 117, 105, 101, 115, 99, 101, 110, 99, 101,
                                                     10] }],
                                  GoLean.GoCore.Stmt.breakStmt])
                              (GoLean.GoCore.Stmt.seqn #[]),
                            GoLean.GoCore.Stmt.continueStmt])
                        (GoLean.GoCore.Stmt.seqn #[]),
                      GoLean.GoCore.Stmt.seqn
                        #[GoLean.GoCore.Stmt.assign
                            (GoLean.GoCore.Assignee.addr
                              (GoLean.GoCore.Expr.fieldAddr
                                (GoLean.GoCore.Expr.var "t")
                                { key := "main.twin" }
                                "halt"))
                            (GoLean.GoCore.Expr.boolLit true)],
                      GoLean.GoCore.Stmt.call
                        #[]
                        { key := "main.twin.say" }
                        #[GoLean.GoCore.Expr.var "t",
                          GoLean.GoCore.Expr.stringLit
                            { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115,
                                         99, 101, 110, 116, 32, 119, 105, 116, 104, 111, 117, 116, 32, 83, 52,
                                         10] }],
                      GoLean.GoCore.Stmt.breakStmt]])
              [[("$forFirst", GoLean.Loc.base { id := 6072 })],
               [],
               [("stuckPropose", GoLean.Loc.base { id := 6071 }),
                ("round", GoLean.Loc.base { id := 6070 }),
                ("t", GoLean.Loc.base { id := 110 })],
               [("$res2", GoLean.Loc.base { id := 108 }),
                ("$res1", GoLean.Loc.base { id := 107 }),
                ("$res0", GoLean.Loc.base { id := 106 })]]
              (GoLean.GoCore.Machine.Cont.seq
                []
                [[("$forFirst", GoLean.Loc.base { id := 6072 })],
                 [],
                 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
                  ("round", GoLean.Loc.base { id := 6070 }),
                  ("t", GoLean.Loc.base { id := 110 })],
                 [("$res2", GoLean.Loc.base { id := 108 }),
                  ("$res1", GoLean.Loc.base { id := 107 }),
                  ("$res0", GoLean.Loc.base { id := 106 })]]
                (GoLean.GoCore.Machine.Cont.seq
                  []
                  [[],
                   [("stuckPropose", GoLean.Loc.base { id := 6071 }),
                    ("round", GoLean.Loc.base { id := 6070 }),
                    ("t", GoLean.Loc.base { id := 110 })],
                   [("$res2", GoLean.Loc.base { id := 108 }),
                    ("$res1", GoLean.Loc.base { id := 107 }),
                    ("$res0", GoLean.Loc.base { id := 106 })]]
                  (GoLean.GoCore.Machine.Cont.seq
                    [GoLean.GoCore.Stmt.seqn
                       #[GoLean.GoCore.Stmt.initialization
                           { id := "comp", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
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
                                 (GoLean.GoCore.Expr.deref
                                   (GoLean.GoCore.Expr.var "t")
                                   (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                                 { key := "main.twin" }
                                 "pending")
                               (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
                             (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                         (GoLean.GoCore.Expr.not
                           (GoLean.GoCore.Expr.fieldGet
                             (GoLean.GoCore.Expr.deref
                               (GoLean.GoCore.Expr.var "t")
                               (GoLean.GoCore.Ty.defined { key := "main.twin" }))
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
                       #[GoLean.GoCore.Stmt.initialization
                           { id := "floorOK", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                         GoLean.GoCore.Stmt.assign
                           (GoLean.GoCore.Assignee.var "floorOK")
                           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))],
                     GoLean.GoCore.Stmt.ifThenElse
                       (GoLean.GoCore.Expr.or
                         (GoLean.GoCore.Expr.lessCmp
                           (GoLean.GoCore.Expr.fieldGet
                             (GoLean.GoCore.Expr.deref
                               (GoLean.GoCore.Expr.var "t")
                               (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                             { key := "main.twin" }
                             "claims")
                           (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))
                         (GoLean.GoCore.Expr.lessCmp
                           (GoLean.GoCore.Expr.fieldGet
                             (GoLean.GoCore.Expr.deref
                               (GoLean.GoCore.Expr.var "t")
                               (GoLean.GoCore.Ty.defined { key := "main.twin" }))
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
                               (GoLean.GoCore.Expr.deref
                                 (GoLean.GoCore.Expr.var "t")
                                 (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                               { key := "main.twin" }
                               "violations"]],
                     GoLean.GoCore.Stmt.seqn
                       #[GoLean.GoCore.Stmt.initialization { id := "$c2247", typ := GoLean.GoCore.Ty.string },
                         GoLean.GoCore.Stmt.call
                           #[GoLean.GoCore.Assignee.var "$c2247"]
                           { key := "itoa" }
                           #[GoLean.GoCore.Expr.fieldGet
                               (GoLean.GoCore.Expr.deref
                                 (GoLean.GoCore.Expr.var "t")
                                 (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                               { key := "main.twin" }
                               "claims"]],
                     GoLean.GoCore.Stmt.seqn
                       #[GoLean.GoCore.Stmt.initialization { id := "$c2248", typ := GoLean.GoCore.Ty.string },
                         GoLean.GoCore.Stmt.call
                           #[GoLean.GoCore.Assignee.var "$c2248"]
                           { key := "itoa" }
                           #[GoLean.GoCore.Expr.fieldGet
                               (GoLean.GoCore.Expr.deref
                                 (GoLean.GoCore.Expr.var "t")
                                 (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                               { key := "main.twin" }
                               "committed"]],
                     GoLean.GoCore.Stmt.seqn
                       #[GoLean.GoCore.Stmt.initialization { id := "$c2249", typ := GoLean.GoCore.Ty.string },
                         GoLean.GoCore.Stmt.call
                           #[GoLean.GoCore.Assignee.var "$c2249"]
                           { key := "itoa" }
                           #[GoLean.GoCore.Expr.var "comp"]],
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
                                                 (GoLean.GoCore.Expr.stringLit
                                                   { bytes := #[101, 110, 100, 32, 118, 105, 111, 108, 61] })
                                                 (GoLean.GoCore.Expr.var "$c2246"))
                                               (GoLean.GoCore.Expr.stringLit
                                                 { bytes := #[32, 99, 108, 97, 105, 109, 115, 61] }))
                                             (GoLean.GoCore.Expr.var "$c2247"))
                                           (GoLean.GoCore.Expr.stringLit
                                             { bytes := #[32, 99, 111, 109, 109, 105, 116, 116, 101, 100,
                                                          61] }))
                                         (GoLean.GoCore.Expr.var "$c2248"))
                                       (GoLean.GoCore.Expr.stringLit
                                         { bytes := #[32, 99, 111, 109, 112, 108, 101, 116, 101, 61] }))
                                     (GoLean.GoCore.Expr.var "$c2249"))
                                   (GoLean.GoCore.Expr.stringLit
                                     { bytes := #[32, 102, 108, 111, 111, 114, 61] }))
                                 (GoLean.GoCore.Expr.var "$c2250"))
                               (GoLean.GoCore.Expr.stringLit
                                 { bytes := #[32, 114, 111, 117, 110, 100, 115, 61] }))
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
                       #[GoLean.GoCore.Stmt.assign
                           (GoLean.GoCore.Assignee.var "$res0")
                           (GoLean.GoCore.Expr.var "t"),
                         GoLean.GoCore.Stmt.assign
                           (GoLean.GoCore.Assignee.var "$res1")
                           (GoLean.GoCore.Expr.var "comp"),
                         GoLean.GoCore.Stmt.assign
                           (GoLean.GoCore.Assignee.var "$res2")
                           (GoLean.GoCore.Expr.var "floorOK"),
                         GoLean.GoCore.Stmt.returnStmt]]
                    [[("stuckPropose", GoLean.Loc.base { id := 6071 }),
                      ("round", GoLean.Loc.base { id := 6070 }),
                      ("t", GoLean.Loc.base { id := 110 })],
                     [("$res2", GoLean.Loc.base { id := 108 }),
                      ("$res1", GoLean.Loc.base { id := 107 }),
                      ("$res0", GoLean.Loc.base { id := 106 })]]
                    (GoLean.GoCore.Machine.Cont.frame
                      [(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "t"]),
                       (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "comp"]),
                       (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "floorOK"])]
                      [[("floorOK", GoLean.Loc.base { id := 105 }),
                        ("comp", GoLean.Loc.base { id := 104 }),
                        ("t", GoLean.Loc.base { id := 103 })],
                       [("$res4", GoLean.Loc.base { id := 102 }),
                        ("$res3", GoLean.Loc.base { id := 101 }),
                        ("$res2", GoLean.Loc.base { id := 100 }),
                        ("$res1", GoLean.Loc.base { id := 99 }),
                        ("$res0", GoLean.Loc.base { id := 98 })]]
                      [GoLean.Loc.base { id := 106 },
                       GoLean.Loc.base { id := 107 },
                       GoLean.Loc.base { id := 108 }]
                      []
                      (GoLean.GoCore.Machine.Cont.seq
                        [GoLean.GoCore.Stmt.seqn
                           #[GoLean.GoCore.Stmt.assign
                               (GoLean.GoCore.Assignee.var "$res0")
                               (GoLean.GoCore.Expr.fieldGet
                                 (GoLean.GoCore.Expr.deref
                                   (GoLean.GoCore.Expr.var "t")
                                   (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                                 { key := "main.twin" }
                                 "violations"),
                             GoLean.GoCore.Stmt.assign
                               (GoLean.GoCore.Assignee.var "$res1")
                               (GoLean.GoCore.Expr.fieldGet
                                 (GoLean.GoCore.Expr.deref
                                   (GoLean.GoCore.Expr.var "t")
                                   (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                                 { key := "main.twin" }
                                 "claims"),
                             GoLean.GoCore.Stmt.assign
                               (GoLean.GoCore.Assignee.var "$res2")
                               (GoLean.GoCore.Expr.fieldGet
                                 (GoLean.GoCore.Expr.deref
                                   (GoLean.GoCore.Expr.var "t")
                                   (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                                 { key := "main.twin" }
                                 "committed"),
                             GoLean.GoCore.Stmt.assign
                               (GoLean.GoCore.Assignee.var "$res3")
                               (GoLean.GoCore.Expr.var "comp"),
                             GoLean.GoCore.Stmt.assign
                               (GoLean.GoCore.Assignee.var "$res4")
                               (GoLean.GoCore.Expr.var "floorOK"),
                             GoLean.GoCore.Stmt.returnStmt]]
                        [[("floorOK", GoLean.Loc.base { id := 105 }),
                          ("comp", GoLean.Loc.base { id := 104 }),
                          ("t", GoLean.Loc.base { id := 103 })],
                         [("$res4", GoLean.Loc.base { id := 102 }),
                          ("$res3", GoLean.Loc.base { id := 101 }),
                          ("$res2", GoLean.Loc.base { id := 100 }),
                          ("$res1", GoLean.Loc.base { id := 99 }),
                          ("$res0", GoLean.Loc.base { id := 98 })]]
                        (GoLean.GoCore.Machine.Cont.frame
                          []
                          []
                          []
                          []
                          (GoLean.GoCore.Machine.Cont.stop)
                          false))
                      false))))))))))

def rhbCh1 : GoLean.GoCore.Choices := [0, 0, 0, 0]

def rhbNa2 : Nat := 6097

def rhbHeap2 : GoLean.GoCore.Heap :=
  [(GoLean.Loc.base { id := 15 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 57 }) }),
 (GoLean.Loc.base { id := 27 },
  { declaredTy := some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.array
               #[GoLean.GoValue.bool true, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool true,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool true,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool true] }),
 (GoLean.Loc.base { id := 28 },
  { declaredTy := some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.array
               #[GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool false, GoLean.GoValue.bool true,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true] }),
 (GoLean.Loc.base { id := 57 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.HardState" }
               #[("Term", GoLean.GoValue.nil), ("Vote", GoLean.GoValue.nil),
                 ("Commit", GoLean.GoValue.nil)] }),
 (GoLean.Loc.base { id := 110 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 121 }) }),
 (GoLean.Loc.base { id := 121 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twin" }),
    value := GoLean.GoValue.struct
               { key := "main.twin" }
               #[("nodes",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 1764 }), offset := 0, len := 3, cap := 4 }),
                 ("net",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6077 }), offset := 0, len := 1, cap := 1 }),
                 ("live",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6078 }), offset := 0, len := 1, cap := 1 }),
                 ("leaderOf", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 115 }) }),
                 ("byIndex", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 118 }) }),
                 ("claims", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("committed", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("violations", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("pending",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 136 }), offset := 0, len := 2, cap := 4 }),
                 ("driven", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("seq", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.int)),
                 ("trace",
                  GoLean.GoValue.string
                    { bytes := #[91, 99, 104, 111, 105, 99, 101, 45, 100, 114, 105, 118, 101, 110, 93, 10, 99,
                                 97, 109, 112, 97, 105, 103, 110, 49] }),
                 ("halt", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 170 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
    value := GoLean.GoValue.struct
               { key := "main.twinNode" }
               #[("id", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("rn", GoLean.GoValue.addr (GoLean.Loc.base { id := 1742 })),
                 ("st", GoLean.GoValue.addr (GoLean.Loc.base { id := 179 })),
                 ("term", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("commit", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("state", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("lastTrm", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("got", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 167 }) })] }),
 (GoLean.Loc.base { id := 1764 },
  { declaredTy := some (GoLean.GoCore.Ty.array
                    4
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))),
    value := GoLean.GoValue.array
               #[GoLean.GoValue.addr (GoLean.Loc.base { id := 170 }),
                 GoLean.GoValue.addr (GoLean.Loc.base { id := 1770 }),
                 GoLean.GoValue.addr (GoLean.Loc.base { id := 3369 }), GoLean.GoValue.nil] }),
 (GoLean.Loc.base { id := 1770 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
    value := GoLean.GoValue.struct
               { key := "main.twinNode" }
               #[("id", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                 ("rn", GoLean.GoValue.addr (GoLean.Loc.base { id := 3342 })),
                 ("st", GoLean.GoValue.addr (GoLean.Loc.base { id := 1779 })),
                 ("term", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("commit", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("state", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("lastTrm", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("got", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 1767 }) })] }),
 (GoLean.Loc.base { id := 1949 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }),
    value := GoLean.GoValue.struct
               { key := "raft.raftLog" }
               #[("storage",
                  GoLean.GoValue.interface
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }))
                    (GoLean.GoValue.addr (GoLean.Loc.base { id := 1779 }))),
                 ("unstable",
                  GoLean.GoValue.struct
                    { key := "raft.unstable" }
                    #[("snapshot", GoLean.GoValue.nil),
                      ("entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                      ("offset", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                      ("snapshotInProgress", GoLean.GoValue.bool false),
                      ("offsetInProgress", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                      ("logger",
                       GoLean.GoValue.interface
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
                         (GoLean.GoValue.addr (GoLean.Loc.base { id := 97 })))]),
                 ("committed", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("applying", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("logger",
                  GoLean.GoValue.interface
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
                    (GoLean.GoValue.addr (GoLean.Loc.base { id := 97 }))),
                 ("maxApplyingEntsSize", GoLean.GoValue.int 1048576 (GoLean.GoCore.IntKind.uint64)),
                 ("applyingEntsSize", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("applyingEntsPaused", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 1989 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.raft" }),
    value := GoLean.GoValue.struct
               { key := "raft.raft" }
               #[("id", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                 ("Term", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("Vote", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("readStates", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("raftLog", GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 })),
                 ("maxMsgSize", GoLean.GoValue.int 1048576 (GoLean.GoCore.IntKind.uint64)),
                 ("maxUncommittedSize",
                  GoLean.GoValue.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
                 ("trk",
                  GoLean.GoValue.struct
                    { key := "tracker.ProgressTracker" }
                    #[("Config",
                       GoLean.GoValue.struct
                         { key := "tracker.Config" }
                         #[("Voters",
                            GoLean.GoValue.array
                              #[GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 2686 }) },
                                GoLean.GoValue.map { base := none }]),
                           ("AutoLeave", GoLean.GoValue.bool false),
                           ("Learners", GoLean.GoValue.map { base := none }),
                           ("LearnersNext", GoLean.GoValue.map { base := none })]),
                      ("Progress", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 2703 }) }),
                      ("Votes", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 3059 }) }),
                      ("MaxInflight", GoLean.GoValue.int 256 (GoLean.GoCore.IntKind.int)),
                      ("MaxInflightBytes",
                       GoLean.GoValue.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64))]),
                 ("state", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("isLearner", GoLean.GoValue.bool false),
                 ("msgs", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("msgsAfterAppend", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("lead", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("leadTransferee", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("pendingConfIndex", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("disableConfChangeValidation", GoLean.GoValue.bool false),
                 ("uncommittedSize", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("readOnly", GoLean.GoValue.addr (GoLean.Loc.base { id := 3199 })),
                 ("electionElapsed", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("heartbeatElapsed", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("checkQuorum", GoLean.GoValue.bool false), ("preVote", GoLean.GoValue.bool false),
                 ("heartbeatTimeout", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int)),
                 ("electionTimeout", GoLean.GoValue.int 10 (GoLean.GoCore.IntKind.int)),
                 ("randomizedElectionTimeout", GoLean.GoValue.int 10 (GoLean.GoCore.IntKind.int)),
                 ("disableProposalForwarding", GoLean.GoValue.bool false),
                 ("stepDownOnRemoval", GoLean.GoValue.bool false),
                 ("tick",
                  GoLean.GoValue.funcVal
                    { key := "raft.raft.tickElection" }
                    [GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 })]),
                 ("step", GoLean.GoValue.funcVal { key := "raft.stepFollower" } []),
                 ("logger",
                  GoLean.GoValue.interface
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
                    (GoLean.GoValue.addr (GoLean.Loc.base { id := 97 }))),
                 ("pendingReadIndexMessages",
                  GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("traceLogger", GoLean.GoValue.nil)] }),
 (GoLean.Loc.base { id := 3342 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }),
    value := GoLean.GoValue.struct
               { key := "raft.RawNode" }
               #[("raft", GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 })),
                 ("asyncStorageWrites", GoLean.GoValue.bool false),
                 ("prevSoftSt", GoLean.GoValue.addr (GoLean.Loc.base { id := 3344 })),
                 ("prevHardSt", GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 })),
                 ("stepsOnAdvance",
                  GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 })] }),
 (GoLean.Loc.base { id := 3344 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }),
    value := GoLean.GoValue.struct
               { key := "raft.SoftState" }
               #[("Lead", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("RaftState", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64))] }),
 (GoLean.Loc.base { id := 3351 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 3354 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 3357 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 3360 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.HardState" }
               #[("Term", GoLean.GoValue.addr (GoLean.Loc.base { id := 3351 })),
                 ("Vote", GoLean.GoValue.addr (GoLean.Loc.base { id := 3354 })),
                 ("Commit", GoLean.GoValue.addr (GoLean.Loc.base { id := 3357 }))] }),
 (GoLean.Loc.base { id := 3369 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
    value := GoLean.GoValue.struct
               { key := "main.twinNode" }
               #[("id", GoLean.GoValue.int 3 (GoLean.GoCore.IntKind.uint64)),
                 ("rn", GoLean.GoValue.addr (GoLean.Loc.base { id := 4941 })),
                 ("st", GoLean.GoValue.addr (GoLean.Loc.base { id := 3378 })),
                 ("term", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("commit", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("state", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("lastTrm", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("got", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 3366 }) })] }),
 (GoLean.Loc.base { id := 6070 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6072 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6073 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32)),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6074 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6075 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6076 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.Message" }
               #[("Type", GoLean.GoValue.addr (GoLean.Loc.base { id := 6073 })),
                 ("To", GoLean.GoValue.addr (GoLean.Loc.base { id := 6074 })),
                 ("From", GoLean.GoValue.addr (GoLean.Loc.base { id := 6075 })), ("Term", GoLean.GoValue.nil),
                 ("LogTerm", GoLean.GoValue.nil), ("Index", GoLean.GoValue.nil),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Commit", GoLean.GoValue.nil), ("Vote", GoLean.GoValue.nil),
                 ("Snapshot", GoLean.GoValue.nil), ("Reject", GoLean.GoValue.nil),
                 ("RejectHint", GoLean.GoValue.nil),
                 ("Context", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Responses", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 })] }),
 (GoLean.Loc.base { id := 6077 },
  { declaredTy := some (GoLean.GoCore.Ty.array
                    1
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.array #[GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 })] }),
 (GoLean.Loc.base { id := 6078 },
  { declaredTy := some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.array #[GoLean.GoValue.bool true] }),
 (GoLean.Loc.base { id := 6079 },
  { declaredTy := some (GoLean.GoCore.Ty.map
                    (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                    (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 6080 }) } }),
 (GoLean.Loc.base { id := 6080 },
  { declaredTy := none,
    value := GoLean.GoValue.mapData
               #[(GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int), GoLean.GoValue.bool true)] }),
 (GoLean.Loc.base { id := 6081 },
  { declaredTy := some (GoLean.GoCore.Ty.map
                    (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                    (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 6080 }) } }),
 (GoLean.Loc.base { id := 6082 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.slice
               { base := some (GoLean.Loc.base { id := 6077 }), offset := 0, len := 1, cap := 1 } }),
 (GoLean.Loc.base { id := 6083 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6084 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6085 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6086 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6087 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6088 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6089 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6090 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[] } }),
 (GoLean.Loc.base { id := 6091 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6092 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[] } }),
 (GoLean.Loc.base { id := 6093 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[] } }),
 (GoLean.Loc.base { id := 6094 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6095 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[] } }),
 (GoLean.Loc.base { id := 6096 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[] } })]

def rhbC2 : GoLean.GoCore.Machine.Config :=
  GoLean.GoCore.Machine.Config.next
  (GoLean.GoCore.Machine.Cont.seq
    [GoLean.GoCore.Stmt.block
       #[]
       #[GoLean.GoCore.Stmt.initialization { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
         GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$forFirst") (GoLean.GoCore.Expr.boolLit true),
         GoLean.GoCore.Stmt.while
           (GoLean.GoCore.Expr.boolLit true)
           (GoLean.GoCore.Stmt.block
             #[]
             #[GoLean.GoCore.Stmt.ifThenElse
                 (GoLean.GoCore.Expr.var "$forFirst")
                 (GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.var "$forFirst")
                   (GoLean.GoCore.Expr.boolLit false))
                 (GoLean.GoCore.Stmt.seqn #[]),
               GoLean.GoCore.Stmt.seqn #[],
               GoLean.GoCore.Stmt.ifThenElse
                 (GoLean.GoCore.Expr.greaterCmp
                   (GoLean.GoCore.Expr.var "v")
                   (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64)))
                 (GoLean.GoCore.Stmt.seqn #[])
                 (GoLean.GoCore.Stmt.breakStmt),
               GoLean.GoCore.Stmt.block
                 #[]
                 #[GoLean.GoCore.Stmt.seqn
                     #[GoLean.GoCore.Stmt.assign
                         (GoLean.GoCore.Assignee.var "s")
                         (GoLean.GoCore.Expr.add
                           (GoLean.GoCore.Expr.stringFromRune
                             (GoLean.GoCore.Expr.convert
                               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32))
                               (GoLean.GoCore.Expr.add
                                 (GoLean.GoCore.Expr.intLit 48 (GoLean.GoCore.IntKind.int))
                                 (GoLean.GoCore.Expr.convert
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                                   (GoLean.GoCore.Expr.mod
                                     (GoLean.GoCore.Expr.var "v")
                                     (GoLean.GoCore.Expr.intLit 10 (GoLean.GoCore.IntKind.uint64)))))))
                           (GoLean.GoCore.Expr.var "s"))],
                   GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.var "v")
                     (GoLean.GoCore.Expr.div
                       (GoLean.GoCore.Expr.var "v")
                       (GoLean.GoCore.Expr.intLit 10 (GoLean.GoCore.IntKind.uint64)))]])],
     GoLean.GoCore.Stmt.seqn
       #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "s"),
         GoLean.GoCore.Stmt.returnStmt]]
    [[("s", GoLean.Loc.base { id := 6096 })],
     [("$res0", GoLean.Loc.base { id := 6095 }), ("v", GoLean.Loc.base { id := 6094 })]]
    (GoLean.GoCore.Machine.Cont.frame
      [(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c2254"])]
      [[("$c2254", GoLean.Loc.base { id := 6093 })],
       [("$res0", GoLean.Loc.base { id := 6092 }), ("v", GoLean.Loc.base { id := 6091 })]]
      [GoLean.Loc.base { id := 6095 }]
      []
      (GoLean.GoCore.Machine.Cont.seq
        [GoLean.GoCore.Stmt.seqn
           #[GoLean.GoCore.Stmt.assign (GoLean.GoCore.Assignee.var "$res0") (GoLean.GoCore.Expr.var "$c2254"),
             GoLean.GoCore.Stmt.returnStmt]]
        [[("$c2254", GoLean.Loc.base { id := 6093 })],
         [("$res0", GoLean.Loc.base { id := 6092 }), ("v", GoLean.Loc.base { id := 6091 })]]
        (GoLean.GoCore.Machine.Cont.frame
          [(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "$c2236"])]
          [[("$c2236", GoLean.Loc.base { id := 6090 }),
            ("m", GoLean.Loc.base { id := 6089 }),
            ("picked", GoLean.Loc.base { id := 6087 })],
           [("live", GoLean.Loc.base { id := 6081 }), ("$c2235", GoLean.Loc.base { id := 6079 })],
           [],
           [("$forFirst", GoLean.Loc.base { id := 6072 })],
           [],
           [("stuckPropose", GoLean.Loc.base { id := 6071 }),
            ("round", GoLean.Loc.base { id := 6070 }),
            ("t", GoLean.Loc.base { id := 110 })],
           [("$res2", GoLean.Loc.base { id := 108 }),
            ("$res1", GoLean.Loc.base { id := 107 }),
            ("$res0", GoLean.Loc.base { id := 106 })]]
          [GoLean.Loc.base { id := 6092 }]
          []
          (GoLean.GoCore.Machine.Cont.seq
            [GoLean.GoCore.Stmt.seqn
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
             GoLean.GoCore.Stmt.continueStmt]
            [[("$c2236", GoLean.Loc.base { id := 6090 }),
              ("m", GoLean.Loc.base { id := 6089 }),
              ("picked", GoLean.Loc.base { id := 6087 })],
             [("live", GoLean.Loc.base { id := 6081 }), ("$c2235", GoLean.Loc.base { id := 6079 })],
             [],
             [("$forFirst", GoLean.Loc.base { id := 6072 })],
             [],
             [("stuckPropose", GoLean.Loc.base { id := 6071 }),
              ("round", GoLean.Loc.base { id := 6070 }),
              ("t", GoLean.Loc.base { id := 110 })],
             [("$res2", GoLean.Loc.base { id := 108 }),
              ("$res1", GoLean.Loc.base { id := 107 }),
              ("$res0", GoLean.Loc.base { id := 106 })]]
            (GoLean.GoCore.Machine.Cont.seq
              [GoLean.GoCore.Stmt.seqn
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
                             GoLean.GoCore.Expr.defaultValue
                               (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
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
                                   (GoLean.GoCore.Expr.fieldAddr
                                     (GoLean.GoCore.Expr.var "t")
                                     { key := "main.twin" }
                                     "halt"))
                                 (GoLean.GoCore.Expr.boolLit true)],
                           GoLean.GoCore.Stmt.call
                             #[]
                             { key := "main.twin.say" }
                             #[GoLean.GoCore.Expr.var "t",
                               GoLean.GoCore.Expr.stringLit
                                 { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112,
                                              111, 115, 101, 32, 115, 116, 117, 99, 107, 32, 97, 116, 32, 113,
                                              117, 105, 101, 115, 99, 101, 110, 99, 101, 10] }],
                           GoLean.GoCore.Stmt.breakStmt])
                       (GoLean.GoCore.Stmt.seqn #[]),
                     GoLean.GoCore.Stmt.continueStmt])
                 (GoLean.GoCore.Stmt.seqn #[]),
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.addr
                       (GoLean.GoCore.Expr.fieldAddr
                         (GoLean.GoCore.Expr.var "t")
                         { key := "main.twin" }
                         "halt"))
                     (GoLean.GoCore.Expr.boolLit true)],
               GoLean.GoCore.Stmt.call
                 #[]
                 { key := "main.twin.say" }
                 #[GoLean.GoCore.Expr.var "t",
                   GoLean.GoCore.Expr.stringLit
                     { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101,
                                  110, 116, 32, 119, 105, 116, 104, 111, 117, 116, 32, 83, 52, 10] }],
               GoLean.GoCore.Stmt.breakStmt]
              [[("live", GoLean.Loc.base { id := 6081 }), ("$c2235", GoLean.Loc.base { id := 6079 })],
               [],
               [("$forFirst", GoLean.Loc.base { id := 6072 })],
               [],
               [("stuckPropose", GoLean.Loc.base { id := 6071 }),
                ("round", GoLean.Loc.base { id := 6070 }),
                ("t", GoLean.Loc.base { id := 110 })],
               [("$res2", GoLean.Loc.base { id := 108 }),
                ("$res1", GoLean.Loc.base { id := 107 }),
                ("$res0", GoLean.Loc.base { id := 106 })]]
              (GoLean.GoCore.Machine.Cont.seq
                []
                [[],
                 [("$forFirst", GoLean.Loc.base { id := 6072 })],
                 [],
                 [("stuckPropose", GoLean.Loc.base { id := 6071 }),
                  ("round", GoLean.Loc.base { id := 6070 }),
                  ("t", GoLean.Loc.base { id := 110 })],
                 [("$res2", GoLean.Loc.base { id := 108 }),
                  ("$res1", GoLean.Loc.base { id := 107 }),
                  ("$res0", GoLean.Loc.base { id := 106 })]]
                (GoLean.GoCore.Machine.Cont.loop
                  (GoLean.GoCore.Expr.boolLit true)
                  (GoLean.GoCore.Stmt.block
                    #[]
                    #[GoLean.GoCore.Stmt.ifThenElse
                        (GoLean.GoCore.Expr.var "$forFirst")
                        (GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$forFirst")
                          (GoLean.GoCore.Expr.boolLit false))
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
                              GoLean.GoCore.Stmt.assign
                                (GoLean.GoCore.Assignee.var "live")
                                (GoLean.GoCore.Expr.var "$c2235")],
                          GoLean.GoCore.Stmt.block
                            #[]
                            #[GoLean.GoCore.Stmt.initialization
                                { id := "$rcoll",
                                  typ := GoLean.GoCore.Ty.slice
                                           (GoLean.GoCore.Ty.pointer
                                             (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
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
                              GoLean.GoCore.Stmt.initialization
                                { id := "$rfirst", typ := GoLean.GoCore.Ty.bool },
                              GoLean.GoCore.Stmt.assign
                                (GoLean.GoCore.Assignee.var "$rfirst")
                                (GoLean.GoCore.Expr.boolLit true),
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
                                      (GoLean.GoCore.Expr.atLeastCmp
                                        (GoLean.GoCore.Expr.var "$ridx")
                                        (GoLean.GoCore.Expr.var "$rlen"))
                                      (GoLean.GoCore.Stmt.breakStmt)
                                      (GoLean.GoCore.Stmt.seqn #[]),
                                    GoLean.GoCore.Stmt.initialization
                                      { id := "j", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                                    GoLean.GoCore.Stmt.assign
                                      (GoLean.GoCore.Assignee.var "j")
                                      (GoLean.GoCore.Expr.var "$ridx"),
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
                                (some (GoLean.GoCore.Ty.map
                                   (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                                   (GoLean.GoCore.Ty.bool))))
                              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int)))
                            (GoLean.GoCore.Stmt.block
                              #[]
                              #[GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.initialization
                                      { id := "picked",
                                        typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
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
                                        #[GoLean.GoCore.Stmt.assign
                                            (GoLean.GoCore.Assignee.var "picked")
                                            (GoLean.GoCore.Expr.var "j")],
                                      GoLean.GoCore.Stmt.breakStmt]),
                                GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.initialization
                                      { id := "m",
                                        typ := GoLean.GoCore.Ty.pointer
                                                 (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
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
                                  #[GoLean.GoCore.Stmt.initialization
                                      { id := "$c2236", typ := GoLean.GoCore.Ty.string },
                                    GoLean.GoCore.Stmt.call
                                      #[GoLean.GoCore.Assignee.var "$c2236"]
                                      { key := "itoa" }
                                      #[GoLean.GoCore.Expr.add
                                          (GoLean.GoCore.Expr.var "round")
                                          (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))]],
                                GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.initialization
                                      { id := "$c2237", typ := GoLean.GoCore.Ty.string },
                                    GoLean.GoCore.Stmt.call
                                      #[GoLean.GoCore.Assignee.var "$c2237"]
                                      { key := "itoa" }
                                      #[GoLean.GoCore.Expr.var "picked"]],
                                GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.initialization
                                      { id := "$c2238",
                                        typ := GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" } },
                                    GoLean.GoCore.Stmt.call
                                      #[GoLean.GoCore.Assignee.var "$c2238"]
                                      { key := "raftpb.Message.GetType" }
                                      #[GoLean.GoCore.Expr.var "m"]],
                                GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.initialization
                                      { id := "$c2239", typ := GoLean.GoCore.Ty.string },
                                    GoLean.GoCore.Stmt.call
                                      #[GoLean.GoCore.Assignee.var "$c2239"]
                                      { key := "itoa" }
                                      #[GoLean.GoCore.Expr.convert
                                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                                          (GoLean.GoCore.Expr.var "$c2238")]],
                                GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.initialization
                                      { id := "$c2240",
                                        typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                    GoLean.GoCore.Stmt.call
                                      #[GoLean.GoCore.Assignee.var "$c2240"]
                                      { key := "raftpb.Message.GetTo" }
                                      #[GoLean.GoCore.Expr.var "m"]],
                                GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.initialization
                                      { id := "$c2241", typ := GoLean.GoCore.Ty.string },
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
                                                (GoLean.GoCore.Expr.stringLit
                                                  { bytes := #[32, 112, 105, 99, 107, 35] }))
                                              (GoLean.GoCore.Expr.var "$c2237"))
                                            (GoLean.GoCore.Expr.stringLit
                                              { bytes := #[32, 116, 121, 112, 101] }))
                                          (GoLean.GoCore.Expr.var "$c2239"))
                                        (GoLean.GoCore.Expr.stringLit { bytes := #[45, 62] }))
                                      (GoLean.GoCore.Expr.var "$c2241")],
                                GoLean.GoCore.Stmt.call
                                  #[]
                                  { key := "main.twin.deliverIdx" }
                                  #[GoLean.GoCore.Expr.var "t", GoLean.GoCore.Expr.var "picked"],
                                GoLean.GoCore.Stmt.seqn
                                  #[GoLean.GoCore.Stmt.initialization
                                      { id := "$c2242", typ := GoLean.GoCore.Ty.string },
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
                            #[GoLean.GoCore.Stmt.initialization
                                { id := "$c2243", typ := GoLean.GoCore.Ty.bool },
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
                                  #[GoLean.GoCore.Stmt.initialization
                                      { id := "$c2244", typ := GoLean.GoCore.Ty.string },
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
                                        GoLean.GoCore.Expr.defaultValue
                                          (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
                                GoLean.GoCore.Stmt.call
                                  #[]
                                  { key := "main.twin.say" }
                                  #[GoLean.GoCore.Expr.var "t",
                                    GoLean.GoCore.Expr.stringLit { bytes := #[10] }],
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
                                              (GoLean.GoCore.Expr.fieldAddr
                                                (GoLean.GoCore.Expr.var "t")
                                                { key := "main.twin" }
                                                "halt"))
                                            (GoLean.GoCore.Expr.boolLit true)],
                                      GoLean.GoCore.Stmt.call
                                        #[]
                                        { key := "main.twin.say" }
                                        #[GoLean.GoCore.Expr.var "t",
                                          GoLean.GoCore.Expr.stringLit
                                            { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114,
                                                         111, 112, 111, 115, 101, 32, 115, 116, 117, 99, 107,
                                                         32, 97, 116, 32, 113, 117, 105, 101, 115, 99, 101,
                                                         110, 99, 101, 10] }],
                                      GoLean.GoCore.Stmt.breakStmt])
                                  (GoLean.GoCore.Stmt.seqn #[]),
                                GoLean.GoCore.Stmt.continueStmt])
                            (GoLean.GoCore.Stmt.seqn #[]),
                          GoLean.GoCore.Stmt.seqn
                            #[GoLean.GoCore.Stmt.assign
                                (GoLean.GoCore.Assignee.addr
                                  (GoLean.GoCore.Expr.fieldAddr
                                    (GoLean.GoCore.Expr.var "t")
                                    { key := "main.twin" }
                                    "halt"))
                                (GoLean.GoCore.Expr.boolLit true)],
                          GoLean.GoCore.Stmt.call
                            #[]
                            { key := "main.twin.say" }
                            #[GoLean.GoCore.Expr.var "t",
                              GoLean.GoCore.Expr.stringLit
                                { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101,
                                             115, 99, 101, 110, 116, 32, 119, 105, 116, 104, 111, 117, 116,
                                             32, 83, 52, 10] }],
                          GoLean.GoCore.Stmt.breakStmt]])
                  [[("$forFirst", GoLean.Loc.base { id := 6072 })],
                   [],
                   [("stuckPropose", GoLean.Loc.base { id := 6071 }),
                    ("round", GoLean.Loc.base { id := 6070 }),
                    ("t", GoLean.Loc.base { id := 110 })],
                   [("$res2", GoLean.Loc.base { id := 108 }),
                    ("$res1", GoLean.Loc.base { id := 107 }),
                    ("$res0", GoLean.Loc.base { id := 106 })]]
                  (GoLean.GoCore.Machine.Cont.seq
                    []
                    [[("$forFirst", GoLean.Loc.base { id := 6072 })],
                     [],
                     [("stuckPropose", GoLean.Loc.base { id := 6071 }),
                      ("round", GoLean.Loc.base { id := 6070 }),
                      ("t", GoLean.Loc.base { id := 110 })],
                     [("$res2", GoLean.Loc.base { id := 108 }),
                      ("$res1", GoLean.Loc.base { id := 107 }),
                      ("$res0", GoLean.Loc.base { id := 106 })]]
                    (GoLean.GoCore.Machine.Cont.seq
                      []
                      [[],
                       [("stuckPropose", GoLean.Loc.base { id := 6071 }),
                        ("round", GoLean.Loc.base { id := 6070 }),
                        ("t", GoLean.Loc.base { id := 110 })],
                       [("$res2", GoLean.Loc.base { id := 108 }),
                        ("$res1", GoLean.Loc.base { id := 107 }),
                        ("$res0", GoLean.Loc.base { id := 106 })]]
                      (GoLean.GoCore.Machine.Cont.seq
                        [GoLean.GoCore.Stmt.seqn
                           #[GoLean.GoCore.Stmt.initialization
                               { id := "comp", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                             GoLean.GoCore.Stmt.assign
                               (GoLean.GoCore.Assignee.var "comp")
                               (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))],
                         GoLean.GoCore.Stmt.seqn
                           #[GoLean.GoCore.Stmt.initialization
                               { id := "$c2245", typ := GoLean.GoCore.Ty.bool },
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
                                     (GoLean.GoCore.Expr.deref
                                       (GoLean.GoCore.Expr.var "t")
                                       (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                                     { key := "main.twin" }
                                     "pending")
                                   (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
                                 (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                             (GoLean.GoCore.Expr.not
                               (GoLean.GoCore.Expr.fieldGet
                                 (GoLean.GoCore.Expr.deref
                                   (GoLean.GoCore.Expr.var "t")
                                   (GoLean.GoCore.Ty.defined { key := "main.twin" }))
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
                           #[GoLean.GoCore.Stmt.initialization
                               { id := "floorOK", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                             GoLean.GoCore.Stmt.assign
                               (GoLean.GoCore.Assignee.var "floorOK")
                               (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))],
                         GoLean.GoCore.Stmt.ifThenElse
                           (GoLean.GoCore.Expr.or
                             (GoLean.GoCore.Expr.lessCmp
                               (GoLean.GoCore.Expr.fieldGet
                                 (GoLean.GoCore.Expr.deref
                                   (GoLean.GoCore.Expr.var "t")
                                   (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                                 { key := "main.twin" }
                                 "claims")
                               (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))
                             (GoLean.GoCore.Expr.lessCmp
                               (GoLean.GoCore.Expr.fieldGet
                                 (GoLean.GoCore.Expr.deref
                                   (GoLean.GoCore.Expr.var "t")
                                   (GoLean.GoCore.Ty.defined { key := "main.twin" }))
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
                           #[GoLean.GoCore.Stmt.initialization
                               { id := "$c2246", typ := GoLean.GoCore.Ty.string },
                             GoLean.GoCore.Stmt.call
                               #[GoLean.GoCore.Assignee.var "$c2246"]
                               { key := "itoa" }
                               #[GoLean.GoCore.Expr.fieldGet
                                   (GoLean.GoCore.Expr.deref
                                     (GoLean.GoCore.Expr.var "t")
                                     (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                                   { key := "main.twin" }
                                   "violations"]],
                         GoLean.GoCore.Stmt.seqn
                           #[GoLean.GoCore.Stmt.initialization
                               { id := "$c2247", typ := GoLean.GoCore.Ty.string },
                             GoLean.GoCore.Stmt.call
                               #[GoLean.GoCore.Assignee.var "$c2247"]
                               { key := "itoa" }
                               #[GoLean.GoCore.Expr.fieldGet
                                   (GoLean.GoCore.Expr.deref
                                     (GoLean.GoCore.Expr.var "t")
                                     (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                                   { key := "main.twin" }
                                   "claims"]],
                         GoLean.GoCore.Stmt.seqn
                           #[GoLean.GoCore.Stmt.initialization
                               { id := "$c2248", typ := GoLean.GoCore.Ty.string },
                             GoLean.GoCore.Stmt.call
                               #[GoLean.GoCore.Assignee.var "$c2248"]
                               { key := "itoa" }
                               #[GoLean.GoCore.Expr.fieldGet
                                   (GoLean.GoCore.Expr.deref
                                     (GoLean.GoCore.Expr.var "t")
                                     (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                                   { key := "main.twin" }
                                   "committed"]],
                         GoLean.GoCore.Stmt.seqn
                           #[GoLean.GoCore.Stmt.initialization
                               { id := "$c2249", typ := GoLean.GoCore.Ty.string },
                             GoLean.GoCore.Stmt.call
                               #[GoLean.GoCore.Assignee.var "$c2249"]
                               { key := "itoa" }
                               #[GoLean.GoCore.Expr.var "comp"]],
                         GoLean.GoCore.Stmt.seqn
                           #[GoLean.GoCore.Stmt.initialization
                               { id := "$c2250", typ := GoLean.GoCore.Ty.string },
                             GoLean.GoCore.Stmt.call
                               #[GoLean.GoCore.Assignee.var "$c2250"]
                               { key := "itoa" }
                               #[GoLean.GoCore.Expr.var "floorOK"]],
                         GoLean.GoCore.Stmt.seqn
                           #[GoLean.GoCore.Stmt.initialization
                               { id := "$c2251", typ := GoLean.GoCore.Ty.string },
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
                                                     (GoLean.GoCore.Expr.stringLit
                                                       { bytes := #[101, 110, 100, 32, 118, 105, 111, 108,
                                                                    61] })
                                                     (GoLean.GoCore.Expr.var "$c2246"))
                                                   (GoLean.GoCore.Expr.stringLit
                                                     { bytes := #[32, 99, 108, 97, 105, 109, 115, 61] }))
                                                 (GoLean.GoCore.Expr.var "$c2247"))
                                               (GoLean.GoCore.Expr.stringLit
                                                 { bytes := #[32, 99, 111, 109, 109, 105, 116, 116, 101, 100,
                                                              61] }))
                                             (GoLean.GoCore.Expr.var "$c2248"))
                                           (GoLean.GoCore.Expr.stringLit
                                             { bytes := #[32, 99, 111, 109, 112, 108, 101, 116, 101, 61] }))
                                         (GoLean.GoCore.Expr.var "$c2249"))
                                       (GoLean.GoCore.Expr.stringLit
                                         { bytes := #[32, 102, 108, 111, 111, 114, 61] }))
                                     (GoLean.GoCore.Expr.var "$c2250"))
                                   (GoLean.GoCore.Expr.stringLit
                                     { bytes := #[32, 114, 111, 117, 110, 100, 115, 61] }))
                                 (GoLean.GoCore.Expr.var "$c2251"))
                               (GoLean.GoCore.Expr.stringLit { bytes := #[10] })],
                         GoLean.GoCore.Stmt.seqn
                           #[GoLean.GoCore.Stmt.initialization
                               { id := "$c2252", typ := GoLean.GoCore.Ty.string },
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
                           #[GoLean.GoCore.Stmt.assign
                               (GoLean.GoCore.Assignee.var "$res0")
                               (GoLean.GoCore.Expr.var "t"),
                             GoLean.GoCore.Stmt.assign
                               (GoLean.GoCore.Assignee.var "$res1")
                               (GoLean.GoCore.Expr.var "comp"),
                             GoLean.GoCore.Stmt.assign
                               (GoLean.GoCore.Assignee.var "$res2")
                               (GoLean.GoCore.Expr.var "floorOK"),
                             GoLean.GoCore.Stmt.returnStmt]]
                        [[("stuckPropose", GoLean.Loc.base { id := 6071 }),
                          ("round", GoLean.Loc.base { id := 6070 }),
                          ("t", GoLean.Loc.base { id := 110 })],
                         [("$res2", GoLean.Loc.base { id := 108 }),
                          ("$res1", GoLean.Loc.base { id := 107 }),
                          ("$res0", GoLean.Loc.base { id := 106 })]]
                        (GoLean.GoCore.Machine.Cont.frame
                          [(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "t"]),
                           (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "comp"]),
                           (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "floorOK"])]
                          [[("floorOK", GoLean.Loc.base { id := 105 }),
                            ("comp", GoLean.Loc.base { id := 104 }),
                            ("t", GoLean.Loc.base { id := 103 })],
                           [("$res4", GoLean.Loc.base { id := 102 }),
                            ("$res3", GoLean.Loc.base { id := 101 }),
                            ("$res2", GoLean.Loc.base { id := 100 }),
                            ("$res1", GoLean.Loc.base { id := 99 }),
                            ("$res0", GoLean.Loc.base { id := 98 })]]
                          [GoLean.Loc.base { id := 106 },
                           GoLean.Loc.base { id := 107 },
                           GoLean.Loc.base { id := 108 }]
                          []
                          (GoLean.GoCore.Machine.Cont.seq
                            [GoLean.GoCore.Stmt.seqn
                               #[GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res0")
                                   (GoLean.GoCore.Expr.fieldGet
                                     (GoLean.GoCore.Expr.deref
                                       (GoLean.GoCore.Expr.var "t")
                                       (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                                     { key := "main.twin" }
                                     "violations"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res1")
                                   (GoLean.GoCore.Expr.fieldGet
                                     (GoLean.GoCore.Expr.deref
                                       (GoLean.GoCore.Expr.var "t")
                                       (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                                     { key := "main.twin" }
                                     "claims"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res2")
                                   (GoLean.GoCore.Expr.fieldGet
                                     (GoLean.GoCore.Expr.deref
                                       (GoLean.GoCore.Expr.var "t")
                                       (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                                     { key := "main.twin" }
                                     "committed"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res3")
                                   (GoLean.GoCore.Expr.var "comp"),
                                 GoLean.GoCore.Stmt.assign
                                   (GoLean.GoCore.Assignee.var "$res4")
                                   (GoLean.GoCore.Expr.var "floorOK"),
                                 GoLean.GoCore.Stmt.returnStmt]]
                            [[("floorOK", GoLean.Loc.base { id := 105 }),
                              ("comp", GoLean.Loc.base { id := 104 }),
                              ("t", GoLean.Loc.base { id := 103 })],
                             [("$res4", GoLean.Loc.base { id := 102 }),
                              ("$res3", GoLean.Loc.base { id := 101 }),
                              ("$res2", GoLean.Loc.base { id := 100 }),
                              ("$res1", GoLean.Loc.base { id := 99 }),
                              ("$res0", GoLean.Loc.base { id := 98 })]]
                            (GoLean.GoCore.Machine.Cont.frame
                              []
                              []
                              []
                              []
                              (GoLean.GoCore.Machine.Cont.stop)
                              false))
                          false))))))))
          false))
      false))

def rhbCh2 : GoLean.GoCore.Choices := [0, 0, 0]

def rhbNa3 : Nat := 6669

def rhbHeap3 : GoLean.GoCore.Heap :=
  [(GoLean.Loc.base { id := 15 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 57 }) }),
 (GoLean.Loc.base { id := 27 },
  { declaredTy := some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.array
               #[GoLean.GoValue.bool true, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool true,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool true,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool true] }),
 (GoLean.Loc.base { id := 28 },
  { declaredTy := some (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.array
               #[GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool false, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true, GoLean.GoValue.bool false,
                 GoLean.GoValue.bool true, GoLean.GoValue.bool false, GoLean.GoValue.bool true,
                 GoLean.GoValue.bool false, GoLean.GoValue.bool true] }),
 (GoLean.Loc.base { id := 57 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.HardState" }
               #[("Term", GoLean.GoValue.nil), ("Vote", GoLean.GoValue.nil),
                 ("Commit", GoLean.GoValue.nil)] }),
 (GoLean.Loc.base { id := 110 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 121 }) }),
 (GoLean.Loc.base { id := 121 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twin" }),
    value := GoLean.GoValue.struct
               { key := "main.twin" }
               #[("nodes",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 1764 }), offset := 0, len := 3, cap := 4 }),
                 ("net",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6462 }), offset := 0, len := 2, cap := 2 }),
                 ("live",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6466 }), offset := 0, len := 2, cap := 2 }),
                 ("leaderOf", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 115 }) }),
                 ("byIndex", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 118 }) }),
                 ("claims", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("committed", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("violations", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("pending",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 136 }), offset := 0, len := 2, cap := 4 }),
                 ("driven", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("seq", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.int)),
                 ("trace",
                  GoLean.GoValue.string
                    { bytes := #[91, 99, 104, 111, 105, 99, 101, 45, 100, 114, 105, 118, 101, 110, 93, 10, 99,
                                 97, 109, 112, 97, 105, 103, 110, 49, 114, 49, 32, 112, 105, 99, 107, 35, 48,
                                 32, 116, 121, 112, 101, 56, 45, 62, 50, 32, 32, 124, 67, 49, 47, 49, 47, 48,
                                 32, 70, 48, 47, 48, 47, 48, 32, 70, 48, 47, 48, 47, 48, 32, 110, 101, 116,
                                 61, 49, 10] }),
                 ("halt", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 170 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
    value := GoLean.GoValue.struct
               { key := "main.twinNode" }
               #[("id", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("rn", GoLean.GoValue.addr (GoLean.Loc.base { id := 1742 })),
                 ("st", GoLean.GoValue.addr (GoLean.Loc.base { id := 179 })),
                 ("term", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("commit", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("state", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("lastTrm", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("got", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 167 }) })] }),
 (GoLean.Loc.base { id := 1764 },
  { declaredTy := some (GoLean.GoCore.Ty.array
                    4
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))),
    value := GoLean.GoValue.array
               #[GoLean.GoValue.addr (GoLean.Loc.base { id := 170 }),
                 GoLean.GoValue.addr (GoLean.Loc.base { id := 1770 }),
                 GoLean.GoValue.addr (GoLean.Loc.base { id := 3369 }), GoLean.GoValue.nil] }),
 (GoLean.Loc.base { id := 1770 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
    value := GoLean.GoValue.struct
               { key := "main.twinNode" }
               #[("id", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                 ("rn", GoLean.GoValue.addr (GoLean.Loc.base { id := 3342 })),
                 ("st", GoLean.GoValue.addr (GoLean.Loc.base { id := 1779 })),
                 ("term", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("commit", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("state", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("lastTrm", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("got", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 1767 }) })] }),
 (GoLean.Loc.base { id := 1949 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }),
    value := GoLean.GoValue.struct
               { key := "raft.raftLog" }
               #[("storage",
                  GoLean.GoValue.interface
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }))
                    (GoLean.GoValue.addr (GoLean.Loc.base { id := 1779 }))),
                 ("unstable",
                  GoLean.GoValue.struct
                    { key := "raft.unstable" }
                    #[("snapshot", GoLean.GoValue.nil),
                      ("entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                      ("offset", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                      ("snapshotInProgress", GoLean.GoValue.bool false),
                      ("offsetInProgress", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                      ("logger",
                       GoLean.GoValue.interface
                         (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
                         (GoLean.GoValue.addr (GoLean.Loc.base { id := 97 })))]),
                 ("committed", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("applying", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("logger",
                  GoLean.GoValue.interface
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
                    (GoLean.GoValue.addr (GoLean.Loc.base { id := 97 }))),
                 ("maxApplyingEntsSize", GoLean.GoValue.int 1048576 (GoLean.GoCore.IntKind.uint64)),
                 ("applyingEntsSize", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("applyingEntsPaused", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 1989 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.raft" }),
    value := GoLean.GoValue.struct
               { key := "raft.raft" }
               #[("id", GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64)),
                 ("Term", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("Vote", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("readStates", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("raftLog", GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 })),
                 ("maxMsgSize", GoLean.GoValue.int 1048576 (GoLean.GoCore.IntKind.uint64)),
                 ("maxUncommittedSize",
                  GoLean.GoValue.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
                 ("trk",
                  GoLean.GoValue.struct
                    { key := "tracker.ProgressTracker" }
                    #[("Config",
                       GoLean.GoValue.struct
                         { key := "tracker.Config" }
                         #[("Voters",
                            GoLean.GoValue.array
                              #[GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 2686 }) },
                                GoLean.GoValue.map { base := none }]),
                           ("AutoLeave", GoLean.GoValue.bool false),
                           ("Learners", GoLean.GoValue.map { base := none }),
                           ("LearnersNext", GoLean.GoValue.map { base := none })]),
                      ("Progress", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 2703 }) }),
                      ("Votes", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 3059 }) }),
                      ("MaxInflight", GoLean.GoValue.int 256 (GoLean.GoCore.IntKind.int)),
                      ("MaxInflightBytes",
                       GoLean.GoValue.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64))]),
                 ("state", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("isLearner", GoLean.GoValue.bool false),
                 ("msgs", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("msgsAfterAppend", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("lead", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("leadTransferee", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("pendingConfIndex", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("disableConfChangeValidation", GoLean.GoValue.bool false),
                 ("uncommittedSize", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("readOnly", GoLean.GoValue.addr (GoLean.Loc.base { id := 3199 })),
                 ("electionElapsed", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("heartbeatElapsed", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int)),
                 ("checkQuorum", GoLean.GoValue.bool false), ("preVote", GoLean.GoValue.bool false),
                 ("heartbeatTimeout", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int)),
                 ("electionTimeout", GoLean.GoValue.int 10 (GoLean.GoCore.IntKind.int)),
                 ("randomizedElectionTimeout", GoLean.GoValue.int 10 (GoLean.GoCore.IntKind.int)),
                 ("disableProposalForwarding", GoLean.GoValue.bool false),
                 ("stepDownOnRemoval", GoLean.GoValue.bool false),
                 ("tick",
                  GoLean.GoValue.funcVal
                    { key := "raft.raft.tickElection" }
                    [GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 })]),
                 ("step", GoLean.GoValue.funcVal { key := "raft.stepFollower" } []),
                 ("logger",
                  GoLean.GoValue.interface
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
                    (GoLean.GoValue.addr (GoLean.Loc.base { id := 97 }))),
                 ("pendingReadIndexMessages",
                  GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("traceLogger", GoLean.GoValue.nil)] }),
 (GoLean.Loc.base { id := 3342 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }),
    value := GoLean.GoValue.struct
               { key := "raft.RawNode" }
               #[("raft", GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 })),
                 ("asyncStorageWrites", GoLean.GoValue.bool false),
                 ("prevSoftSt", GoLean.GoValue.addr (GoLean.Loc.base { id := 6323 })),
                 ("prevHardSt", GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 })),
                 ("stepsOnAdvance",
                  GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 })] }),
 (GoLean.Loc.base { id := 3344 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }),
    value := GoLean.GoValue.struct
               { key := "raft.SoftState" }
               #[("Lead", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("RaftState", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64))] }),
 (GoLean.Loc.base { id := 3351 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 3354 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 3357 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 3360 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.HardState" }
               #[("Term", GoLean.GoValue.addr (GoLean.Loc.base { id := 3351 })),
                 ("Vote", GoLean.GoValue.addr (GoLean.Loc.base { id := 3354 })),
                 ("Commit", GoLean.GoValue.addr (GoLean.Loc.base { id := 3357 }))] }),
 (GoLean.Loc.base { id := 3369 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
    value := GoLean.GoValue.struct
               { key := "main.twinNode" }
               #[("id", GoLean.GoValue.int 3 (GoLean.GoCore.IntKind.uint64)),
                 ("rn", GoLean.GoValue.addr (GoLean.Loc.base { id := 4941 })),
                 ("st", GoLean.GoValue.addr (GoLean.Loc.base { id := 3378 })),
                 ("term", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("commit", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("state", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("applied", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("lastTrm", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64)),
                 ("got", GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 3366 }) })] }),
 (GoLean.Loc.base { id := 6070 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6072 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6073 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32)),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6074 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6075 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6076 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.Message" }
               #[("Type", GoLean.GoValue.addr (GoLean.Loc.base { id := 6073 })),
                 ("To", GoLean.GoValue.addr (GoLean.Loc.base { id := 6074 })),
                 ("From", GoLean.GoValue.addr (GoLean.Loc.base { id := 6075 })), ("Term", GoLean.GoValue.nil),
                 ("LogTerm", GoLean.GoValue.nil), ("Index", GoLean.GoValue.nil),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Commit", GoLean.GoValue.nil), ("Vote", GoLean.GoValue.nil),
                 ("Snapshot", GoLean.GoValue.nil), ("Reject", GoLean.GoValue.nil),
                 ("RejectHint", GoLean.GoValue.nil),
                 ("Context", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Responses", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 })] }),
 (GoLean.Loc.base { id := 6077 },
  { declaredTy := some (GoLean.GoCore.Ty.array
                    1
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.array #[GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 })] }),
 (GoLean.Loc.base { id := 6078 },
  { declaredTy := some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.array #[GoLean.GoValue.bool false] }),
 (GoLean.Loc.base { id := 6079 },
  { declaredTy := some (GoLean.GoCore.Ty.map
                    (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                    (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 6080 }) } }),
 (GoLean.Loc.base { id := 6080 },
  { declaredTy := none,
    value := GoLean.GoValue.mapData
               #[(GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int), GoLean.GoValue.bool true)] }),
 (GoLean.Loc.base { id := 6081 },
  { declaredTy := some (GoLean.GoCore.Ty.map
                    (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                    (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.map { base := some (GoLean.Loc.base { id := 6080 }) } }),
 (GoLean.Loc.base { id := 6082 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.slice
               { base := some (GoLean.Loc.base { id := 6077 }), offset := 0, len := 1, cap := 1 } }),
 (GoLean.Loc.base { id := 6083 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6084 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6085 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6086 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6087 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6088 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6089 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6090 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6091 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6092 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6093 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6094 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6095 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6096 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6097 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6098 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6099 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6100 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6101 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6102 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6103 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6104 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6105 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6106 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6107 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[56] } }),
 (GoLean.Loc.base { id := 6108 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6109 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[56] } }),
 (GoLean.Loc.base { id := 6110 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[56] } }),
 (GoLean.Loc.base { id := 6111 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6112 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[56] } }),
 (GoLean.Loc.base { id := 6113 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[56] } }),
 (GoLean.Loc.base { id := 6114 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6115 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6116 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6117 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6118 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[50] } }),
 (GoLean.Loc.base { id := 6119 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6120 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[50] } }),
 (GoLean.Loc.base { id := 6121 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[50] } }),
 (GoLean.Loc.base { id := 6122 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6123 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 121 }) }),
 (GoLean.Loc.base { id := 6124 },
  { declaredTy := some (GoLean.GoCore.Ty.string),
    value := GoLean.GoValue.string
               { bytes := #[114, 49, 32, 112, 105, 99, 107, 35, 48, 32, 116, 121, 112, 101, 56, 45, 62,
                            50] } }),
 (GoLean.Loc.base { id := 6125 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 121 }) }),
 (GoLean.Loc.base { id := 6126 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6127 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6128 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6129 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6130 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6131 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1770 }) }),
 (GoLean.Loc.base { id := 6132 },
  { declaredTy := some (GoLean.GoCore.Ty.interface { key := "error" }), value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6133 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3342 }) }),
 (GoLean.Loc.base { id := 6134 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6135 },
  { declaredTy := some (GoLean.GoCore.Ty.interface { key := "error" }), value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6136 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6137 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6138 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6139 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6140 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6141 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6142 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6143 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6144 },
  { declaredTy := some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.slice
               { base := some (GoLean.Loc.base { id := 27 }), offset := 0, len := 23, cap := 23 } }),
 (GoLean.Loc.base { id := 6145 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6146 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6147 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6148 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6149 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6150 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6151 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6152 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6153 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6154 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6155 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6156 },
  { declaredTy := some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.slice
               { base := some (GoLean.Loc.base { id := 28 }), offset := 0, len := 23, cap := 23 } }),
 (GoLean.Loc.base { id := 6157 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6158 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6159 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6160 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6161 },
  { declaredTy := some (GoLean.GoCore.Ty.interface { key := "error" }), value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6162 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6163 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6164 },
  { declaredTy := some (GoLean.GoCore.Ty.interface { key := "error" }), value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6165 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6166 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6167 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6168 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6169 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6170 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6171 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6172 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6173 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6174 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6175 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6176 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 4 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6177 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6178 },
  { declaredTy := some (GoLean.GoCore.Ty.interface { key := "error" }), value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6179 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6180 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6181 },
  { declaredTy := some (GoLean.GoCore.Ty.interface { key := "error" }), value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6182 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6183 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6184 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6185 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 8 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6186 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6187 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6188 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6189 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6190 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6191 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6192 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6193 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6194 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6195 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6196 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 }) }),
 (GoLean.Loc.base { id := 6197 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6198 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6202 }) }),
 (GoLean.Loc.base { id := 6199 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6200 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6202 }) }),
 (GoLean.Loc.base { id := 6201 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6202 }) }),
 (GoLean.Loc.base { id := 6202 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6203 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6202 }) }),
 (GoLean.Loc.base { id := 6204 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6202 }) }),
 (GoLean.Loc.base { id := 6205 },
  { declaredTy := some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint8))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6206 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }) }),
 (GoLean.Loc.base { id := 6207 },
  { declaredTy := some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint8))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6208 },
  { declaredTy := some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint8))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6209 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6210 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.Message" }
               #[("Type", GoLean.GoValue.addr (GoLean.Loc.base { id := 6202 })),
                 ("To", GoLean.GoValue.addr (GoLean.Loc.base { id := 6075 })),
                 ("From", GoLean.GoValue.addr (GoLean.Loc.base { id := 6217 })),
                 ("Term", GoLean.GoValue.addr (GoLean.Loc.base { id := 6244 })),
                 ("LogTerm", GoLean.GoValue.nil), ("Index", GoLean.GoValue.nil),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Commit", GoLean.GoValue.nil), ("Vote", GoLean.GoValue.nil),
                 ("Snapshot", GoLean.GoValue.nil), ("Reject", GoLean.GoValue.nil),
                 ("RejectHint", GoLean.GoValue.nil),
                 ("Context", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Responses", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 })] }),
 (GoLean.Loc.base { id := 6211 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6212 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6213 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6214 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6215 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6216 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6217 }) }),
 (GoLean.Loc.base { id := 6217 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6218 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6219 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6220 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6221 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6222 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6223 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6224 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6225 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6226 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6227 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6228 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6229 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6230 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6231 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6232 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6233 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6234 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6235 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6236 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6237 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6238 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6239 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6240 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6241 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6242 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6243 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6244 }) }),
 (GoLean.Loc.base { id := 6244 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6245 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6246 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6247 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6248 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6249 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6250 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6251 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6252 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6253 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6254 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6255 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.MessageType" }),
    value := GoLean.GoValue.int 9 (GoLean.GoCore.IntKind.int32) }),
 (GoLean.Loc.base { id := 6256 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6257 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6258 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6259 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.slice
               { base := some (GoLean.Loc.base { id := 6260 }), offset := 0, len := 1, cap := 1 } }),
 (GoLean.Loc.base { id := 6260 },
  { declaredTy := some (GoLean.GoCore.Ty.array
                    1
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.array #[GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 })] }),
 (GoLean.Loc.base { id := 6261 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.slice
               { base := some (GoLean.Loc.base { id := 6262 }), offset := 0, len := 1, cap := 4 } }),
 (GoLean.Loc.base { id := 6262 },
  { declaredTy := some (GoLean.GoCore.Ty.array
                    4
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.array
               #[GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }), GoLean.GoValue.nil, GoLean.GoValue.nil,
                 GoLean.GoValue.nil] }),
 (GoLean.Loc.base { id := 6263 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6264 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6265 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6266 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 121 }) }),
 (GoLean.Loc.base { id := 6267 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1770 }) }),
 (GoLean.Loc.base { id := 6268 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6269 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6270 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6271 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6272 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3342 }) }),
 (GoLean.Loc.base { id := 6273 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6274 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6275 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }),
    value := GoLean.GoValue.struct
               { key := "raft.SoftState" }
               #[("Lead", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("RaftState", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64))] }),
 (GoLean.Loc.base { id := 6276 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6277 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }),
    value := GoLean.GoValue.struct
               { key := "raft.SoftState" }
               #[("Lead", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("RaftState", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64))] }),
 (GoLean.Loc.base { id := 6278 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6279 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6275 }) }),
 (GoLean.Loc.base { id := 6280 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3344 }) }),
 (GoLean.Loc.base { id := 6281 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6282 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.Ready" }),
    value := GoLean.GoValue.struct
               { key := "raft.Ready" }
               #[("SoftState", GoLean.GoValue.addr (GoLean.Loc.base { id := 6323 })),
                 ("HardState", GoLean.GoValue.nil),
                 ("ReadStates", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Snapshot", GoLean.GoValue.nil),
                 ("CommittedEntries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Messages",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6262 }), offset := 0, len := 1, cap := 4 }),
                 ("MustSync", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 6283 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3342 }) }),
 (GoLean.Loc.base { id := 6284 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.Ready" }),
    value := GoLean.GoValue.struct
               { key := "raft.Ready" }
               #[("SoftState", GoLean.GoValue.addr (GoLean.Loc.base { id := 6323 })),
                 ("HardState", GoLean.GoValue.nil),
                 ("ReadStates", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Snapshot", GoLean.GoValue.nil),
                 ("CommittedEntries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Messages",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6262 }), offset := 0, len := 1, cap := 4 }),
                 ("MustSync", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 6285 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.Ready" }),
    value := GoLean.GoValue.struct
               { key := "raft.Ready" }
               #[("SoftState", GoLean.GoValue.addr (GoLean.Loc.base { id := 6323 })),
                 ("HardState", GoLean.GoValue.nil),
                 ("ReadStates", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Snapshot", GoLean.GoValue.nil),
                 ("CommittedEntries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Messages",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6262 }), offset := 0, len := 1, cap := 4 }),
                 ("MustSync", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 6286 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3342 }) }),
 (GoLean.Loc.base { id := 6287 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.Ready" }),
    value := GoLean.GoValue.struct
               { key := "raft.Ready" }
               #[("SoftState", GoLean.GoValue.addr (GoLean.Loc.base { id := 6323 })),
                 ("HardState", GoLean.GoValue.nil),
                 ("ReadStates", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Snapshot", GoLean.GoValue.nil),
                 ("CommittedEntries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Messages",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6262 }), offset := 0, len := 1, cap := 4 }),
                 ("MustSync", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 6288 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6289 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6290 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 }) }),
 (GoLean.Loc.base { id := 6291 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6292 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6293 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" })),
    value := GoLean.GoValue.addr
               (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable") }),
 (GoLean.Loc.base { id := 6294 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6295 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6296 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6297 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6298 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3342 }) }),
 (GoLean.Loc.base { id := 6299 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6300 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6301 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 }) }),
 (GoLean.Loc.base { id := 6302 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6303 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6304 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6305 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 }) }),
 (GoLean.Loc.base { id := 6306 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6307 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6308 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 }) }),
 (GoLean.Loc.base { id := 6309 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6310 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6311 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6312 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6313 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6314 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6315 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.Ready" }),
    value := GoLean.GoValue.struct
               { key := "raft.Ready" }
               #[("SoftState", GoLean.GoValue.addr (GoLean.Loc.base { id := 6323 })),
                 ("HardState", GoLean.GoValue.nil),
                 ("ReadStates", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Snapshot", GoLean.GoValue.nil),
                 ("CommittedEntries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Messages",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6262 }), offset := 0, len := 1, cap := 4 }),
                 ("MustSync", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 6316 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }),
    value := GoLean.GoValue.struct
               { key := "raft.SoftState" }
               #[("Lead", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("RaftState", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64))] }),
 (GoLean.Loc.base { id := 6317 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6318 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }),
    value := GoLean.GoValue.struct
               { key := "raft.SoftState" }
               #[("Lead", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("RaftState", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64))] }),
 (GoLean.Loc.base { id := 6319 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6320 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6316 }) }),
 (GoLean.Loc.base { id := 6321 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3344 }) }),
 (GoLean.Loc.base { id := 6322 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6323 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }),
    value := GoLean.GoValue.struct
               { key := "raft.SoftState" }
               #[("Lead", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("RaftState", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64))] }),
 (GoLean.Loc.base { id := 6324 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6337 }) }),
 (GoLean.Loc.base { id := 6325 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6326 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6337 }) }),
 (GoLean.Loc.base { id := 6327 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6328 }) }),
 (GoLean.Loc.base { id := 6328 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6329 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6328 }) }),
 (GoLean.Loc.base { id := 6330 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6331 }) }),
 (GoLean.Loc.base { id := 6331 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6332 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6331 }) }),
 (GoLean.Loc.base { id := 6333 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6334 }) }),
 (GoLean.Loc.base { id := 6334 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6335 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6334 }) }),
 (GoLean.Loc.base { id := 6336 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6337 }) }),
 (GoLean.Loc.base { id := 6337 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.HardState" }
               #[("Term", GoLean.GoValue.addr (GoLean.Loc.base { id := 6328 })),
                 ("Vote", GoLean.GoValue.addr (GoLean.Loc.base { id := 6331 })),
                 ("Commit", GoLean.GoValue.addr (GoLean.Loc.base { id := 6334 }))] }),
 (GoLean.Loc.base { id := 6338 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6339 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6337 }) }),
 (GoLean.Loc.base { id := 6340 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 }) }),
 (GoLean.Loc.base { id := 6341 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6342 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6343 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6337 }) }),
 (GoLean.Loc.base { id := 6344 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6345 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6346 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 }) }),
 (GoLean.Loc.base { id := 6347 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6348 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6349 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6350 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6337 }) }),
 (GoLean.Loc.base { id := 6351 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6352 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6353 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 }) }),
 (GoLean.Loc.base { id := 6354 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6355 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6356 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6357 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6337 }) }),
 (GoLean.Loc.base { id := 6358 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6359 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6360 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 }) }),
 (GoLean.Loc.base { id := 6361 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6362 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6363 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 }) }),
 (GoLean.Loc.base { id := 6364 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6365 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6366 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" })),
    value := GoLean.GoValue.addr
               (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable") }),
 (GoLean.Loc.base { id := 6367 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6368 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6381 }) }),
 (GoLean.Loc.base { id := 6369 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6370 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6381 }) }),
 (GoLean.Loc.base { id := 6371 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6372 }) }),
 (GoLean.Loc.base { id := 6372 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6373 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6372 }) }),
 (GoLean.Loc.base { id := 6374 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6375 }) }),
 (GoLean.Loc.base { id := 6375 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6376 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6375 }) }),
 (GoLean.Loc.base { id := 6377 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6378 }) }),
 (GoLean.Loc.base { id := 6378 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6379 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6378 }) }),
 (GoLean.Loc.base { id := 6380 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6381 }) }),
 (GoLean.Loc.base { id := 6381 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.HardState" }
               #[("Term", GoLean.GoValue.addr (GoLean.Loc.base { id := 6372 })),
                 ("Vote", GoLean.GoValue.addr (GoLean.Loc.base { id := 6375 })),
                 ("Commit", GoLean.GoValue.addr (GoLean.Loc.base { id := 6378 }))] }),
 (GoLean.Loc.base { id := 6382 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6383 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6381 }) }),
 (GoLean.Loc.base { id := 6384 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 }) }),
 (GoLean.Loc.base { id := 6385 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6386 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6387 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6388 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6389 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6381 }) }),
 (GoLean.Loc.base { id := 6390 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6391 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6392 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 }) }),
 (GoLean.Loc.base { id := 6393 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6394 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6395 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6396 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6381 }) }),
 (GoLean.Loc.base { id := 6397 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6398 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6399 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 }) }),
 (GoLean.Loc.base { id := 6400 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6401 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6402 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6403 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6404 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6405 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3342 }) }),
 (GoLean.Loc.base { id := 6406 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.Ready" }),
    value := GoLean.GoValue.struct
               { key := "raft.Ready" }
               #[("SoftState", GoLean.GoValue.addr (GoLean.Loc.base { id := 6323 })),
                 ("HardState", GoLean.GoValue.nil),
                 ("ReadStates", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Snapshot", GoLean.GoValue.nil),
                 ("CommittedEntries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Messages",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6262 }), offset := 0, len := 1, cap := 4 }),
                 ("MustSync", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 6407 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6408 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6409 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6410 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6411 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6412 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6413 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6414 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6415 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6416 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6417 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.Ready" }),
    value := GoLean.GoValue.struct
               { key := "raft.Ready" }
               #[("SoftState", GoLean.GoValue.addr (GoLean.Loc.base { id := 6323 })),
                 ("HardState", GoLean.GoValue.nil),
                 ("ReadStates", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Snapshot", GoLean.GoValue.nil),
                 ("CommittedEntries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Messages",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6262 }), offset := 0, len := 1, cap := 4 }),
                 ("MustSync", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 6418 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6419 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6420 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 }) }),
 (GoLean.Loc.base { id := 6421 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6422 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6423 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6424 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6425 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6426 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer
                    (GoLean.GoCore.Ty.defined { key := "raftpb.SnapshotMetadata" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6427 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6428 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer
                    (GoLean.GoCore.Ty.defined { key := "raftpb.SnapshotMetadata" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6429 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6430 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer
                    (GoLean.GoCore.Ty.defined { key := "raftpb.SnapshotMetadata" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6431 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6432 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6433 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.Ready" }),
    value := GoLean.GoValue.struct
               { key := "raft.Ready" }
               #[("SoftState", GoLean.GoValue.addr (GoLean.Loc.base { id := 6323 })),
                 ("HardState", GoLean.GoValue.nil),
                 ("ReadStates", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Snapshot", GoLean.GoValue.nil),
                 ("CommittedEntries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Messages",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6262 }), offset := 0, len := 1, cap := 4 }),
                 ("MustSync", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 6434 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6435 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6436 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.Ready" }),
    value := GoLean.GoValue.struct
               { key := "raft.Ready" }
               #[("SoftState", GoLean.GoValue.addr (GoLean.Loc.base { id := 6323 })),
                 ("HardState", GoLean.GoValue.nil),
                 ("ReadStates", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Snapshot", GoLean.GoValue.nil),
                 ("CommittedEntries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Messages",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6262 }), offset := 0, len := 1, cap := 4 }),
                 ("MustSync", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 6437 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6438 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 }) }),
 (GoLean.Loc.base { id := 6439 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" })),
    value := GoLean.GoValue.addr
               (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable") }),
 (GoLean.Loc.base { id := 6440 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6441 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6442 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6443 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6444 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6445 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6446 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6447 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6448 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer
                    (GoLean.GoCore.Ty.defined { key := "raftpb.SnapshotMetadata" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6449 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6450 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer
                    (GoLean.GoCore.Ty.defined { key := "raftpb.SnapshotMetadata" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6451 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6452 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer
                    (GoLean.GoCore.Ty.defined { key := "raftpb.SnapshotMetadata" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6453 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6454 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.slice
               { base := some (GoLean.Loc.base { id := 6262 }), offset := 0, len := 1, cap := 4 } }),
 (GoLean.Loc.base { id := 6455 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6456 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6457 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6458 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 }) }),
 (GoLean.Loc.base { id := 6459 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.slice
               { base := some (GoLean.Loc.base { id := 6460 }), offset := 0, len := 1, cap := 1 } }),
 (GoLean.Loc.base { id := 6460 },
  { declaredTy := some (GoLean.GoCore.Ty.array
                    1
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.array #[GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 })] }),
 (GoLean.Loc.base { id := 6461 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.slice
               { base := some (GoLean.Loc.base { id := 6462 }), offset := 0, len := 2, cap := 2 } }),
 (GoLean.Loc.base { id := 6462 },
  { declaredTy := some (GoLean.GoCore.Ty.array
                    2
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.array
               #[GoLean.GoValue.addr (GoLean.Loc.base { id := 6076 }),
                 GoLean.GoValue.addr (GoLean.Loc.base { id := 6210 })] }),
 (GoLean.Loc.base { id := 6463 },
  { declaredTy := some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.slice
               { base := some (GoLean.Loc.base { id := 6464 }), offset := 0, len := 1, cap := 1 } }),
 (GoLean.Loc.base { id := 6464 },
  { declaredTy := some (GoLean.GoCore.Ty.array 1 (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.array #[GoLean.GoValue.bool true] }),
 (GoLean.Loc.base { id := 6465 },
  { declaredTy := some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.slice
               { base := some (GoLean.Loc.base { id := 6466 }), offset := 0, len := 2, cap := 2 } }),
 (GoLean.Loc.base { id := 6466 },
  { declaredTy := some (GoLean.GoCore.Ty.array 2 (GoLean.GoCore.Ty.bool)),
    value := GoLean.GoValue.array #[GoLean.GoValue.bool false, GoLean.GoValue.bool true] }),
 (GoLean.Loc.base { id := 6467 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6468 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6469 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6470 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6471 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3342 }) }),
 (GoLean.Loc.base { id := 6472 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.Ready" }),
    value := GoLean.GoValue.struct
               { key := "raft.Ready" }
               #[("SoftState", GoLean.GoValue.addr (GoLean.Loc.base { id := 6323 })),
                 ("HardState", GoLean.GoValue.nil),
                 ("ReadStates", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Entries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Snapshot", GoLean.GoValue.nil),
                 ("CommittedEntries", GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 }),
                 ("Messages",
                  GoLean.GoValue.slice
                    { base := some (GoLean.Loc.base { id := 6262 }), offset := 0, len := 1, cap := 4 }),
                 ("MustSync", GoLean.GoValue.bool false)] }),
 (GoLean.Loc.base { id := 6473 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6474 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6475 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6476 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6477 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6478 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3342 }) }),
 (GoLean.Loc.base { id := 6479 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6480 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6481 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }),
    value := GoLean.GoValue.struct
               { key := "raft.SoftState" }
               #[("Lead", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("RaftState", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64))] }),
 (GoLean.Loc.base { id := 6482 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6483 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }),
    value := GoLean.GoValue.struct
               { key := "raft.SoftState" }
               #[("Lead", GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64)),
                 ("RaftState", GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64))] }),
 (GoLean.Loc.base { id := 6484 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6485 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6481 }) }),
 (GoLean.Loc.base { id := 6486 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.SoftState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6323 }) }),
 (GoLean.Loc.base { id := 6487 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6488 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6501 }) }),
 (GoLean.Loc.base { id := 6489 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raft" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1989 }) }),
 (GoLean.Loc.base { id := 6490 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6501 }) }),
 (GoLean.Loc.base { id := 6491 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6492 }) }),
 (GoLean.Loc.base { id := 6492 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6493 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6492 }) }),
 (GoLean.Loc.base { id := 6494 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6495 }) }),
 (GoLean.Loc.base { id := 6495 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6496 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6495 }) }),
 (GoLean.Loc.base { id := 6497 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6498 }) }),
 (GoLean.Loc.base { id := 6498 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6499 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6498 }) }),
 (GoLean.Loc.base { id := 6500 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6501 }) }),
 (GoLean.Loc.base { id := 6501 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
    value := GoLean.GoValue.struct
               { key := "raftpb.HardState" }
               #[("Term", GoLean.GoValue.addr (GoLean.Loc.base { id := 6492 })),
                 ("Vote", GoLean.GoValue.addr (GoLean.Loc.base { id := 6495 })),
                 ("Commit", GoLean.GoValue.addr (GoLean.Loc.base { id := 6498 }))] }),
 (GoLean.Loc.base { id := 6502 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6503 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6501 }) }),
 (GoLean.Loc.base { id := 6504 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6505 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6506 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6507 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6501 }) }),
 (GoLean.Loc.base { id := 6508 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 57 }) }),
 (GoLean.Loc.base { id := 6509 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6510 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6511 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6501 }) }),
 (GoLean.Loc.base { id := 6512 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6513 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6514 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 57 }) }),
 (GoLean.Loc.base { id := 6515 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6516 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6517 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6518 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6501 }) }),
 (GoLean.Loc.base { id := 6519 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6520 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6521 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 57 }) }),
 (GoLean.Loc.base { id := 6522 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6523 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6524 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6525 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6501 }) }),
 (GoLean.Loc.base { id := 6526 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6527 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6528 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 57 }) }),
 (GoLean.Loc.base { id := 6529 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6530 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6531 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6532 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6501 }) }),
 (GoLean.Loc.base { id := 6533 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 }) }),
 (GoLean.Loc.base { id := 6534 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6535 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6536 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6501 }) }),
 (GoLean.Loc.base { id := 6537 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6538 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6539 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 }) }),
 (GoLean.Loc.base { id := 6540 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6541 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6542 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6543 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6501 }) }),
 (GoLean.Loc.base { id := 6544 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6545 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6546 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 }) }),
 (GoLean.Loc.base { id := 6547 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6548 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6549 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6550 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 6501 }) }),
 (GoLean.Loc.base { id := 6551 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6552 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6553 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3360 }) }),
 (GoLean.Loc.base { id := 6554 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6555 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6556 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 }) }),
 (GoLean.Loc.base { id := 6557 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6558 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6559 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" })),
    value := GoLean.GoValue.addr
               (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable") }),
 (GoLean.Loc.base { id := 6560 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" })),
    value := GoLean.GoValue.nil }),
 (GoLean.Loc.base { id := 6561 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6562 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 }) }),
 (GoLean.Loc.base { id := 6563 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6564 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6565 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 }) }),
 (GoLean.Loc.base { id := 6566 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6567 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6568 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.unstable" })),
    value := GoLean.GoValue.addr
               (GoLean.Loc.field (GoLean.Loc.base { id := 1949 }) { key := "raft.raftLog" } "unstable") }),
 (GoLean.Loc.base { id := 6569 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }))),
    value := GoLean.GoValue.slice { base := none, offset := 0, len := 0, cap := 0 } }),
 (GoLean.Loc.base { id := 6570 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6571 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6572 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6573 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.RawNode" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3342 }) }),
 (GoLean.Loc.base { id := 6574 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6575 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6576 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 }) }),
 (GoLean.Loc.base { id := 6577 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6578 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6579 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6580 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 }) }),
 (GoLean.Loc.base { id := 6581 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6582 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6583 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.raftLog" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1949 }) }),
 (GoLean.Loc.base { id := 6584 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool true }),
 (GoLean.Loc.base { id := 6585 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6586 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6587 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6588 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6589 },
  { declaredTy := some (GoLean.GoCore.Ty.string),
    value := GoLean.GoValue.string
               { bytes := #[32, 124, 67, 49, 47, 49, 47, 48, 32, 70, 48, 47, 48, 47, 48, 32, 70, 48, 47, 48,
                            47, 48, 32, 110, 101, 116, 61, 49] } }),
 (GoLean.Loc.base { id := 6590 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 121 }) }),
 (GoLean.Loc.base { id := 6591 },
  { declaredTy := some (GoLean.GoCore.Ty.string),
    value := GoLean.GoValue.string
               { bytes := #[32, 124, 67, 49, 47, 49, 47, 48, 32, 70, 48, 47, 48, 47, 48, 32, 70, 48, 47, 48,
                            47, 48, 32, 110, 101, 116, 61, 49] } }),
 (GoLean.Loc.base { id := 6592 },
  { declaredTy := some (GoLean.GoCore.Ty.string),
    value := GoLean.GoValue.string
               { bytes := #[32, 124, 67, 49, 47, 49, 47, 48, 32, 70, 48, 47, 48, 47, 48, 32, 70, 48, 47, 48,
                            47, 48, 32] } }),
 (GoLean.Loc.base { id := 6593 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" }))),
    value := GoLean.GoValue.slice
               { base := some (GoLean.Loc.base { id := 1764 }), offset := 0, len := 3, cap := 4 } }),
 (GoLean.Loc.base { id := 6594 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 3 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6595 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 3 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6596 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6597 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 170 }) }),
 (GoLean.Loc.base { id := 6598 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[67] } }),
 (GoLean.Loc.base { id := 6599 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.StateType" }),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6600 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[67] } }),
 (GoLean.Loc.base { id := 6601 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.StateType" }),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6602 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6603 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6604 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6605 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6606 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6607 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6608 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6609 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6610 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6611 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6612 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6613 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6614 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6615 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6616 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6617 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 1770 }) }),
 (GoLean.Loc.base { id := 6618 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[70] } }),
 (GoLean.Loc.base { id := 6619 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.StateType" }),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6620 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[70] } }),
 (GoLean.Loc.base { id := 6621 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.StateType" }),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6622 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6623 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6624 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6625 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6626 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6627 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6628 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6629 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6630 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6631 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6632 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6633 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 3369 }) }),
 (GoLean.Loc.base { id := 6634 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[70] } }),
 (GoLean.Loc.base { id := 6635 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.StateType" }),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6636 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[70] } }),
 (GoLean.Loc.base { id := 6637 },
  { declaredTy := some (GoLean.GoCore.Ty.defined { key := "raft.StateType" }),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6638 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6639 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6640 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6641 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6642 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6643 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6644 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6645 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6646 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6647 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6648 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[48] } }),
 (GoLean.Loc.base { id := 6649 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6650 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 121 }) }),
 (GoLean.Loc.base { id := 6651 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6652 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6653 },
  { declaredTy := some (GoLean.GoCore.Ty.slice
                    (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }))),
    value := GoLean.GoValue.slice
               { base := some (GoLean.Loc.base { id := 6462 }), offset := 0, len := 2, cap := 2 } }),
 (GoLean.Loc.base { id := 6654 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6655 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 2 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6656 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6657 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6658 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6659 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6660 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
    value := GoLean.GoValue.int 1 (GoLean.GoCore.IntKind.int) }),
 (GoLean.Loc.base { id := 6661 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6662 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6663 },
  { declaredTy := some (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
    value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.uint64) }),
 (GoLean.Loc.base { id := 6664 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6665 },
  { declaredTy := some (GoLean.GoCore.Ty.string), value := GoLean.GoValue.string { bytes := #[49] } }),
 (GoLean.Loc.base { id := 6666 },
  { declaredTy := some (GoLean.GoCore.Ty.bool), value := GoLean.GoValue.bool false }),
 (GoLean.Loc.base { id := 6667 },
  { declaredTy := some (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twin" })),
    value := GoLean.GoValue.addr (GoLean.Loc.base { id := 121 }) }),
 (GoLean.Loc.base { id := 6668 },
  { declaredTy := some (GoLean.GoCore.Ty.string),
    value := GoLean.GoValue.string
               { bytes := #[32, 32, 124, 67, 49, 47, 49, 47, 48, 32, 70, 48, 47, 48, 47, 48, 32, 70, 48, 47,
                            48, 47, 48, 32, 110, 101, 116, 61, 49, 10] } }),
 (GoLean.Loc.base { id := 6071 },
  { declaredTy := none, value := GoLean.GoValue.int 0 (GoLean.GoCore.IntKind.int) })]

-- final config: verified equal to rhbC0 (self-returning)
def rhbCF : GoLean.GoCore.Machine.Config :=
  GoLean.GoCore.Machine.Config.exec
  (GoLean.GoCore.Stmt.ifThenElse
    (GoLean.GoCore.Expr.lessCmp
      (GoLean.GoCore.Expr.var "round")
      (GoLean.GoCore.Expr.intLit 400 (GoLean.GoCore.IntKind.int)))
    (GoLean.GoCore.Stmt.seqn #[])
    (GoLean.GoCore.Stmt.breakStmt))
  [[],
   [("$forFirst", GoLean.Loc.base { id := 6072 })],
   [],
   [("stuckPropose", GoLean.Loc.base { id := 6071 }),
    ("round", GoLean.Loc.base { id := 6070 }),
    ("t", GoLean.Loc.base { id := 110 })],
   [("$res2", GoLean.Loc.base { id := 108 }),
    ("$res1", GoLean.Loc.base { id := 107 }),
    ("$res0", GoLean.Loc.base { id := 106 })]]
  (GoLean.GoCore.Machine.Cont.seq
    [GoLean.GoCore.Stmt.block
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
             GoLean.GoCore.Stmt.assign
               (GoLean.GoCore.Assignee.var "$rfirst")
               (GoLean.GoCore.Expr.boolLit true),
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
                     (GoLean.GoCore.Expr.atLeastCmp
                       (GoLean.GoCore.Expr.var "$ridx")
                       (GoLean.GoCore.Expr.var "$rlen"))
                     (GoLean.GoCore.Stmt.breakStmt)
                     (GoLean.GoCore.Stmt.seqn #[]),
                   GoLean.GoCore.Stmt.initialization
                     { id := "j", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                   GoLean.GoCore.Stmt.assign
                     (GoLean.GoCore.Assignee.var "j")
                     (GoLean.GoCore.Expr.var "$ridx"),
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
               (some (GoLean.GoCore.Ty.map
                  (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                  (GoLean.GoCore.Ty.bool))))
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
                       #[GoLean.GoCore.Stmt.assign
                           (GoLean.GoCore.Assignee.var "picked")
                           (GoLean.GoCore.Expr.var "j")],
                     GoLean.GoCore.Stmt.breakStmt]),
               GoLean.GoCore.Stmt.seqn
                 #[GoLean.GoCore.Stmt.initialization
                     { id := "m",
                       typ := GoLean.GoCore.Ty.pointer
                                (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
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
                             (GoLean.GoCore.Expr.fieldAddr
                               (GoLean.GoCore.Expr.var "t")
                               { key := "main.twin" }
                               "halt"))
                           (GoLean.GoCore.Expr.boolLit true)],
                     GoLean.GoCore.Stmt.call
                       #[]
                       { key := "main.twin.say" }
                       #[GoLean.GoCore.Expr.var "t",
                         GoLean.GoCore.Expr.stringLit
                           { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112, 111,
                                        115, 101, 32, 115, 116, 117, 99, 107, 32, 97, 116, 32, 113, 117, 105,
                                        101, 115, 99, 101, 110, 99, 101, 10] }],
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
               { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101, 110,
                            116, 32, 119, 105, 116, 104, 111, 117, 116, 32, 83, 52, 10] }],
         GoLean.GoCore.Stmt.breakStmt]]
    [[],
     [("$forFirst", GoLean.Loc.base { id := 6072 })],
     [],
     [("stuckPropose", GoLean.Loc.base { id := 6071 }),
      ("round", GoLean.Loc.base { id := 6070 }),
      ("t", GoLean.Loc.base { id := 110 })],
     [("$res2", GoLean.Loc.base { id := 108 }),
      ("$res1", GoLean.Loc.base { id := 107 }),
      ("$res0", GoLean.Loc.base { id := 106 })]]
    (GoLean.GoCore.Machine.Cont.loop
      (GoLean.GoCore.Expr.boolLit true)
      (GoLean.GoCore.Stmt.block
        #[]
        #[GoLean.GoCore.Stmt.ifThenElse
            (GoLean.GoCore.Expr.var "$forFirst")
            (GoLean.GoCore.Stmt.assign
              (GoLean.GoCore.Assignee.var "$forFirst")
              (GoLean.GoCore.Expr.boolLit false))
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
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "live")
                    (GoLean.GoCore.Expr.var "$c2235")],
              GoLean.GoCore.Stmt.block
                #[]
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$rcoll",
                      typ := GoLean.GoCore.Ty.slice
                               (GoLean.GoCore.Ty.pointer
                                 (GoLean.GoCore.Ty.defined { key := "raftpb.Message" })) },
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
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$rfirst")
                    (GoLean.GoCore.Expr.boolLit true),
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
                          (GoLean.GoCore.Expr.atLeastCmp
                            (GoLean.GoCore.Expr.var "$ridx")
                            (GoLean.GoCore.Expr.var "$rlen"))
                          (GoLean.GoCore.Stmt.breakStmt)
                          (GoLean.GoCore.Stmt.seqn #[]),
                        GoLean.GoCore.Stmt.initialization
                          { id := "j", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "j")
                          (GoLean.GoCore.Expr.var "$ridx"),
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
                    (some (GoLean.GoCore.Ty.map
                       (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))
                       (GoLean.GoCore.Ty.bool))))
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
                            #[GoLean.GoCore.Stmt.assign
                                (GoLean.GoCore.Assignee.var "picked")
                                (GoLean.GoCore.Expr.var "j")],
                          GoLean.GoCore.Stmt.breakStmt]),
                    GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "m",
                            typ := GoLean.GoCore.Ty.pointer
                                     (GoLean.GoCore.Ty.defined { key := "raftpb.Message" }) },
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
                            GoLean.GoCore.Expr.defaultValue
                              (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int))]],
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
                                  (GoLean.GoCore.Expr.fieldAddr
                                    (GoLean.GoCore.Expr.var "t")
                                    { key := "main.twin" }
                                    "halt"))
                                (GoLean.GoCore.Expr.boolLit true)],
                          GoLean.GoCore.Stmt.call
                            #[]
                            { key := "main.twin.say" }
                            #[GoLean.GoCore.Expr.var "t",
                              GoLean.GoCore.Expr.stringLit
                                { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 112, 114, 111, 112,
                                             111, 115, 101, 32, 115, 116, 117, 99, 107, 32, 97, 116, 32, 113,
                                             117, 105, 101, 115, 99, 101, 110, 99, 101, 10] }],
                          GoLean.GoCore.Stmt.breakStmt])
                      (GoLean.GoCore.Stmt.seqn #[]),
                    GoLean.GoCore.Stmt.continueStmt])
                (GoLean.GoCore.Stmt.seqn #[]),
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.addr
                      (GoLean.GoCore.Expr.fieldAddr
                        (GoLean.GoCore.Expr.var "t")
                        { key := "main.twin" }
                        "halt"))
                    (GoLean.GoCore.Expr.boolLit true)],
              GoLean.GoCore.Stmt.call
                #[]
                { key := "main.twin.say" }
                #[GoLean.GoCore.Expr.var "t",
                  GoLean.GoCore.Expr.stringLit
                    { bytes := #[33, 100, 114, 105, 118, 101, 114, 58, 32, 113, 117, 105, 101, 115, 99, 101,
                                 110, 116, 32, 119, 105, 116, 104, 111, 117, 116, 32, 83, 52, 10] }],
              GoLean.GoCore.Stmt.breakStmt]])
      [[("$forFirst", GoLean.Loc.base { id := 6072 })],
       [],
       [("stuckPropose", GoLean.Loc.base { id := 6071 }),
        ("round", GoLean.Loc.base { id := 6070 }),
        ("t", GoLean.Loc.base { id := 110 })],
       [("$res2", GoLean.Loc.base { id := 108 }),
        ("$res1", GoLean.Loc.base { id := 107 }),
        ("$res0", GoLean.Loc.base { id := 106 })]]
      (GoLean.GoCore.Machine.Cont.seq
        []
        [[("$forFirst", GoLean.Loc.base { id := 6072 })],
         [],
         [("stuckPropose", GoLean.Loc.base { id := 6071 }),
          ("round", GoLean.Loc.base { id := 6070 }),
          ("t", GoLean.Loc.base { id := 110 })],
         [("$res2", GoLean.Loc.base { id := 108 }),
          ("$res1", GoLean.Loc.base { id := 107 }),
          ("$res0", GoLean.Loc.base { id := 106 })]]
        (GoLean.GoCore.Machine.Cont.seq
          []
          [[],
           [("stuckPropose", GoLean.Loc.base { id := 6071 }),
            ("round", GoLean.Loc.base { id := 6070 }),
            ("t", GoLean.Loc.base { id := 110 })],
           [("$res2", GoLean.Loc.base { id := 108 }),
            ("$res1", GoLean.Loc.base { id := 107 }),
            ("$res0", GoLean.Loc.base { id := 106 })]]
          (GoLean.GoCore.Machine.Cont.seq
            [GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.initialization
                   { id := "comp", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
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
                         (GoLean.GoCore.Expr.deref
                           (GoLean.GoCore.Expr.var "t")
                           (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                         { key := "main.twin" }
                         "pending")
                       (some (GoLean.GoCore.Ty.slice (GoLean.GoCore.Ty.string))))
                     (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.int))))
                 (GoLean.GoCore.Expr.not
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "t")
                       (GoLean.GoCore.Ty.defined { key := "main.twin" }))
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
               #[GoLean.GoCore.Stmt.initialization
                   { id := "floorOK", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int) },
                 GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.var "floorOK")
                   (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int))],
             GoLean.GoCore.Stmt.ifThenElse
               (GoLean.GoCore.Expr.or
                 (GoLean.GoCore.Expr.lessCmp
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "t")
                       (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                     { key := "main.twin" }
                     "claims")
                   (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.int)))
                 (GoLean.GoCore.Expr.lessCmp
                   (GoLean.GoCore.Expr.fieldGet
                     (GoLean.GoCore.Expr.deref
                       (GoLean.GoCore.Expr.var "t")
                       (GoLean.GoCore.Ty.defined { key := "main.twin" }))
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
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "t")
                         (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                       { key := "main.twin" }
                       "violations"]],
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.initialization { id := "$c2247", typ := GoLean.GoCore.Ty.string },
                 GoLean.GoCore.Stmt.call
                   #[GoLean.GoCore.Assignee.var "$c2247"]
                   { key := "itoa" }
                   #[GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "t")
                         (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                       { key := "main.twin" }
                       "claims"]],
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.initialization { id := "$c2248", typ := GoLean.GoCore.Ty.string },
                 GoLean.GoCore.Stmt.call
                   #[GoLean.GoCore.Assignee.var "$c2248"]
                   { key := "itoa" }
                   #[GoLean.GoCore.Expr.fieldGet
                       (GoLean.GoCore.Expr.deref
                         (GoLean.GoCore.Expr.var "t")
                         (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                       { key := "main.twin" }
                       "committed"]],
             GoLean.GoCore.Stmt.seqn
               #[GoLean.GoCore.Stmt.initialization { id := "$c2249", typ := GoLean.GoCore.Ty.string },
                 GoLean.GoCore.Stmt.call
                   #[GoLean.GoCore.Assignee.var "$c2249"]
                   { key := "itoa" }
                   #[GoLean.GoCore.Expr.var "comp"]],
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
                                         (GoLean.GoCore.Expr.stringLit
                                           { bytes := #[101, 110, 100, 32, 118, 105, 111, 108, 61] })
                                         (GoLean.GoCore.Expr.var "$c2246"))
                                       (GoLean.GoCore.Expr.stringLit
                                         { bytes := #[32, 99, 108, 97, 105, 109, 115, 61] }))
                                     (GoLean.GoCore.Expr.var "$c2247"))
                                   (GoLean.GoCore.Expr.stringLit
                                     { bytes := #[32, 99, 111, 109, 109, 105, 116, 116, 101, 100, 61] }))
                                 (GoLean.GoCore.Expr.var "$c2248"))
                               (GoLean.GoCore.Expr.stringLit
                                 { bytes := #[32, 99, 111, 109, 112, 108, 101, 116, 101, 61] }))
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
                 GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.var "$res1")
                   (GoLean.GoCore.Expr.var "comp"),
                 GoLean.GoCore.Stmt.assign
                   (GoLean.GoCore.Assignee.var "$res2")
                   (GoLean.GoCore.Expr.var "floorOK"),
                 GoLean.GoCore.Stmt.returnStmt]]
            [[("stuckPropose", GoLean.Loc.base { id := 6071 }),
              ("round", GoLean.Loc.base { id := 6070 }),
              ("t", GoLean.Loc.base { id := 110 })],
             [("$res2", GoLean.Loc.base { id := 108 }),
              ("$res1", GoLean.Loc.base { id := 107 }),
              ("$res0", GoLean.Loc.base { id := 106 })]]
            (GoLean.GoCore.Machine.Cont.frame
              [(GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "t"]),
               (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "comp"]),
               (GoLean.GoCore.Machine.TargetShape.chain [], [GoLean.GoCore.Expr.ref "floorOK"])]
              [[("floorOK", GoLean.Loc.base { id := 105 }),
                ("comp", GoLean.Loc.base { id := 104 }),
                ("t", GoLean.Loc.base { id := 103 })],
               [("$res4", GoLean.Loc.base { id := 102 }),
                ("$res3", GoLean.Loc.base { id := 101 }),
                ("$res2", GoLean.Loc.base { id := 100 }),
                ("$res1", GoLean.Loc.base { id := 99 }),
                ("$res0", GoLean.Loc.base { id := 98 })]]
              [GoLean.Loc.base { id := 106 }, GoLean.Loc.base { id := 107 }, GoLean.Loc.base { id := 108 }]
              []
              (GoLean.GoCore.Machine.Cont.seq
                [GoLean.GoCore.Stmt.seqn
                   #[GoLean.GoCore.Stmt.assign
                       (GoLean.GoCore.Assignee.var "$res0")
                       (GoLean.GoCore.Expr.fieldGet
                         (GoLean.GoCore.Expr.deref
                           (GoLean.GoCore.Expr.var "t")
                           (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                         { key := "main.twin" }
                         "violations"),
                     GoLean.GoCore.Stmt.assign
                       (GoLean.GoCore.Assignee.var "$res1")
                       (GoLean.GoCore.Expr.fieldGet
                         (GoLean.GoCore.Expr.deref
                           (GoLean.GoCore.Expr.var "t")
                           (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                         { key := "main.twin" }
                         "claims"),
                     GoLean.GoCore.Stmt.assign
                       (GoLean.GoCore.Assignee.var "$res2")
                       (GoLean.GoCore.Expr.fieldGet
                         (GoLean.GoCore.Expr.deref
                           (GoLean.GoCore.Expr.var "t")
                           (GoLean.GoCore.Ty.defined { key := "main.twin" }))
                         { key := "main.twin" }
                         "committed"),
                     GoLean.GoCore.Stmt.assign
                       (GoLean.GoCore.Assignee.var "$res3")
                       (GoLean.GoCore.Expr.var "comp"),
                     GoLean.GoCore.Stmt.assign
                       (GoLean.GoCore.Assignee.var "$res4")
                       (GoLean.GoCore.Expr.var "floorOK"),
                     GoLean.GoCore.Stmt.returnStmt]]
                [[("floorOK", GoLean.Loc.base { id := 105 }),
                  ("comp", GoLean.Loc.base { id := 104 }),
                  ("t", GoLean.Loc.base { id := 103 })],
                 [("$res4", GoLean.Loc.base { id := 102 }),
                  ("$res3", GoLean.Loc.base { id := 101 }),
                  ("$res2", GoLean.Loc.base { id := 100 }),
                  ("$res1", GoLean.Loc.base { id := 99 }),
                  ("$res0", GoLean.Loc.base { id := 98 })]]
                (GoLean.GoCore.Machine.Cont.frame [] [] [] [] (GoLean.GoCore.Machine.Cont.stop) false))
              false))))))

def rhbCh3 : GoLean.GoCore.Choices := []

end GoLean.RaftSeam
