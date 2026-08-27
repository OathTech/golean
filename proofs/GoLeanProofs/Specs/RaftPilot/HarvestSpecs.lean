import GoLeanProofs.Specs.RaftPilot.RaftLogReadSpecs

/-!
# W3 U3.1-B — the harvest engine cluster: first members
(`raft.softState`, `raft.hardState`)

The harvest loop's shell-sync vocabulary (census E6/E8-E12;
`readyWithoutAccept:147/152`, `HasReady:451/454`, `NewRawNode:57/59`
all consume exactly these two): `softState` returns the
`{lead, state}` pair BY VALUE, `hardState` builds the fresh
three-pointer `raftpb.HardState` from `r.Term`/`r.Vote`/
`l.committed`. Their conclusions are the deep-reader agreement facts
the invariant's `shellSync` clause (C2) consumes at Ready
processing: what the harvest writes into the harness shell IS the
deep state/term (U3.2e's consumption site).

**QUANTIFIER AUDIT:** CallSpecR rules discharging ∀-state at the
harvest-loop call sites (∀ σ over the raft-cell footprint family —
26 of the 31 raft fields ride FREE; ∀ plans/env/k; ∀ ch; ∃ n).
No end-theorem quantifier closes here.

**Statement hygiene:** step counts (28/117) private; exports
count-free; addresses canonical-placement constants; the raft/
HardState/SoftState field censuses are the pinned wire's typeDefs.

LINEAGE: as the cluster's siblings (window-split symbolic execution
over computational reflection). No new mechanism.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Spec
open GoLean.Surface

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The raft-cell footprint family
Layout: 31 = the raft cell (raftLog → 32); 32 = the raftLog cell.
The READ fields are int-shape-pinned with free payloads (`Term`,
`Vote`, `lead`, `state`, `raftLog.committed`); the other 26 raft
fields and 8 raftLog fields ride fully free. -/

/-- The raft cell value (field census and order = the pinned wire's
`raft.raft` typeDef; the four read scalars int-shaped, `raftLog`
pinned to the canonical cell 32, everything else free). -/
def raftCellV (tmv vtv ldv stv : Int)
    (idv rsv mmv muv trkv lrnv msgsv msgsAAv ltv pciv dccv ucsv rov
     eev hev cqv pvv htv etv retv dpfv sdrv tickv stepv lgv primv
     tlv : GoValue) : GoValue :=
  .struct ⟨"raft.raft"⟩
    #[("id", idv), ("Term", .int tmv .uint64),
      ("Vote", .int vtv .uint64), ("readStates", rsv),
      ("raftLog", .addr (Loc.base ⟨32⟩)),
      ("maxMsgSize", mmv), ("maxUncommittedSize", muv),
      ("trk", trkv), ("state", .int stv .uint64),
      ("isLearner", lrnv), ("msgs", msgsv),
      ("msgsAfterAppend", msgsAAv), ("lead", .int ldv .uint64),
      ("leadTransferee", ltv), ("pendingConfIndex", pciv),
      ("disableConfChangeValidation", dccv),
      ("uncommittedSize", ucsv), ("readOnly", rov),
      ("electionElapsed", eev), ("heartbeatElapsed", hev),
      ("checkQuorum", cqv), ("preVote", pvv),
      ("heartbeatTimeout", htv), ("electionTimeout", etv),
      ("randomizedElectionTimeout", retv),
      ("disableProposalForwarding", dpfv),
      ("stepDownOnRemoval", sdrv), ("tick", tickv), ("step", stepv),
      ("logger", lgv), ("pendingReadIndexMessages", primv),
      ("traceLogger", tlv)]

/-- The raft-cell family former: raft at 31 (raftLog → 32), the
raftLog cell at 32 (`committed` int-shaped, the rest free via
`logCellV`'s parameters). -/
def rnFam (dty rldty : Option Ty) (tmv vtv ldv stv : Int)
    (idv rsv mmv muv trkv lrnv msgsv msgsAAv ltv pciv dccv ucsv rov
     eev hev cqv pvv htv etv retv dpfv sdrv tickv stepv lgv primv
     tlv : GoValue)
    (rlstv rlentsv rloffv rlsipv rloipv rlulgv : GoValue) (cmv : Int)
    (rlapv rladv rllgv rlmxv rlaszv rlpzv : GoValue) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨31⟩,
        { declaredTy := dty
          value := raftCellV tmv vtv ldv stv idv rsv mmv muv trkv
            lrnv msgsv msgsAAv ltv pciv dccv ucsv rov eev hev cqv pvv
            htv etv retv dpfv sdrv tickv stepv lgv primv tlv }),
       (Loc.base ⟨32⟩,
        { declaredTy := rldty
          value := logCellV rlstv rlentsv rloffv rlsipv rloipv rlulgv
            (.int cmv .uint64) rlapv rladv rllgv rlmxv rlaszv
            rlpzv })]
      nextAddr := 33 }

/-- The raft-cell footprint carrier. -/
def RNPre (dty rldty : Option Ty) (tmv vtv ldv stv : Int)
    (idv rsv mmv muv trkv lrnv msgsv msgsAAv ltv pciv dccv ucsv rov
     eev hev cqv pvv htv etv retv dpfv sdrv tickv stepv lgv primv
     tlv : GoValue)
    (rlstv rlentsv rloffv rlsipv rloipv rlulgv : GoValue) (cmv : Int)
    (rlapv rladv rllgv rlmxv rlaszv rlpzv : GoValue)
    (σm : ExecState) : Prop :=
  σm = rnFam dty rldty tmv vtv ldv stv idv rsv mmv muv trkv lrnv
    msgsv msgsAAv ltv pciv dccv ucsv rov eev hev cqv pvv htv etv retv
    dpfv sdrv tickv stepv lgv primv tlv rlstv rlentsv rloffv rlsipv
    rloipv rlulgv cmv rlapv rladv rllgv rlmxv rlaszv rlpzv

/-- The raft receiver value: `&r` at the canonical anchor. -/
def rnArgV : GoValue := .addr (Loc.base ⟨31⟩)

/-! ## `raft.softState` (census raft.go:521) -/

section SoftState

/-- The softState span (PRIVATE — 28 steps, one window: two field
reads + the struct literal + the result store). -/
private theorem ss_span (dty rldty : Option Ty)
    (tmv vtv ldv stv : Int)
    (idv rsv mmv muv trkv lrnv msgsv msgsAAv ltv pciv dccv ucsv rov
     eev hev cqv pvv htv etv retv dpfv sdrv tickv stepv lgv primv
     tlv : GoValue)
    (rlstv rlentsv rloffv rlsipv rloipv rlulgv : GoValue) (cmv : Int)
    (rlapv rladv rllgv rlmxv rlaszv rlpzv : GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 28
      (rnFam dty rldty tmv vtv ldv stv idv rsv mmv muv trkv lrnv
        msgsv msgsAAv ltv pciv dccv ucsv rov eev hev cqv pvv htv etv
        retv dpfv sdrv tickv stepv lgv primv tlv rlstv rlentsv rloffv
        rlsipv rloipv rlulgv cmv rlapv rladv rllgv rlmxv rlaszv rlpzv)
      (.retV rnArgV
        (.callArgsK ⟨"raft.raft.softState"⟩ plans [] [] env k)) ch
      = .ok (.returning
          (.frame plans env [Loc.base ⟨34⟩] [] k false),
        { wBase with
            heap := [(Loc.base ⟨31⟩,
              { declaredTy := dty
                value := raftCellV tmv vtv ldv stv idv rsv mmv muv
                  trkv lrnv msgsv msgsAAv ltv pciv dccv ucsv rov eev
                  hev cqv pvv htv etv retv dpfv sdrv tickv stepv lgv
                  primv tlv }),
             (Loc.base ⟨32⟩,
              { declaredTy := rldty
                value := logCellV rlstv rlentsv rloffv rlsipv rloipv
                  rlulgv (.int cmv .uint64) rlapv rladv rllgv rlmxv
                  rlaszv rlpzv }),
             (Loc.base ⟨33⟩,
              { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.raft"⟩))
                value := rnArgV }),
             (Loc.base ⟨34⟩,
              { declaredTy := some (Ty.defined ⟨"raft.SoftState"⟩)
                value := .struct ⟨"raft.SoftState"⟩
                  #[("Lead",
                     .int (IntKind.normalize .uint64
                       (IntKind.normalize .uint64 ldv)) .uint64),
                    ("RaftState",
                     .int (IntKind.normalize .uint64
                       (IntKind.normalize .uint64 stv)) .uint64)] })]
            nextAddr := 35 },
        ch) := by
  kernel_rfl

/-- **THE `raft.softState` CallSpecR**: returns
`SoftState{Lead: r.lead, RaftState: r.state}` BY VALUE — the
shell-sync fact (C2) the harvest's SoftState read consumes; the
footprint reads back unchanged (26 of 31 raft fields ride free). -/
theorem raft_softState_callSpecR (dty rldty : Option Ty)
    (tmv vtv ldv stv : Int)
    (idv rsv mmv muv trkv lrnv msgsv msgsAAv ltv pciv dccv ucsv rov
     eev hev cqv pvv htv etv retv dpfv sdrv tickv stepv lgv primv
     tlv : GoValue)
    (rlstv rlentsv rloffv rlsipv rloipv rlulgv : GoValue) (cmv : Int)
    (rlapv rladv rllgv rlmxv rlaszv rlpzv : GoValue)
    (hld0 : 0 ≤ ldv) (hld64 : ldv < 18446744073709551616)
    (hst0 : 0 ≤ stv) (hst64 : stv < 18446744073709551616) :
    CallSpecR
      (RNPre dty rldty tmv vtv ldv stv idv rsv mmv muv trkv lrnv
        msgsv msgsAAv ltv pciv dccv ucsv rov eev hev cqv pvv htv etv
        retv dpfv sdrv tickv stepv lgv primv tlv rlstv rlentsv rloffv
        rlsipv rloipv rlulgv cmv rlapv rladv rllgv rlmxv rlaszv
        rlpzv)
      ⟨"raft.raft.softState"⟩ [] rnArgV
      (fun σ' vs =>
        vs = [.struct ⟨"raft.SoftState"⟩
                #[("Lead", .int ldv .uint64),
                  ("RaftState", .int stv .uint64)]] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := dty
                   value := raftCellV tmv vtv ldv stv idv rsv mmv muv
                     trkv lrnv msgsv msgsAAv ltv pciv dccv ucsv rov
                     eev hev cqv pvv htv etv retv dpfv sdrv tickv
                     stepv lgv primv tlv }) := by
  intro σ hP plans env k ch
  have hLd : IntKind.normalize .uint64 ldv = ldv :=
    normalize_uint64_eq hld0 hld64
  have hSt : IntKind.normalize .uint64 stv = stv :=
    normalize_uint64_eq hst0 hst64
  have h1 := ss_span dty rldty tmv vtv ldv stv idv rsv mmv muv trkv
    lrnv msgsv msgsAAv ltv pciv dccv ucsv rov eev hev cqv pvv htv etv
    retv dpfv sdrv tickv stepv lgv primv tlv rlstv rlentsv rloffv
    rlsipv rloipv rlulgv cmv rlapv rladv rllgv rlmxv rlaszv rlpzv
    plans env k ch
  rw [hLd, hLd, hSt, hSt] at h1
  refine ⟨28,
    { wBase with
        heap := [(Loc.base ⟨31⟩,
          { declaredTy := dty
            value := raftCellV tmv vtv ldv stv idv rsv mmv muv
              trkv lrnv msgsv msgsAAv ltv pciv dccv ucsv rov eev
              hev cqv pvv htv etv retv dpfv sdrv tickv stepv lgv
              primv tlv }),
         (Loc.base ⟨32⟩,
          { declaredTy := rldty
            value := logCellV rlstv rlentsv rloffv rlsipv rloipv
              rlulgv (.int cmv .uint64) rlapv rladv rllgv rlmxv
              rlaszv rlpzv }),
         (Loc.base ⟨33⟩,
          { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.raft"⟩))
            value := rnArgV }),
         (Loc.base ⟨34⟩,
          { declaredTy := some (Ty.defined ⟨"raft.SoftState"⟩)
            value := .struct ⟨"raft.SoftState"⟩
              #[("Lead", .int ldv .uint64),
                ("RaftState", .int stv .uint64)] })]
        nextAddr := 35 },
    [Loc.base ⟨34⟩],
    [.struct ⟨"raft.SoftState"⟩
      #[("Lead", .int ldv .uint64), ("RaftState", .int stv .uint64)]],
    ch, ?_, ?_, ⟨rfl, ?_⟩, List.suffix_refl ch⟩
  · rw [hP]; exact h1
  · rfl
  · rfl

end SoftState

/-! ## `raft.hardState` (census raft.go:523) -/

section HardState

/-- The hardState span (PRIVATE — 117 steps, one window: the three
scalar reads (`r.Term`, `r.Vote`, `l.committed` through the raftLog
pointer), three fresh value cells, the fresh three-pointer HardState
cell, the result store). -/
private theorem hs_span (dty rldty : Option Ty)
    (tmv vtv ldv stv : Int)
    (idv rsv mmv muv trkv lrnv msgsv msgsAAv ltv pciv dccv ucsv rov
     eev hev cqv pvv htv etv retv dpfv sdrv tickv stepv lgv primv
     tlv : GoValue)
    (rlstv rlentsv rloffv rlsipv rloipv rlulgv : GoValue) (cmv : Int)
    (rlapv rladv rllgv rlmxv rlaszv rlpzv : GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 117
      (rnFam dty rldty tmv vtv ldv stv idv rsv mmv muv trkv lrnv
        msgsv msgsAAv ltv pciv dccv ucsv rov eev hev cqv pvv htv etv
        retv dpfv sdrv tickv stepv lgv primv tlv rlstv rlentsv rloffv
        rlsipv rloipv rlulgv cmv rlapv rladv rllgv rlmxv rlaszv rlpzv)
      (.retV rnArgV
        (.callArgsK ⟨"raft.raft.hardState"⟩ plans [] [] env k)) ch
      = .ok (.returning
          (.frame plans env [Loc.base ⟨34⟩] [] k false),
        { wBase with
            heap := [(Loc.base ⟨31⟩,
              { declaredTy := dty
                value := raftCellV tmv vtv ldv stv idv rsv mmv muv
                  trkv lrnv msgsv msgsAAv ltv pciv dccv ucsv rov eev
                  hev cqv pvv htv etv retv dpfv sdrv tickv stepv lgv
                  primv tlv }),
             (Loc.base ⟨32⟩,
              { declaredTy := rldty
                value := logCellV rlstv rlentsv rloffv rlsipv rloipv
                  rlulgv (.int cmv .uint64) rlapv rladv rllgv rlmxv
                  rlaszv rlpzv }),
             (Loc.base ⟨33⟩,
              { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.raft"⟩))
                value := rnArgV }),
             (Loc.base ⟨34⟩,
              { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.HardState"⟩))
                value := .addr (Loc.base ⟨45⟩) }),
             (Loc.base ⟨35⟩,
              { declaredTy := some (Ty.pointer (Ty.int .uint64))
                value := .addr (Loc.base ⟨36⟩) }),
             (Loc.base ⟨36⟩,
              { declaredTy := some (Ty.int .uint64)
                value := .int tmv .uint64 }),
             (Loc.base ⟨37⟩,
              { declaredTy := some (Ty.pointer (Ty.int .uint64))
                value := .addr (Loc.base ⟨36⟩) }),
             (Loc.base ⟨38⟩,
              { declaredTy := some (Ty.pointer (Ty.int .uint64))
                value := .addr (Loc.base ⟨39⟩) }),
             (Loc.base ⟨39⟩,
              { declaredTy := some (Ty.int .uint64)
                value := .int vtv .uint64 }),
             (Loc.base ⟨40⟩,
              { declaredTy := some (Ty.pointer (Ty.int .uint64))
                value := .addr (Loc.base ⟨39⟩) }),
             (Loc.base ⟨41⟩,
              { declaredTy := some (Ty.pointer (Ty.int .uint64))
                value := .addr (Loc.base ⟨42⟩) }),
             (Loc.base ⟨42⟩,
              { declaredTy := some (Ty.int .uint64)
                value := .int cmv .uint64 }),
             (Loc.base ⟨43⟩,
              { declaredTy := some (Ty.pointer (Ty.int .uint64))
                value := .addr (Loc.base ⟨42⟩) }),
             (Loc.base ⟨44⟩,
              { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.HardState"⟩))
                value := .addr (Loc.base ⟨45⟩) }),
             (Loc.base ⟨45⟩,
              { declaredTy := some (Ty.defined ⟨"raftpb.HardState"⟩)
                value := .struct ⟨"raftpb.HardState"⟩
                  #[("Term", .addr (Loc.base ⟨36⟩)),
                    ("Vote", .addr (Loc.base ⟨39⟩)),
                    ("Commit", .addr (Loc.base ⟨42⟩))] })]
            nextAddr := 46 },
        ch) := by
  kernel_rfl

/-- **THE `raft.hardState` CallSpecR**: returns a POINTER to a fresh
`raftpb.HardState` whose Term/Vote/Commit point at fresh cells
holding exactly `r.Term` / `r.Vote` / `r.raftLog.committed` — the
shell-sync/term-agreement carrier (C2) the harvest's SetHardState
and the MsgStorageAppendResp construction consume. -/
theorem raft_hardState_callSpecR (dty rldty : Option Ty)
    (tmv vtv ldv stv : Int)
    (idv rsv mmv muv trkv lrnv msgsv msgsAAv ltv pciv dccv ucsv rov
     eev hev cqv pvv htv etv retv dpfv sdrv tickv stepv lgv primv
     tlv : GoValue)
    (rlstv rlentsv rloffv rlsipv rloipv rlulgv : GoValue) (cmv : Int)
    (rlapv rladv rllgv rlmxv rlaszv rlpzv : GoValue) :
    CallSpecR
      (RNPre dty rldty tmv vtv ldv stv idv rsv mmv muv trkv lrnv
        msgsv msgsAAv ltv pciv dccv ucsv rov eev hev cqv pvv htv etv
        retv dpfv sdrv tickv stepv lgv primv tlv rlstv rlentsv rloffv
        rlsipv rloipv rlulgv cmv rlapv rladv rllgv rlmxv rlaszv
        rlpzv)
      ⟨"raft.raft.hardState"⟩ [] rnArgV
      (fun σ' vs =>
        vs = [.addr (Loc.base ⟨45⟩)] ∧
        Heap.lookup σ'.heap (Loc.base ⟨45⟩)
          = some { declaredTy := some (Ty.defined ⟨"raftpb.HardState"⟩)
                   value := .struct ⟨"raftpb.HardState"⟩
                     #[("Term", .addr (Loc.base ⟨36⟩)),
                       ("Vote", .addr (Loc.base ⟨39⟩)),
                       ("Commit", .addr (Loc.base ⟨42⟩))] } ∧
        Heap.lookup σ'.heap (Loc.base ⟨36⟩)
          = some { declaredTy := some (Ty.int .uint64)
                   value := .int tmv .uint64 } ∧
        Heap.lookup σ'.heap (Loc.base ⟨39⟩)
          = some { declaredTy := some (Ty.int .uint64)
                   value := .int vtv .uint64 } ∧
        Heap.lookup σ'.heap (Loc.base ⟨42⟩)
          = some { declaredTy := some (Ty.int .uint64)
                   value := .int cmv .uint64 } ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some { declaredTy := dty
                   value := raftCellV tmv vtv ldv stv idv rsv mmv muv
                     trkv lrnv msgsv msgsAAv ltv pciv dccv ucsv rov
                     eev hev cqv pvv htv etv retv dpfv sdrv tickv
                     stepv lgv primv tlv }) := by
  intro σ hP plans env k ch
  have h1 := hs_span dty rldty tmv vtv ldv stv idv rsv mmv muv trkv
    lrnv msgsv msgsAAv ltv pciv dccv ucsv rov eev hev cqv pvv htv etv
    retv dpfv sdrv tickv stepv lgv primv tlv rlstv rlentsv rloffv
    rlsipv rloipv rlulgv cmv rlapv rladv rllgv rlmxv rlaszv rlpzv
    plans env k ch
  refine ⟨117,
    { wBase with
        heap := [(Loc.base ⟨31⟩,
          { declaredTy := dty
            value := raftCellV tmv vtv ldv stv idv rsv mmv muv
              trkv lrnv msgsv msgsAAv ltv pciv dccv ucsv rov eev
              hev cqv pvv htv etv retv dpfv sdrv tickv stepv lgv
              primv tlv }),
         (Loc.base ⟨32⟩,
          { declaredTy := rldty
            value := logCellV rlstv rlentsv rloffv rlsipv rloipv
              rlulgv (.int cmv .uint64) rlapv rladv rllgv rlmxv
              rlaszv rlpzv }),
         (Loc.base ⟨33⟩,
          { declaredTy := some (Ty.pointer (Ty.defined ⟨"raft.raft"⟩))
            value := rnArgV }),
         (Loc.base ⟨34⟩,
          { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.HardState"⟩))
            value := .addr (Loc.base ⟨45⟩) }),
         (Loc.base ⟨35⟩,
          { declaredTy := some (Ty.pointer (Ty.int .uint64))
            value := .addr (Loc.base ⟨36⟩) }),
         (Loc.base ⟨36⟩,
          { declaredTy := some (Ty.int .uint64)
            value := .int tmv .uint64 }),
         (Loc.base ⟨37⟩,
          { declaredTy := some (Ty.pointer (Ty.int .uint64))
            value := .addr (Loc.base ⟨36⟩) }),
         (Loc.base ⟨38⟩,
          { declaredTy := some (Ty.pointer (Ty.int .uint64))
            value := .addr (Loc.base ⟨39⟩) }),
         (Loc.base ⟨39⟩,
          { declaredTy := some (Ty.int .uint64)
            value := .int vtv .uint64 }),
         (Loc.base ⟨40⟩,
          { declaredTy := some (Ty.pointer (Ty.int .uint64))
            value := .addr (Loc.base ⟨39⟩) }),
         (Loc.base ⟨41⟩,
          { declaredTy := some (Ty.pointer (Ty.int .uint64))
            value := .addr (Loc.base ⟨42⟩) }),
         (Loc.base ⟨42⟩,
          { declaredTy := some (Ty.int .uint64)
            value := .int cmv .uint64 }),
         (Loc.base ⟨43⟩,
          { declaredTy := some (Ty.pointer (Ty.int .uint64))
            value := .addr (Loc.base ⟨42⟩) }),
         (Loc.base ⟨44⟩,
          { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.HardState"⟩))
            value := .addr (Loc.base ⟨45⟩) }),
         (Loc.base ⟨45⟩,
          { declaredTy := some (Ty.defined ⟨"raftpb.HardState"⟩)
            value := .struct ⟨"raftpb.HardState"⟩
              #[("Term", .addr (Loc.base ⟨36⟩)),
                ("Vote", .addr (Loc.base ⟨39⟩)),
                ("Commit", .addr (Loc.base ⟨42⟩))] })]
        nextAddr := 46 },
    [Loc.base ⟨34⟩], [.addr (Loc.base ⟨45⟩)], ch,
    ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩, List.suffix_refl ch⟩
  · rw [hP]; exact h1
  · rfl
  · rfl

end HardState

/-! ## `raft.MustSync` (census rawnode.go:191) — the nonzero-entries
member (the harvest's common case: entries appended → sync owed).
The subject is the three-way OR `entsnum ≠ 0 || vote changed || term
changed`; this member covers the first disjunct's short-circuit —
NOTHING beyond the two HardState pointers is read (the scalar cells
ride fully free). The vote/term-comparison arms are
consumer-demand/parked (log record). -/

section MustSync

/-- The `st` HardState cell (Term → 33, Vote → 35, Commit free). -/
def msyncHS1 (h1dty : Option Ty) (cm1 : GoValue) : HeapCell :=
  { declaredTy := h1dty
    value := .struct ⟨"raftpb.HardState"⟩
      #[("Term", .addr (Loc.base ⟨33⟩)), ("Vote", .addr (Loc.base ⟨35⟩)),
        ("Commit", cm1)] }

/-- The `prevst` HardState cell (Term → 34, Vote → 36). -/
def msyncHS2 (h2dty : Option Ty) (cm2 : GoValue) : HeapCell :=
  { declaredTy := h2dty
    value := .struct ⟨"raftpb.HardState"⟩
      #[("Term", .addr (Loc.base ⟨34⟩)), ("Vote", .addr (Loc.base ⟨36⟩)),
        ("Commit", cm2)] }

/-- The MustSync footprint family (31/32 = the two HardState cells,
33-36 = their scalar targets — FREE cells for this member). -/
def msyncFam (h1dty h2dty : Option Ty) (cm1 cm2 : GoValue)
    (c33 c34 c35 c36 : HeapCell) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨31⟩, msyncHS1 h1dty cm1),
       (Loc.base ⟨32⟩, msyncHS2 h2dty cm2),
       (Loc.base ⟨33⟩, c33), (Loc.base ⟨34⟩, c34),
       (Loc.base ⟨35⟩, c35), (Loc.base ⟨36⟩, c36)]
      nextAddr := 37 }

def MSyncPre (h1dty h2dty : Option Ty) (cm1 cm2 : GoValue)
    (c33 c34 c35 c36 : HeapCell) (σm : ExecState) : Prop :=
  σm = msyncFam h1dty h2dty cm1 cm2 c33 c34 c35 c36

private def msyncEnv : LocalEnv :=
  [[("$c1813", Loc.base ⟨41⟩)],
   [("$res0", Loc.base ⟨40⟩), ("entsnum", Loc.base ⟨39⟩),
    ("prevst", Loc.base ⟨38⟩), ("st", Loc.base ⟨37⟩)]]

private def msyncVoteArm : Stmt :=
  .block #[] #[
    .seqn #[.initialization ⟨"$c1811", .int .uint64⟩,
      .call #[.var "$c1811"] ⟨"raftpb.HardState.GetVote"⟩
        #[.var "st"]],
    .seqn #[.initialization ⟨"$c1812", .int .uint64⟩,
      .call #[.var "$c1812"] ⟨"raftpb.HardState.GetVote"⟩
        #[.var "prevst"]],
    .seqn #[.assign (.var "$c1813")
      (.neqCmp (.int .uint64) (.var "$c1811") (.var "$c1812"))]]

private def msyncTermArm : Stmt :=
  .block #[] #[
    .seqn #[.initialization ⟨"$c1814", .int .uint64⟩,
      .call #[.var "$c1814"] ⟨"raftpb.HardState.GetTerm"⟩
        #[.var "st"]],
    .seqn #[.initialization ⟨"$c1815", .int .uint64⟩,
      .call #[.var "$c1815"] ⟨"raftpb.HardState.GetTerm"⟩
        #[.var "prevst"]],
    .seqn #[.assign (.var "$c1816")
      (.neqCmp (.int .uint64) (.var "$c1814") (.var "$c1815"))]]

private def msyncTail : List Stmt :=
  [.seqn #[.initialization ⟨"$c1816", Ty.bool⟩,
     .assign (.var "$c1816") (.var "$c1813")],
   .ifThenElse (.not (.var "$c1816")) msyncTermArm (.seqn #[]),
   .seqn #[.assign (.var "$res0") (.var "$c1816"), .returnStmt]]

private def msyncFrame (plans : List (TargetShape × List Expr))
    (env : LocalEnv) (k : Cont) : Cont :=
  .frame plans env [Loc.base ⟨40⟩] [] k false

private def msyncIn (h1dty h2dty : Option Ty) (cm1 cm2 : GoValue)
    (c33 c34 c35 c36 : HeapCell) (env2 : GoValue) (r0 c1813 : GoValue)
    (extra : Heap) (na : Nat) : ExecState :=
  { wBase with
      heap := [(Loc.base ⟨31⟩, msyncHS1 h1dty cm1),
       (Loc.base ⟨32⟩, msyncHS2 h2dty cm2),
       (Loc.base ⟨33⟩, c33), (Loc.base ⟨34⟩, c34),
       (Loc.base ⟨35⟩, c35), (Loc.base ⟨36⟩, c36),
       (Loc.base ⟨37⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.HardState"⟩))
          value := .addr (Loc.base ⟨31⟩) }),
       (Loc.base ⟨38⟩,
        { declaredTy := some (Ty.pointer (Ty.defined ⟨"raftpb.HardState"⟩))
          value := .addr (Loc.base ⟨32⟩) }),
       (Loc.base ⟨39⟩,
        { declaredTy := some (Ty.int .int), value := env2 }),
       (Loc.base ⟨40⟩,
        { declaredTy := some Ty.bool, value := r0 }),
       (Loc.base ⟨41⟩,
        { declaredTy := some Ty.bool, value := c1813 })]
        ++ extra
      nextAddr := na }

/-- Window 1 (24 steps): entry, the `entsnum ≠ 0` comparison and its
negation, to the first branch boundary (the stuck two-scalar
`Int`-beq riding). -/
private theorem msync_w1 (h1dty h2dty : Option Ty) (cm1 cm2 : GoValue)
    (c33 c34 c35 c36 : HeapCell) (en : Int)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 24
      (msyncFam h1dty h2dty cm1 cm2 c33 c34 c35 c36)
      (.retV (.int en .int)
        (.callArgsK ⟨"raft.MustSync"⟩ plans
          [.addr (Loc.base ⟨31⟩), .addr (Loc.base ⟨32⟩)] [] env k)) ch
      = .ok (.retV
          (.bool (!(!(IntKind.normalize .int en == 0))))
          (.ifK msyncVoteArm (.seqn #[]) msyncEnv
            (.seq msyncTail msyncEnv (msyncFrame plans env k))),
        msyncIn h1dty h2dty cm1 cm2 c33 c34 c35 c36
          (.int (IntKind.normalize .int en) .int) (.bool false)
          (.bool (!(IntKind.normalize .int en == 0))) [] 42,
        ch) := by
  kernel_rfl

/-- Window 2 (35 steps, from the crossed FALSE branch at the pinned
TRUE `$c1813`): the `$c1816` copy, the second negation (false — the
term arm skipped), the result store, return arrival. -/
private theorem msync_w2 (h1dty h2dty : Option Ty) (cm1 cm2 : GoValue)
    (c33 c34 c35 c36 : HeapCell) (env2 : GoValue)
    (plans : List (TargetShape × List Expr)) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFnIter 35
      (msyncIn h1dty h2dty cm1 cm2 c33 c34 c35 c36 env2 (.bool false)
        (.bool true) [] 42)
      (.exec (.seqn #[]) msyncEnv
        (.seq msyncTail msyncEnv (msyncFrame plans env k))) ch
      = .ok (.returning (msyncFrame plans env k),
        msyncIn h1dty h2dty cm1 cm2 c33 c34 c35 c36 env2 (.bool true)
          (.bool true)
          [(Loc.base ⟨42⟩,
            { declaredTy := some Ty.bool, value := .bool true })] 43,
        ch) := by
  kernel_rfl

/-- **THE `raft.MustSync` CallSpecR, nonzero-entries member**
(`entsnum ≠ 0` — the short-circuit disjunct): returns `true` with
NOTHING read beyond the two receiver pointers (every HardState
scalar cell rides free); footprint unchanged. The harvest's
"entries appended → sync owed" fact (U3.2c's drain vocabulary). -/
theorem raft_MustSync_nonzeroEnts_callSpecR (h1dty h2dty : Option Ty)
    (cm1 cm2 : GoValue) (c33 c34 c35 c36 : HeapCell) (en : Int)
    (hen0 : 0 ≤ en) (hen63 : en < 9223372036854775808)
    (hne : en ≠ 0) :
    CallSpecR
      (MSyncPre h1dty h2dty cm1 cm2 c33 c34 c35 c36)
      ⟨"raft.MustSync"⟩
      [.addr (Loc.base ⟨31⟩), .addr (Loc.base ⟨32⟩)] (.int en .int)
      (fun σ' vs =>
        vs = [.bool true] ∧
        Heap.lookup σ'.heap (Loc.base ⟨31⟩)
          = some (msyncHS1 h1dty cm1) ∧
        Heap.lookup σ'.heap (Loc.base ⟨32⟩)
          = some (msyncHS2 h2dty cm2)) := by
  intro σ hP plans env k ch
  have hEn : IntKind.normalize .int en = en :=
    normalize_int_eq (by omega) hen63
  have hBeq : (en == 0) = false := beq_eq_false_iff_ne.mpr hne
  have h1 := msync_w1 h1dty h2dty cm1 cm2 c33 c34 c35 c36 en
    plans env k ch
  rw [hEn, hBeq] at h1
  have hx : stepFn
      (msyncIn h1dty h2dty cm1 cm2 c33 c34 c35 c36
        (.int en .int) (.bool false) (.bool true) [] 42)
      (.retV (.bool (!(!false)))
        (.ifK msyncVoteArm (.seqn #[]) msyncEnv
          (.seq msyncTail msyncEnv (msyncFrame plans env k)))) ch
      = .ok (.exec (.seqn #[]) msyncEnv
          (.seq msyncTail msyncEnv (msyncFrame plans env k)),
        msyncIn h1dty h2dty cm1 cm2 c33 c34 c35 c36
          (.int en .int) (.bool false) (.bool true) [] 42,
        ch) :=
    stepFn_ifK_false rfl
  have h2 := msync_w2 h1dty h2dty cm1 cm2 c33 c34 c35 c36
    (.int en .int) plans env k ch
  refine ⟨24 + (1 + 35),
    msyncIn h1dty h2dty cm1 cm2 c33 c34 c35 c36 (.int en .int)
      (.bool true) (.bool true)
      [(Loc.base ⟨42⟩,
        { declaredTy := some Ty.bool, value := .bool true })] 43,
    [Loc.base ⟨40⟩], [.bool true], ch, ?_, ?_, ⟨rfl, rfl, ?_⟩,
    List.suffix_refl ch⟩
  · rw [hP]
    exact stepFnIter_chain h1 (stepFnIter_chain (stepFnIter_one hx) h2)
  · rfl
  · rfl

end MustSync

/-- Non-vacuity of the raft-cell carrier (the ∃-discharge, concrete
values in every free slot). -/
theorem rnPre_inhabited :
    RNPre none none 7 1 1 2
      (.int 1 .uint64) .nil (.int 1048576 .uint64) (.int 0 .uint64)
      .nil (.bool false) .nil .nil (.int 0 .uint64) (.int 0 .uint64)
      (.bool false) (.int 0 .uint64) .nil (.int 0 .int) (.int 0 .int)
      (.bool false) (.bool false) (.int 1 .int) (.int 10 .int)
      (.int 13 .int) (.bool false) (.bool false) .nil .nil .nil .nil
      .nil
      .nil (.slice ⟨none, 0, 0, 0⟩) (.int 104 .uint64) (.bool false)
      (.int 104 .uint64) .nil 103 (.int 103 .uint64)
      (.int 103 .uint64) .nil (.int 1048576 .uint64) (.int 0 .uint64)
      (.bool false)
      (rnFam none none 7 1 1 2
        (.int 1 .uint64) .nil (.int 1048576 .uint64) (.int 0 .uint64)
        .nil (.bool false) .nil .nil (.int 0 .uint64) (.int 0 .uint64)
        (.bool false) (.int 0 .uint64) .nil (.int 0 .int) (.int 0 .int)
        (.bool false) (.bool false) (.int 1 .int) (.int 10 .int)
        (.int 13 .int) (.bool false) (.bool false) .nil .nil .nil .nil
        .nil
        .nil (.slice ⟨none, 0, 0, 0⟩) (.int 104 .uint64) (.bool false)
        (.int 104 .uint64) .nil 103 (.int 103 .uint64)
        (.int 103 .uint64) .nil (.int 1048576 .uint64) (.int 0 .uint64)
        (.bool false)) := rfl

end GoLean.RaftSeam
