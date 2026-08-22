import VerdiCompat.Raft

/-!
# verdi-raft's ghost-layer (refined) proof scaffold, re-proved in Lean

Port of the ghost-variable refinement layer that ~73 of verdi-raft's 90
RaftProofs files ride (campaign Arc 3, opening unit; design doc
`docs/2026-08-22_campaign-arc3-refined-port-design.md`). Sources, at the
recorded pins (`deps/verdi-raft` @ a3375e8, `deps/verdi` @ 7e1641b):

- `Raft/RaftRefinementInterface.v` — `electionsData` (`:10-16`), the
  `update_elections_data_*` ghost handlers (`:18-146`), the refined
  parameter triple (via `GhostSimulations.v:26-65`, inlined here at its
  raft instance — design decision D1), `refined_raft_intermediate_reachable`
  (`:166-209`), and the eleven `refined_raft_net_invariant_*` obligation
  shapes (`:211-325`).
- `RaftProofs/RaftRefinementProof.v` — the dispatchers (`:10-55`), THE
  induction principle `refined_raft_net_invariant` (`:56-194`), and the
  transfer components `simulation_1`/`lift_prop`/`simulation_2`/
  `lower_prop`/`deghost_spec` (`:429-618`), whose step_failure legs are
  Verdi's `ghost_simulation_1`/`ghost_simulation_2`
  (`Core/GhostSimulations.v:166-232`), here proved directly at the raft
  instance (D1: Coq routes them through `TotalMapSimulations`, which we
  do not port).

The ghost state is a HISTORY VARIABLE: written beside the real state on
every handler step, never read by execution, hence erasable (`deghost`,
the two simulations). Statements are 1:1 against the cited lines; proofs
are re-proved from scratch (Ltac does not port). Constitution §3.2
note: ghost state is a proof device — every ghost-proved invariant
reaches headline form only through `lower_prop`'s base-level projection.

Naming: as in `ProofStructure.lean`, Coq's invariant variable `P` is
`Pr` (`P` is our `BaseParams` section variable). Not ported (recorded
gaps, arc log GAP-1/GAP-2): the primed obligation variants
(`RaftRefinementInterface.v:327-439`) and the msg-ghost layer
(`RaftMsgRefinementInterface.v`).
-/

namespace VerdiCompat
namespace Raft

section RefinedProofStructure
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

/-- `RaftRefinementInterface.v:10-16` — the election-history ghost state.
`votes`: every vote ever granted (term, votee), per voter; `votesWithLog`:
the voter's log at each grant; `cronies`: a candidate's supporters per
term; `leaderLogs`: the log held at each election win; `allEntries`:
every entry ever appended. -/
structure electionsData where
  votes : List (term × name (P := P))
  votesWithLog : List (term × name (P := P) × List (entry (P := P)))
  cronies : term → List (name (P := P))
  leaderLogs : List (term × List (entry (P := P)))
  allEntries : List (term × entry (P := P))

/-- `RaftRefinementInterface.v:151-153` (the `ghost_init` field). -/
def elections_ghost_init : electionsData (P := P) where
  votes := []
  votesWithLog := []
  cronies := fun _ => []
  leaderLogs := []
  allEntries := []

/-- `RaftRefinementInterface.v:18-41`. A newly recorded or changed vote
appends to `votes`/`votesWithLog`; an unchanged re-grant (same term, same
candidate) records nothing. NOTE upstream's argument passing at the
dispatch site (`:94-95`): `src` is passed for BOTH `src` and
`candidateId`; the `candidateId` parameter is kept (unused beyond the
handler call) so obligation statements match upstream line-for-line. -/
def update_elections_data_requestVote (me _src : name (P := P)) (t : term)
    (candidateId : name (P := P)) (lastLogIndex : logIndex) (lastLogTerm : term)
    (st : electionsData (P := P) × raft_data (P := P)) : electionsData (P := P) :=
  let st' := (handleRequestVote me st.2 t candidateId lastLogIndex lastLogTerm).1
  match st.2.votedFor, st'.votedFor with
  | none, some cid =>
    { st.1 with
        votes := (st'.currentTerm, cid) :: st.1.votes,
        votesWithLog := (st'.currentTerm, cid, st'.log) :: st.1.votesWithLog }
  | some cid, some cid' =>
    if (st.2.currentTerm == st'.currentTerm) && decide (cid = cid') then st.1
    else
      { st.1 with
          votes := (st'.currentTerm, cid') :: st.1.votes,
          votesWithLog := (st'.currentTerm, cid', st'.log) :: st.1.votesWithLog }
  | _, _ => st.1

/-- `RaftRefinementInterface.v:43-72`. A candidate/leader snapshots its
`votesReceived` into `cronies` at its current term; a candidate→leader
transition additionally snapshots its log into `leaderLogs`. -/
def update_elections_data_requestVoteReply (me src : name (P := P)) (t : term)
    (voteGranted : Bool) (st : electionsData (P := P) × raft_data (P := P)) :
    electionsData (P := P) :=
  let st' := handleRequestVoteReply me st.2 src t voteGranted
  match st'.type with
  | .Follower => st.1
  | .Candidate =>
    { st.1 with
        cronies := fun tm =>
          if tm = st'.currentTerm then st'.votesReceived else st.1.cronies tm }
  | .Leader =>
    { st.1 with
        cronies := fun tm =>
          if tm = st'.currentTerm then st'.votesReceived else st.1.cronies tm,
        leaderLogs :=
          if st.2.type = .Candidate then (st'.currentTerm, st'.log) :: st.1.leaderLogs
          else st.1.leaderLogs }

/-- `RaftRefinementInterface.v:74-89`. An ACCEPTED append records the
reply's entries into `allEntries`. NOTE the Coq pattern
`AppendEntriesReply t entries true` SHADOWS the request's `t`/`entries`
with the reply's — named `t'`/`es'` here to make the shadowing visible;
the recorded pairs use the REPLY's term. -/
def update_elections_data_appendEntries (me : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) (t : term)
    (leaderId : name (P := P)) (prevLogIndex : logIndex) (prevLogTerm : term)
    (entries : List (entry (P := P))) (leaderCommit : logIndex) :
    electionsData (P := P) :=
  let m := (handleAppendEntries me st.2 t leaderId prevLogIndex prevLogTerm
      entries leaderCommit).2
  match m with
  | .AppendEntriesReply t' es' true =>
    { st.1 with allEntries := (es'.map fun e => (t', e)) ++ st.1.allEntries }
  | _ => st.1

/-- `RaftRefinementInterface.v:92-101` — the per-message ghost dispatcher.
Mirrors upstream exactly, INCLUDING passing `src` in the `candidateId`
position for `RequestVote` (the pattern's own `candidateId` is unused,
as upstream). -/
def update_elections_data_net (me src : name (P := P)) (m : msg (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) : electionsData (P := P) :=
  match m with
  | .RequestVote t _candidateId lastLogIndex lastLogTerm =>
    update_elections_data_requestVote me src t src lastLogIndex lastLogTerm st
  | .RequestVoteReply t voteGranted =>
    update_elections_data_requestVoteReply me src t voteGranted st
  | .AppendEntries t lid prevLogIndex prevLogTerm entries leaderCommit =>
    update_elections_data_appendEntries me st t lid prevLogIndex prevLogTerm
      entries leaderCommit
  | .AppendEntriesReply _ _ _ => st.1

/-- `RaftRefinementInterface.v:103-124`. A non-leader timing out records
its (self-)vote; if it became candidate, its fresh `votesReceived`
snapshots into `cronies`. -/
def update_elections_data_timeout (me : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) : electionsData (P := P) :=
  let st' := (handleTimeout me st.2).2.1
  match st'.votedFor with
  | some cid =>
    if st.2.type = .Leader then st.1
    else
      { st.1 with
          votes := (st'.currentTerm, cid) :: st.1.votes,
          votesWithLog := (st'.currentTerm, cid, st'.log) :: st.1.votesWithLog,
          cronies :=
            if st'.type = .Candidate then
              fun tm =>
                if tm = st'.currentTerm then st'.votesReceived else st.1.cronies tm
            else st.1.cronies }
  | none => st.1

/-- `RaftRefinementInterface.v:127-140`. A leader's accepted client
request records the new head entry into `allEntries`. -/
def update_elections_data_client_request (me : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) (client : R.clientId)
    (id : Nat) (c : P.input) : electionsData (P := P) :=
  let st' := (handleClientRequest me st.2 client id c).2.1
  if st.2.log.length <? st'.log.length then
    match st'.log with
    | e :: _ => { st.1 with allEntries := (st'.currentTerm, e) :: st.1.allEntries }
    | [] => st.1
  else st.1

/-- `RaftRefinementInterface.v:142-146` — the per-input ghost dispatcher. -/
def update_elections_data_input (me : name (P := P)) (inp : raft_input (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) : electionsData (P := P) :=
  match inp with
  | .Timeout => update_elections_data_timeout me st
  | .ClientRequest client id c => update_elections_data_client_request me st client id c

/-! ## The refined parameter triple

`GhostSimulations.v:26-65` inlined at the raft instance (design doc D1):
the refined node state is `ghost × real`; the refined handlers run the
REAL handler on the real component and write the ghost beside it — the
ghost never influences execution. -/

/-- `GhostSimulations.v:41-46` at `elections_ghost_params`
(`RaftRefinementInterface.v:148-158`). -/
@[reducible] def raft_refined_base_params : BaseParams where
  data := electionsData (P := P) × raft_data (P := P)
  input := raft_input (P := P)
  output := raft_output (P := P)

/-- `GhostSimulations.v:26-29` (`refined_net_handlers`) at the raft
instance. -/
def refined_net_handlers (me src : name (P := P)) (m : msg (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) :
    List (raft_output (P := P)) × (electionsData (P := P) × raft_data (P := P)) ×
      List (name (P := P) × msg (P := P)) :=
  let (out, st', ps) := RaftNetHandler me src m st.2
  (out, (update_elections_data_net me src m st, st'), ps)

/-- `GhostSimulations.v:31-33` (`refined_input_handlers`) at the raft
instance. -/
def refined_input_handlers (me : name (P := P)) (inp : raft_input (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) :
    List (raft_output (P := P)) × (electionsData (P := P) × raft_data (P := P)) ×
      List (name (P := P) × msg (P := P)) :=
  let (out, st', ps) := RaftInputHandler me inp st.2
  (out, (update_elections_data_input me inp st, st'), ps)

/-- `GhostSimulations.v:48-60` + `RaftRefinementInterface.v:159`
(`raft_refined_multi_params`). -/
@[reducible] def raft_refined_multi_params :
    MultiParams (raft_refined_base_params (P := P)) where
  name := name (P := P)
  msg := msg (P := P)
  msg_eq_dec := inferInstance
  name_eq_dec := inferInstance
  nodes := nodes
  all_names_nodes := fun n => allFin_all n
  no_dup_nodes := allFin_NoDup _
  init_handlers := fun h => (elections_ghost_init, init_handlers h)
  net_handlers := refined_net_handlers
  input_handlers := refined_input_handlers

/-- `GhostSimulations.v:62-65` + `RaftRefinementInterface.v:160`
(`raft_refined_failure_params`): reboot resets the real state, PRESERVES
the ghost (history survives crashes — that is the point of a history
variable). -/
@[reducible] def raft_refined_failure_params :
    FailureParams (raft_refined_multi_params (P := P)) where
  reboot := fun st => (st.1, reboot st.2)

local notation "RaftNet" => Network (raft_base_params (P := P)) raft_multi_params
local notation "RaftPacket" => Packet (raft_base_params (P := P)) raft_multi_params
local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RefinedPacket" =>
  Packet (raft_refined_base_params (P := P)) raft_refined_multi_params

/-- `RaftRefinementInterface.v:166-209` — the refined twin of
`raft_intermediate_reachable`: closed under refined `step_failure` and
the four decomposed handler stages; the ghost is written exactly at the
`handleInput`/`handleMessage` stage and held fixed through
`doLeader`/`doGenericServer`. Constructor premises use pair projections
where Coq threads `nwState net h = (gd, d)` equations (design doc D2;
definitionally equivalent by pair eta, and the style of the sibling
`RIR_doLeader`). -/
inductive refined_raft_intermediate_reachable : RefinedNet → Prop
  | RRIR_init : refined_raft_intermediate_reachable (step_async_init _ _)
  | RRIR_step_failure :
      ∀ failed (net : RefinedNet) failed' net' out,
        refined_raft_intermediate_reachable net →
        step_failure _ _ raft_refined_failure_params (failed, net) (failed', net') out →
        refined_raft_intermediate_reachable net'
  | RRIR_handleInput :
      ∀ (net : RefinedNet) (h : name (P := P)) inp out d l ps' st',
        refined_raft_intermediate_reachable net →
        handleInput h inp (net.nwState h).2 = (out, d, l) →
        (∀ h', st' h' = update net.nwState h
          (update_elections_data_input h inp (net.nwState h), d) h') →
        (∀ p', p' ∈ ps' → p' ∈ net.nwPackets ∨ p' ∈ send_packets h l) →
        refined_raft_intermediate_reachable ⟨ps', st'⟩
  | RRIR_handleMessage :
      ∀ (p : RefinedPacket) (net : RefinedNet) xs ys st' ps' d l,
        refined_raft_intermediate_reachable net →
        handleMessage p.pSrc p.pDst p.pBody (net.nwState p.pDst).2 = (d, l) →
        net.nwPackets = xs ++ p :: ys →
        (∀ h, st' h = update net.nwState p.pDst
          (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d) h) →
        (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨ p' ∈ send_packets p.pDst l) →
        refined_raft_intermediate_reachable ⟨ps', st'⟩
  | RRIR_doLeader :
      ∀ (net : RefinedNet) st' ps' (h : name (P := P)) os d' ms,
        refined_raft_intermediate_reachable net →
        doLeader (net.nwState h).2 h = (os, d', ms) →
        (∀ h', st' h' = update net.nwState h ((net.nwState h).1, d') h') →
        (∀ q, q ∈ ps' → q ∈ net.nwPackets ∨ q ∈ send_packets h ms) →
        refined_raft_intermediate_reachable ⟨ps', st'⟩
  | RRIR_doGenericServer :
      ∀ (net : RefinedNet) st' ps' (h : name (P := P)) os d' ms,
        refined_raft_intermediate_reachable net →
        doGenericServer h (net.nwState h).2 = (os, d', ms) →
        (∀ h', st' h' = update net.nwState h ((net.nwState h).1, d') h') →
        (∀ q, q ∈ ps' → q ∈ net.nwPackets ∨ q ∈ send_packets h ms) →
        refined_raft_intermediate_reachable ⟨ps', st'⟩

end RefinedProofStructure

end Raft
end VerdiCompat
