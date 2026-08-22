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

/-! ## The eleven obligation shapes

`RaftRefinementInterface.v:211-325`. Premise shapes kept 1:1 with
upstream (explicit `gd` with its defining equation — design doc D2):
these are the interfaces the chain proofs instantiate. -/

/-- `RaftRefinementInterface.v:211-220` -/
def refined_raft_net_invariant_client_request (Pr : RefinedNet → Prop) : Prop :=
  ∀ (h : name (P := P)) (net : RefinedNet) st' ps' gd out d l client id c,
    handleClientRequest h (net.nwState h).2 client id c = (out, d, l) →
    gd = update_elections_data_client_request h (net.nwState h) client id c →
    Pr net →
    refined_raft_intermediate_reachable net →
    (∀ h', st' h' = update net.nwState h (gd, d) h') →
    (∀ p', p' ∈ ps' → p' ∈ net.nwPackets ∨ p' ∈ send_packets h l) →
    Pr ⟨ps', st'⟩

/-- `RaftRefinementInterface.v:222-231` -/
def refined_raft_net_invariant_timeout (Pr : RefinedNet → Prop) : Prop :=
  ∀ (net : RefinedNet) (h : name (P := P)) st' ps' gd out d l,
    handleTimeout h (net.nwState h).2 = (out, d, l) →
    gd = update_elections_data_timeout h (net.nwState h) →
    Pr net →
    refined_raft_intermediate_reachable net →
    (∀ h', st' h' = update net.nwState h (gd, d) h') →
    (∀ p', p' ∈ ps' → p' ∈ net.nwPackets ∨ p' ∈ send_packets h l) →
    Pr ⟨ps', st'⟩

/-- `RaftRefinementInterface.v:233-244` -/
def refined_raft_net_invariant_append_entries (Pr : RefinedNet → Prop) : Prop :=
  ∀ xs (p : RefinedPacket) ys (net : RefinedNet) st' ps' gd d m t n pli plt es ci,
    handleAppendEntries p.pDst (net.nwState p.pDst).2 t n pli plt es ci = (d, m) →
    gd = update_elections_data_appendEntries p.pDst (net.nwState p.pDst) t n pli plt es ci →
    p.pBody = .AppendEntries t n pli plt es ci →
    Pr net →
    refined_raft_intermediate_reachable net →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst (gd, d) h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨ p' = (⟨p.pDst, p.pSrc, m⟩ : RefinedPacket)) →
    Pr ⟨ps', st'⟩

/-- `RaftRefinementInterface.v:246-257` — note the ghost is UNCHANGED on
an AppendEntriesReply (`gd = fst`). -/
def refined_raft_net_invariant_append_entries_reply (Pr : RefinedNet → Prop) : Prop :=
  ∀ xs (p : RefinedPacket) ys (net : RefinedNet) st' ps' gd d m t es res,
    handleAppendEntriesReply p.pDst (net.nwState p.pDst).2 p.pSrc t es res = (d, m) →
    gd = (net.nwState p.pDst).1 →
    p.pBody = .AppendEntriesReply t es res →
    Pr net →
    refined_raft_intermediate_reachable net →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst (gd, d) h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨ p' ∈ send_packets p.pDst m) →
    Pr ⟨ps', st'⟩

/-- `RaftRefinementInterface.v:259-270` -/
def refined_raft_net_invariant_request_vote (Pr : RefinedNet → Prop) : Prop :=
  ∀ xs (p : RefinedPacket) ys (net : RefinedNet) st' ps' gd d m t cid lli llt,
    handleRequestVote p.pDst (net.nwState p.pDst).2 t p.pSrc lli llt = (d, m) →
    gd = update_elections_data_requestVote p.pDst p.pSrc t p.pSrc lli llt
      (net.nwState p.pDst) →
    p.pBody = .RequestVote t cid lli llt →
    Pr net →
    refined_raft_intermediate_reachable net →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst (gd, d) h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨ p' = (⟨p.pDst, p.pSrc, m⟩ : RefinedPacket)) →
    Pr ⟨ps', st'⟩

/-- `RaftRefinementInterface.v:272-282` -/
def refined_raft_net_invariant_request_vote_reply (Pr : RefinedNet → Prop) : Prop :=
  ∀ xs (p : RefinedPacket) ys (net : RefinedNet) st' ps' gd d t v,
    handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t v = d →
    gd = update_elections_data_requestVoteReply p.pDst p.pSrc t v (net.nwState p.pDst) →
    p.pBody = .RequestVoteReply t v →
    Pr net →
    refined_raft_intermediate_reachable net →
    net.nwPackets = xs ++ p :: ys →
    (∀ h, st' h = update net.nwState p.pDst (gd, d) h) →
    (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys)) →
    Pr ⟨ps', st'⟩

/-- `RaftRefinementInterface.v:284-293` — the ghost rides along unchanged
through `doLeader`. -/
def refined_raft_net_invariant_do_leader (Pr : RefinedNet → Prop) : Prop :=
  ∀ (net : RefinedNet) st' ps' gd d (h : name (P := P)) os d' ms,
    doLeader d h = (os, d', ms) →
    Pr net →
    refined_raft_intermediate_reachable net →
    net.nwState h = (gd, d) →
    (∀ h', st' h' = update net.nwState h (gd, d') h') →
    (∀ q, q ∈ ps' → q ∈ net.nwPackets ∨ q ∈ send_packets h ms) →
    Pr ⟨ps', st'⟩

/-- `RaftRefinementInterface.v:295-304` -/
def refined_raft_net_invariant_do_generic_server (Pr : RefinedNet → Prop) : Prop :=
  ∀ (net : RefinedNet) st' ps' gd d os d' ms (h : name (P := P)),
    doGenericServer h d = (os, d', ms) →
    Pr net →
    refined_raft_intermediate_reachable net →
    net.nwState h = (gd, d) →
    (∀ h', st' h' = update net.nwState h (gd, d') h') →
    (∀ q, q ∈ ps' → q ∈ net.nwPackets ∨ q ∈ send_packets h ms) →
    Pr ⟨ps', st'⟩

/-- `RaftRefinementInterface.v:306-312` -/
def refined_raft_net_invariant_state_same_packet_subset (Pr : RefinedNet → Prop) : Prop :=
  ∀ net net' : RefinedNet,
    (∀ h, net.nwState h = net'.nwState h) →
    (∀ q, q ∈ net'.nwPackets → q ∈ net.nwPackets) →
    Pr net →
    refined_raft_intermediate_reachable net →
    Pr net'

/-- `RaftRefinementInterface.v:314-322` — reboot resets the real state
and PRESERVES the ghost. -/
def refined_raft_net_invariant_reboot (Pr : RefinedNet → Prop) : Prop :=
  ∀ (net net' : RefinedNet) gd d (h : name (P := P)) d',
    reboot d = d' →
    Pr net →
    refined_raft_intermediate_reachable net →
    net.nwState h = (gd, d) →
    (∀ h', net'.nwState h' = update net.nwState h (gd, d') h') →
    net.nwPackets = net'.nwPackets →
    Pr net'

/-- `RaftRefinementInterface.v:324-325` -/
def refined_raft_net_invariant_init (Pr : RefinedNet → Prop) : Prop :=
  Pr (step_async_init _ _)

/-- `RaftRefinementProof.v:10-35` — dispatch a `handleMessage` step (ghost
written by `update_elections_data_net`) to the per-message obligations. -/
theorem refined_raft_invariant_handle_message {Pr : RefinedNet → Prop}
    (hae : refined_raft_net_invariant_append_entries Pr)
    (haer : refined_raft_net_invariant_append_entries_reply Pr)
    (hrv : refined_raft_net_invariant_request_vote Pr)
    (hrvr : refined_raft_net_invariant_request_vote_reply Pr) :
    ∀ xs (p : RefinedPacket) ys (net : RefinedNet) st' ps' d l,
      handleMessage p.pSrc p.pDst p.pBody (net.nwState p.pDst).2 = (d, l) →
      Pr net →
      refined_raft_intermediate_reachable net →
      net.nwPackets = xs ++ p :: ys →
      (∀ h, st' h = update net.nwState p.pDst
        (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d) h) →
      (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨ p' ∈ send_packets p.pDst l) →
      Pr ⟨ps', st'⟩ := by
  intro xs p ys net st' ps' d l hm hP hreach hpkts hst hps
  unfold handleMessage at hm
  cases hbody : p.pBody with
  | AppendEntries t lid pli plt es ci =>
    rw [hbody] at hm
    simp only [] at hm
    rcases hh : handleAppendEntries p.pDst (net.nwState p.pDst).2 t lid pli plt es ci
      with ⟨d0, r0⟩
    rw [hh] at hm
    simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact hae xs p ys net st' ps' (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst)) d0 r0 t lid pli plt es ci hh
      (by rw [hbody]; rfl) hbody hP hreach hpkts hst
      (fun p' hp' => by
        rcases hps p' hp' with h | h
        · exact Or.inl h
        · right
          have h' : p' ∈ [(⟨p.pDst, p.pSrc, r0⟩ : RefinedPacket)] := h
          simpa using h')
  | AppendEntriesReply t es res =>
    rw [hbody] at hm
    simp only [] at hm
    exact haer xs p ys net st' ps' (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst)) d l t es res hm
      (by rw [hbody]; rfl) hbody hP hreach hpkts hst hps
  | RequestVote t cid lli llt =>
    rw [hbody] at hm
    simp only [] at hm
    rcases hh : handleRequestVote p.pDst (net.nwState p.pDst).2 t p.pSrc lli llt
      with ⟨d0, r0⟩
    rw [hh] at hm
    simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact hrv xs p ys net st' ps' (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst)) d0 r0 t cid lli llt hh
      (by rw [hbody]; rfl) hbody hP hreach hpkts hst
      (fun p' hp' => by
        rcases hps p' hp' with h | h
        · exact Or.inl h
        · right
          have h' : p' ∈ [(⟨p.pDst, p.pSrc, r0⟩ : RefinedPacket)] := h
          simpa using h')
  | RequestVoteReply t v =>
    rw [hbody] at hm
    simp only [] at hm
    simp only [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact hrvr xs p ys net st' ps' (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst)) _ t v rfl
      (by rw [hbody]; rfl) hbody hP hreach hpkts hst
      (fun p' hp' => by
        rcases hps p' hp' with h | h
        · exact h
        · simp [send_packets] at h)

/-- `RaftRefinementProof.v:37-55` — dispatch a `handleInput` step (ghost
written by `update_elections_data_input`). -/
theorem refined_raft_invariant_handle_input {Pr : RefinedNet → Prop}
    (hto : refined_raft_net_invariant_timeout Pr)
    (hcr : refined_raft_net_invariant_client_request Pr) :
    ∀ (h : name (P := P)) inp (net : RefinedNet) st' ps' out d l,
      handleInput h inp (net.nwState h).2 = (out, d, l) →
      Pr net →
      refined_raft_intermediate_reachable net →
      (∀ h', st' h' = update net.nwState h
        (update_elections_data_input h inp (net.nwState h), d) h') →
      (∀ p', p' ∈ ps' → p' ∈ net.nwPackets ∨ p' ∈ send_packets h l) →
      Pr ⟨ps', st'⟩ := by
  intro h inp net st' ps' out d l hi hP hreach hst hps
  unfold handleInput at hi
  cases inp with
  | Timeout => exact hto net h st' ps' _ out d l hi rfl hP hreach hst hps
  | ClientRequest client id c =>
    exact hcr h net st' ps' _ out d l client id c hi rfl hP hreach hst hps

/-- `RaftRefinementInterface.v:522-538` / `RaftRefinementProof.v:56-194` —
THE ghost-layer induction principle: an invariant holds of every
`refined_raft_intermediate_reachable` network if it is preserved by each
handler step with its ghost update (plus init, packet-subset, and reboot
obligations). ~73 of verdi-raft's 90 RaftProofs files instantiate exactly
this. Re-proved from scratch (the Coq proof is 140 lines of Ltac). -/
theorem refined_raft_net_invariant {Pr : RefinedNet → Prop}
    (hinit : refined_raft_net_invariant_init Pr)
    (hcr : refined_raft_net_invariant_client_request Pr)
    (hto : refined_raft_net_invariant_timeout Pr)
    (hae : refined_raft_net_invariant_append_entries Pr)
    (haer : refined_raft_net_invariant_append_entries_reply Pr)
    (hrv : refined_raft_net_invariant_request_vote Pr)
    (hrvr : refined_raft_net_invariant_request_vote_reply Pr)
    (hdl : refined_raft_net_invariant_do_leader Pr)
    (hgs : refined_raft_net_invariant_do_generic_server Pr)
    (hsub : refined_raft_net_invariant_state_same_packet_subset Pr)
    (hreb : refined_raft_net_invariant_reboot Pr) :
    ∀ net, refined_raft_intermediate_reachable (P := P) net → Pr net := by
  intro net hreach
  induction hreach with
  | RRIR_init => exact hinit
  | RRIR_handleInput net h inp out d l ps' st' hreach hi hst hps ih =>
    exact refined_raft_invariant_handle_input hto hcr h inp net st' ps' out d l
      hi ih hreach hst hps
  | RRIR_handleMessage p net xs ys st' ps' d l hreach hm hpkts hst hps ih =>
    exact refined_raft_invariant_handle_message hae haer hrv hrvr xs p ys net st' ps'
      d l hm ih hreach hpkts hst hps
  | RRIR_doLeader net st' ps' h os d' ms hreach hdo hst hps ih =>
    exact hdl net st' ps' _ _ h os d' ms hdo ih hreach rfl hst hps
  | RRIR_doGenericServer net st' ps' h os d' ms hreach hdo hst hps ih =>
    exact hgs net st' ps' _ _ os d' ms h hdo ih hreach rfl hst hps
  | RRIR_step_failure failed net failed' net' out hreach hstep ih =>
    cases hstep with
    | StepFailure_deliver net _ failed p xs ys out' dfull l hpkts hlive hnh hnet' =>
      -- decompose refined RaftNetHandler = handleMessage ; doLeader ;
      -- doGenericServer, ghost written once at the handleMessage stage
      rcases hm : handleMessage p.pSrc p.pDst p.pBody (net.nwState p.pDst).2
        with ⟨d0, l0⟩
      rcases hl : doLeader d0 p.pDst with ⟨o1, d1, l1⟩
      rcases hg : doGenericServer p.pDst d1 with ⟨o2, d2, l2⟩
      have hnh' : (o1 ++ o2,
          ((update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d2) :
            electionsData (P := P) × raft_data (P := P)),
          l0 ++ l1 ++ l2) = (out', dfull, l) := by
        have hnh : refined_net_handlers p.pDst p.pSrc p.pBody (net.nwState p.pDst)
            = (out', dfull, l) := hnh
        unfold refined_net_handlers RaftNetHandler at hnh
        rw [hm] at hnh
        simp only [] at hnh
        rw [hl] at hnh
        simp only [] at hnh
        rw [hg] at hnh
        simpa using hnh
      simp only [Prod.mk.injEq] at hnh'
      obtain ⟨-, rfl, rfl⟩ := hnh'
      subst hnet'
      -- intermediate reachable states, mirroring the Coq assert chain
      have hnet1 : refined_raft_intermediate_reachable (P := P)
          ⟨(xs ++ ys) ++ send_packets p.pDst l0,
           update net.nwState p.pDst
             (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d0)⟩ :=
        .RRIR_handleMessage p net xs ys _ _ d0 l0 hreach hm hpkts (fun _ => rfl)
          (fun p' hp' => by simpa using (List.mem_append.mp hp'))
      have hstate1 : (update net.nwState p.pDst
          (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d0))
            p.pDst
          = (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d0) :=
        update_same ..
      have hnet2 : refined_raft_intermediate_reachable (P := P)
          ⟨((xs ++ ys) ++ send_packets p.pDst l0) ++ send_packets p.pDst l1,
           update (update net.nwState p.pDst
               (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d0))
             p.pDst
             (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d1)⟩ :=
        .RRIR_doLeader ⟨(xs ++ ys) ++ send_packets p.pDst l0,
            update net.nwState p.pDst
              (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d0)⟩
          _ _ p.pDst o1 d1 l1 hnet1
          (by show doLeader (update net.nwState p.pDst
                (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d0)
                p.pDst).2 p.pDst = (o1, d1, l1)
              rw [hstate1]; exact hl)
          (fun h' => by simp only [update_same])
          (fun q hq => by simpa using (List.mem_append.mp hq))
      -- Pr net1 via the message dispatcher
      have hP1 : Pr ⟨(xs ++ ys) ++ send_packets p.pDst l0,
          update net.nwState p.pDst
            (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d0)⟩ :=
        refined_raft_invariant_handle_message hae haer hrv hrvr xs p ys net _ _ d0 l0
          hm ih hreach hpkts (fun _ => rfl)
          (fun p' hp' => List.mem_append.mp hp')
      -- Pr net2 via the do_leader obligation (ghost rides along)
      have hP2 : Pr ⟨((xs ++ ys) ++ send_packets p.pDst l0) ++ send_packets p.pDst l1,
          update (update net.nwState p.pDst
              (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d0))
            p.pDst
            (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d1)⟩ :=
        hdl ⟨(xs ++ ys) ++ send_packets p.pDst l0,
            update net.nwState p.pDst
              (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d0)⟩
          _ _ _ d0 p.pDst o1 d1 l1 hl hP1 hnet1 hstate1
          (fun h' => by rw [update_update_same])
          (fun q hq => List.mem_append.mp hq)
      -- conclude via the do_generic_server obligation on net2
      refine hgs ⟨((xs ++ ys) ++ send_packets p.pDst l0) ++ send_packets p.pDst l1,
          update (update net.nwState p.pDst
              (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d0))
            p.pDst
            (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst), d1)⟩
        _ _ (update_elections_data_net p.pDst p.pSrc p.pBody (net.nwState p.pDst)) d1
        o2 d2 l2 p.pDst hg hP2 hnet2 (by simp) ?_ ?_
      · intro h'
        simp only [update_update_same]
      · intro q hq
        rw [send_packets_app, send_packets_app] at hq
        simp only [List.mem_append] at hq ⊢
        -- hq : (((l0 ∨ l1) ∨ l2) ∨ xs) ∨ ys ; ⊢ (((xs ∨ ys) ∨ l0) ∨ l1) ∨ l2
        rcases hq with (((h | h) | h) | h) | h
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
        · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    | StepFailure_input h net _ failed out' inp dfull l hlive hih hnet' =>
      rcases hi : handleInput h inp (net.nwState h).2 with ⟨o0, d0, l0⟩
      rcases hl : doLeader d0 h with ⟨o1, d1, l1⟩
      rcases hg : doGenericServer h d1 with ⟨o2, d2, l2⟩
      have hih' : (o0 ++ o1 ++ o2,
          ((update_elections_data_input h inp (net.nwState h), d2) :
            electionsData (P := P) × raft_data (P := P)),
          l0 ++ l1 ++ l2) = (out', dfull, l) := by
        have hih : refined_input_handlers h inp (net.nwState h) = (out', dfull, l) := hih
        unfold refined_input_handlers RaftInputHandler at hih
        rw [hi] at hih
        simp only [] at hih
        rw [hl] at hih
        simp only [] at hih
        rw [hg] at hih
        simpa using hih
      simp only [Prod.mk.injEq] at hih'
      obtain ⟨-, rfl, rfl⟩ := hih'
      subst hnet'
      have hnet1 : refined_raft_intermediate_reachable (P := P)
          ⟨net.nwPackets ++ send_packets h l0,
           update net.nwState h (update_elections_data_input h inp (net.nwState h), d0)⟩ :=
        .RRIR_handleInput net h inp o0 d0 l0 _ _ hreach hi (fun _ => rfl)
          (fun p' hp' => List.mem_append.mp hp')
      have hstate1 : (update net.nwState h
            (update_elections_data_input h inp (net.nwState h), d0)) h
          = (update_elections_data_input h inp (net.nwState h), d0) := update_same ..
      have hnet2 : refined_raft_intermediate_reachable (P := P)
          ⟨(net.nwPackets ++ send_packets h l0) ++ send_packets h l1,
           update (update net.nwState h
               (update_elections_data_input h inp (net.nwState h), d0)) h
             (update_elections_data_input h inp (net.nwState h), d1)⟩ :=
        .RRIR_doLeader ⟨net.nwPackets ++ send_packets h l0,
            update net.nwState h (update_elections_data_input h inp (net.nwState h), d0)⟩
          _ _ h o1 d1 l1 hnet1
          (by show doLeader (update net.nwState h
                (update_elections_data_input h inp (net.nwState h), d0) h).2 h
                = (o1, d1, l1)
              rw [hstate1]; exact hl)
          (fun h' => by simp only [update_same])
          (fun q hq => List.mem_append.mp hq)
      have hP1 : Pr ⟨net.nwPackets ++ send_packets h l0,
          update net.nwState h (update_elections_data_input h inp (net.nwState h), d0)⟩ :=
        refined_raft_invariant_handle_input hto hcr h inp net _ _ o0 d0 l0 hi ih hreach
          (fun _ => rfl) (fun p' hp' => List.mem_append.mp hp')
      have hP2 : Pr ⟨(net.nwPackets ++ send_packets h l0) ++ send_packets h l1,
          update (update net.nwState h
              (update_elections_data_input h inp (net.nwState h), d0)) h
            (update_elections_data_input h inp (net.nwState h), d1)⟩ :=
        hdl ⟨net.nwPackets ++ send_packets h l0,
            update net.nwState h (update_elections_data_input h inp (net.nwState h), d0)⟩
          _ _ _ d0 h o1 d1 l1 hl hP1 hnet1 hstate1
          (fun h' => by rw [update_update_same])
          (fun q hq => List.mem_append.mp hq)
      refine hgs ⟨(net.nwPackets ++ send_packets h l0) ++ send_packets h l1,
          update (update net.nwState h
              (update_elections_data_input h inp (net.nwState h), d0)) h
            (update_elections_data_input h inp (net.nwState h), d1)⟩
        _ _ (update_elections_data_input h inp (net.nwState h)) d1
        o2 d2 l2 h hg hP2 hnet2 (by simp) ?_ ?_
      · intro h'
        simp only [update_update_same]
      · intro q hq
        rw [send_packets_app, send_packets_app] at hq
        simp only [List.mem_append] at hq ⊢
        -- hq : ((l0 ∨ l1) ∨ l2) ∨ pk ; ⊢ ((pk ∨ l0) ∨ l1) ∨ l2
        rcases hq with ((h' | h') | h') | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
        · exact Or.inl (Or.inl (Or.inl h'))
    | StepFailure_drop net _ failed p xs ys hpkts hnet' =>
      subst hnet'
      refine hsub net _ (fun _ => rfl) (fun q hq => ?_) ih hreach
      rw [hpkts]
      simp only [List.mem_append, List.mem_cons] at hq ⊢
      rcases hq with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    | StepFailure_dup net _ failed p xs ys hpkts hnet' =>
      subst hnet'
      refine hsub net _ (fun _ => rfl) (fun q hq => ?_) ih hreach
      rw [hpkts]
      simp only [List.mem_append, List.mem_cons] at hq ⊢
      -- hq : (q = p ∨ q ∈ xs) ∨ (q = p ∨ q ∈ ys) ; ⊢ q ∈ xs ∨ q = p ∨ q ∈ ys
      rcases hq with (h | h) | (h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    | StepFailure_fail h net failed => exact ih
    | StepFailure_reboot h net _ failed failed' hmem hfailed' hnet' =>
      subst hnet'
      exact hreb net _ (net.nwState h).1 (net.nwState h).2 h _ rfl ih hreach rfl
        (fun _ => rfl) rfl

end RefinedProofStructure

end Raft
end VerdiCompat
