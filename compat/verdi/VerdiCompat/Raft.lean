import VerdiCompat.Net
import VerdiCompat.RaftState

/-!
# verdi-raft's Raft protocol spec

1:1 port of `deps/verdi-raft/theories/Raft/Raft.v:9-554`: the parameter
class, wire types, log utilities, every handler, the composed
`RaftNetHandler`/`RaftInputHandler`, `reboot`/`init_handlers`, the three
Verdi instances, and `raft_intermediate_reachable` (the reachability
predicate the safety theorem is stated over). Each definition cites its
source lines. The `raft_net_invariant_*` induction principle
(`Raft.v:594-848`) is ported and re-proved in `ProofStructure.lean`.

Boolean-comparison notations mirror Coq's (`Raft.v:29-34`): the spec's
comparisons are BOOLEAN (`Nat.blt` etc.), not propositional, and stay
that way here.
-/

namespace VerdiCompat

/-- `Raft.v:9-16` -/
class RaftParams (orig_base_params : BaseParams) where
  N : Nat
  [input_eq_dec : DecidableEq orig_base_params.input]
  [output_eq_dec : DecidableEq orig_base_params.output]
  clientId : Type
  [clientId_eq_dec : DecidableEq clientId]

@[reducible] instance {P : BaseParams} [R : RaftParams P] : DecidableEq P.input :=
  R.input_eq_dec
@[reducible] instance {P : BaseParams} [R : RaftParams P] : DecidableEq P.output :=
  R.output_eq_dec
@[reducible] instance {P : BaseParams} [R : RaftParams P] : DecidableEq R.clientId :=
  R.clientId_eq_dec

namespace Raft

/-- `Raft.v:29` (`a >? b := b <? a`) -/
scoped notation:50 a:51 " >? " b:51 => Nat.blt b a
/-- `Raft.v:30` -/
scoped notation:50 a:51 " >=? " b:51 => Nat.ble b a
scoped notation:50 a:51 " <? " b:51 => Nat.blt a b
scoped notation:50 a:51 " <=? " b:51 => Nat.ble a b

section RaftSection

variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

/-- `Raft.v:23` -/
abbrev term := Nat
/-- `Raft.v:24` -/
abbrev logIndex := Nat
/-- `Raft.v:25`. StructTact `fin N` ↦ Lean `Fin N` (see `allFin`). -/
abbrev name := Fin (RaftParams.N P)
/-- `Raft.v:26` -/
def nodes : List (name (P := P)) := allFin _

/-- `Raft.v:36-43` -/
structure entry where
  eAt : name (P := P)
  eClient : R.clientId
  eId : Nat
  eIndex : logIndex
  eTerm : term
  eInput : P.input
deriving DecidableEq

/-- `Raft.v:45-49` -/
inductive msg where
  | RequestVote : term → name (P := P) → logIndex → term → msg
  | RequestVoteReply : term → Bool → msg
  | AppendEntries : term → name (P := P) → logIndex → term → List (entry (P := P)) → logIndex → msg
  | AppendEntriesReply : term → List (entry (P := P)) → Bool → msg
deriving DecidableEq

/-- `Raft.v:51-53` -/
inductive raft_input where
  | Timeout : raft_input
  | ClientRequest : R.clientId → Nat → P.input → raft_input
deriving DecidableEq

/-- `Raft.v:55-57` -/
inductive raft_output where
  | NotLeader : R.clientId → Nat → raft_output
  | ClientResponse : R.clientId → Nat → P.output → raft_output
deriving DecidableEq

/-- `Raft.v:59-62` -/
inductive serverType where
  | Follower
  | Candidate
  | Leader
deriving DecidableEq

/-- `Raft.v:80-81` -/
abbrev raft_data :=
  RaftData term (name (P := P)) (entry (P := P)) logIndex serverType
    P.data R.clientId P.output

/-- `Raft.v:99-109`. The log is stored NEWEST-FIRST; lookup walks down
past larger indices and gives up early once below `i`. -/
def findAtIndex : List (entry (P := P)) → logIndex → Option (entry (P := P))
  | [], _ => none
  | e :: es, i =>
    if e.eIndex == i then some e
    else if e.eIndex <? i then none
    else findAtIndex es i

/-- `Raft.v:111-118` -/
def findGtIndex : List (entry (P := P)) → logIndex → List (entry (P := P))
  | [], _ => []
  | e :: es, i =>
    if e.eIndex >? i then e :: findGtIndex es i
    else []

/-- `Raft.v:120-127` -/
def removeAfterIndex : List (entry (P := P)) → logIndex → List (entry (P := P))
  | [], _ => []
  | e :: es, i =>
    if e.eIndex <=? i then e :: es
    else removeAfterIndex es i

/-- `Raft.v:129-133` (head of the newest-first log) -/
def maxIndex : List (entry (P := P)) → logIndex
  | [] => 0
  | e :: _ => e.eIndex

/-- `Raft.v:135-139` -/
def maxTerm : List (entry (P := P)) → term
  | [] => 0
  | e :: _ => e.eTerm

/-- `Raft.v:141-148` -/
def advanceCurrentTerm (state : raft_data (P := P)) (newTerm : term) :
    raft_data (P := P) :=
  if newTerm >? state.currentTerm then
    { state with currentTerm := newTerm, votedFor := none,
                 type := .Follower, leaderId := none }
  else state

/-- `Raft.v:150-151` -/
def getNextIndex (state : raft_data (P := P)) (h : name (P := P)) : logIndex :=
  assoc_default state.nextIndex h (maxIndex state.log)

/-- `Raft.v:153-169` -/
def tryToBecomeLeader (me : name (P := P)) (state : raft_data (P := P)) :
    List (raft_output (P := P)) × raft_data (P := P) × List (name (P := P) × msg (P := P)) :=
  let t := state.currentTerm + 1
  ([],
   { state with type := .Candidate, votedFor := some me,
                votesReceived := [me], currentTerm := t },
   (nodes.filter fun h => if me = h then false else true).map
     fun node => (node, .RequestVote t me (maxIndex state.log) (maxTerm state.log)))

/-- `Raft.v:171-175` -/
def not_empty {A : Type} : List A → Bool
  | [] => false
  | _ => true

/-- `Raft.v:177-181` -/
def haveNewEntries (state : raft_data (P := P)) (entries : List (entry (P := P))) : Bool :=
  not_empty entries &&
    (match findAtIndex state.log (maxIndex entries) with
     | none => true
     | some e => !(maxTerm entries == e.eTerm))

/-- `Raft.v:183-222` -/
def handleAppendEntries (_me : name (P := P)) (state : raft_data (P := P))
    (t : term) (leaderId : name (P := P)) (prevLogIndex : logIndex)
    (prevLogTerm : term) (entries : List (entry (P := P))) (leaderCommit : logIndex) :
    raft_data (P := P) × msg (P := P) :=
  if state.currentTerm >? t then
    (state, .AppendEntriesReply state.currentTerm entries false)
  else if prevLogIndex == 0 then
    if haveNewEntries state entries then
      ({ advanceCurrentTerm state t with
           log := entries,
           commitIndex := max state.commitIndex (min leaderCommit (maxIndex entries)),
           type := .Follower, leaderId := some leaderId },
       .AppendEntriesReply t entries true)
    else
      ({ advanceCurrentTerm state t with type := .Follower, leaderId := some leaderId },
       .AppendEntriesReply t entries true)
  else
    match findAtIndex state.log prevLogIndex with
    | none => (state, .AppendEntriesReply state.currentTerm entries false)
    | some e =>
      if !(prevLogTerm == e.eTerm) then
        (state, .AppendEntriesReply state.currentTerm entries false)
      else if haveNewEntries state entries then
        let log' := removeAfterIndex state.log prevLogIndex
        let log'' := entries ++ log'
        ({ advanceCurrentTerm state t with
             log := log'',
             commitIndex := max state.commitIndex (min leaderCommit (maxIndex log'')),
             type := .Follower, leaderId := some leaderId },
         .AppendEntriesReply t entries true)
      else
        ({ advanceCurrentTerm state t with type := .Follower, leaderId := some leaderId },
         .AppendEntriesReply t entries true)

/-- `Raft.v:224-249`. Note the single-step `nextIndex` backoff via `pred`
(`Raft.v:241`) — a recorded delta vs etcd-io/raft's fast conflict backoff. -/
def handleAppendEntriesReply (_me : name (P := P)) (state : raft_data (P := P))
    (src : name (P := P)) (t : term) (entries : List (entry (P := P))) (result : Bool) :
    raft_data (P := P) × List (name (P := P) × msg (P := P)) :=
  if state.currentTerm == t then
    if result then
      let index := maxIndex entries
      ({ state with
           matchIndex := assoc_set state.matchIndex src
             (max (assoc_default state.matchIndex src 0) index),
           nextIndex := assoc_set state.nextIndex src
             (max (getNextIndex state src) (index + 1)) },
       [])
    else
      ({ state with
           nextIndex := assoc_set state.nextIndex src
             (Nat.pred (getNextIndex state src)) },
       [])
  else if state.currentTerm <? t then
    -- leader behind, convert to follower
    (advanceCurrentTerm state t, [])
  else
    -- follower behind, ignore
    (state, [])

/-- `Raft.v:251` -/
def moreUpToDate (t1 i1 t2 i2 : Nat) : Bool :=
  (t1 >? t2) || ((t1 == t2) && (i1 >=? i2))

/-- `Raft.v:253-268`. `Raft.v:258`'s Coq `if leaderId state then false else
true` is an option-match: true iff no known leader — the "sticky leader"
vote guard, a recorded deviation from the Raft paper. -/
def handleRequestVote (_me : name (P := P)) (state : raft_data (P := P))
    (t : term) (candidateId : name (P := P)) (lastLogIndex : logIndex)
    (lastLogTerm : term) : raft_data (P := P) × msg (P := P) :=
  if state.currentTerm >? t then
    (state, .RequestVoteReply state.currentTerm false)
  else
    let state := advanceCurrentTerm state t
    if state.leaderId.isNone &&
       moreUpToDate lastLogTerm lastLogIndex (maxTerm state.log) (maxIndex state.log) then
      match state.votedFor with
      | none =>
        ({ state with votedFor := some candidateId },
         .RequestVoteReply state.currentTerm true)
      | some candidateId' =>
        (state, .RequestVoteReply state.currentTerm (decide (candidateId = candidateId')))
    else
      (state, .RequestVoteReply state.currentTerm false)

/-- `Raft.v:270-275` (their own fixpoint, kept verbatim rather than mapped
to `Nat.div2`) -/
def div2 : Nat → Nat
  | n + 2 => div2 n + 1
  | 1 => 0
  | 0 => 0

/-- `Raft.v:277-278` -/
def wonElection (votes : List (name (P := P))) : Bool :=
  div2 (nodes (P := P)).length + 1 <=? votes.length

/-- `Raft.v:280-305` -/
def handleRequestVoteReply (me : name (P := P)) (state : raft_data (P := P))
    (src : name (P := P)) (t : term) (voteGranted : Bool) : raft_data (P := P) :=
  if t >? state.currentTerm then
    { advanceCurrentTerm state t with type := .Follower }
  else if t <? state.currentTerm then state
  else
    let won := voteGranted &&
      wonElection (dedup (src :: state.votesReceived))
    match state.type with
    | .Candidate =>
      { state with
          votesReceived := (if voteGranted then [src] else []) ++ state.votesReceived,
          type := if won then .Leader else state.type,  -- long live the king
          matchIndex := assoc_set [] me (maxIndex state.log),
          nextIndex := [],
          electoralVictories :=
            (if won then [(state.currentTerm, src :: state.votesReceived, state.log)]
             else []) ++ state.electoralVictories }
    | _ => state

/-- `Raft.v:307-323` -/
def handleMessage (src me : name (P := P)) (m : msg (P := P))
    (state : raft_data (P := P)) :
    raft_data (P := P) × List (name (P := P) × msg (P := P)) :=
  match m with
  | .AppendEntries t lid prevLogIndex prevLogTerm entries leaderCommit =>
    let (st, r) := handleAppendEntries me state t lid prevLogIndex prevLogTerm entries leaderCommit
    (st, [(src, r)])
  | .AppendEntriesReply t entries result =>
    handleAppendEntriesReply me state src t entries result
  | .RequestVote t _candidateId lastLogIndex lastLogTerm =>
    let (st, r) := handleRequestVote me state t src lastLogIndex lastLogTerm
    (st, [(src, r)])
  | .RequestVoteReply t voteGranted =>
    (handleRequestVoteReply me state src t voteGranted, [])

/-- `Raft.v:325-326` -/
def getLastId (state : raft_data (P := P)) (client : R.clientId) : Option (Nat × P.output) :=
  assoc state.clientCache client

/-- `Raft.v:328-331` — the only place the replicated `OneNodeParams`
machine is invoked. -/
def applyEntry (st : raft_data (P := P)) (e : entry (P := P)) :
    List P.output × raft_data (P := P) :=
  let (out, d) := O.handler e.eInput st.stateMachine
  ([out],
   { st with clientCache := assoc_set st.clientCache e.eClient (e.eId, out),
             stateMachine := d })

/-- `Raft.v:333-344` — client-session dedup cache. -/
def cacheApplyEntry (st : raft_data (P := P)) (e : entry (P := P)) :
    List P.output × raft_data (P := P) :=
  match getLastId st e.eClient with
  | some (id, o) =>
    if e.eId <? id then ([], st)
    else if e.eId == id then ([o], st)
    else applyEntry st e
  | none => applyEntry st e

/-- `Raft.v:346-357` -/
def applyEntries (h : name (P := P)) (st : raft_data (P := P)) :
    List (entry (P := P)) → List (raft_output (P := P)) × raft_data (P := P)
  | [] => ([], st)
  | e :: es =>
    let (out, st) := cacheApplyEntry st e
    let out : List (raft_output (P := P)) :=
      if e.eAt = h then out.map fun o => .ClientResponse e.eClient e.eId o
      else []
    let (out', state) := applyEntries h st es
    (out ++ out', state)

/-- `Raft.v:359-371` -/
def doGenericServer (h : name (P := P)) (state : raft_data (P := P)) :
    List (raft_output (P := P)) × raft_data (P := P) × List (name (P := P) × msg (P := P)) :=
  let (out, state') := applyEntries h state
    ((findGtIndex state.log state.lastApplied).filter
      (fun x => (state.lastApplied <? x.eIndex) && (x.eIndex <=? state.commitIndex))).reverse
  (out,
   { state' with lastApplied :=
       if state'.commitIndex >? state'.lastApplied then state'.commitIndex
       else state'.lastApplied },
   [])

/-- `Raft.v:373-381` -/
def replicaMessage (state : raft_data (P := P)) (me host : name (P := P)) :
    name (P := P) × msg (P := P) :=
  let prevIndex := Nat.pred (getNextIndex state host)
  let prevTerm :=
    match findAtIndex state.log prevIndex with
    | some e => e.eTerm
    | none => 0
  let newEntries := findGtIndex state.log prevIndex
  (host, .AppendEntries state.currentTerm me prevIndex prevTerm newEntries state.commitIndex)

/-- `Raft.v:383-384`. The parameter `N` shadows `RaftParams.N` exactly as
in the Coq source. -/
def haveQuorum (state : raft_data (P := P)) (_me : name (P := P)) (N : logIndex) : Bool :=
  div2 (nodes (P := P)).length <?
    (nodes.filter fun h => N <=? assoc_default state.matchIndex h 0).length

/-- `Raft.v:386-392` — commit advancement, guarded to current-term entries. -/
def advanceCommitIndex (state : raft_data (P := P)) (me : name (P := P)) :
    raft_data (P := P) :=
  let entriesToCommit :=
    (findGtIndex state.log state.commitIndex).filter fun e =>
      (state.currentTerm == e.eTerm) && (state.commitIndex <? e.eIndex) &&
      haveQuorum state me e.eIndex
  { state with commitIndex :=
      (entriesToCommit.map entry.eIndex).foldl max state.commitIndex }

/-- `Raft.v:394-409` -/
def doLeader (state : raft_data (P := P)) (me : name (P := P)) :
    List (raft_output (P := P)) × raft_data (P := P) × List (name (P := P) × msg (P := P)) :=
  match state.type with
  | .Leader =>
    let state' := advanceCommitIndex state me
    if state'.shouldSend then
      let state' := { state' with shouldSend := false }
      let replicaMessages :=
        ((nodes (P := P)).filter fun h => if me = h then false else true).map
          (replicaMessage state' me)
      ([], state', replicaMessages)
    else
      ([], state', [])
  | _ => ([], state, [])

/-- `Raft.v:411-417` -/
def RaftNetHandler (me src : name (P := P)) (m : msg (P := P))
    (state : raft_data (P := P)) :
    List (raft_output (P := P)) × raft_data (P := P) × List (name (P := P) × msg (P := P)) :=
  let (state, pkts) := handleMessage src me m state
  let (leaderOut, state, leaderPkts) := doLeader state me
  let (genericOut, state, genericPkts) := doGenericServer me state
  (leaderOut ++ genericOut, state, pkts ++ leaderPkts ++ genericPkts)

/-- `Raft.v:419-432` -/
def handleClientRequest (me : name (P := P)) (state : raft_data (P := P))
    (client : R.clientId) (id : Nat) (c : P.input) :
    List (raft_output (P := P)) × raft_data (P := P) × List (name (P := P) × msg (P := P)) :=
  match state.type with
  | .Leader =>
    let index := maxIndex state.log + 1
    ([],
     { state with
         log := ⟨me, client, id, index, state.currentTerm, c⟩ :: state.log,
         matchIndex := assoc_set state.matchIndex me index,
         shouldSend := true },
     [])
  | _ => ([.NotLeader client id], state, [])

/-- `Raft.v:435-440` -/
def handleTimeout (me : name (P := P)) (state : raft_data (P := P)) :
    List (raft_output (P := P)) × raft_data (P := P) × List (name (P := P) × msg (P := P)) :=
  match state.type with
  | .Leader => ([], { state with shouldSend := true }, [])  -- we automatically heartbeat elsewhere
  | _ => tryToBecomeLeader me state

/-- `Raft.v:442-447` -/
def handleInput (me : name (P := P)) (inp : raft_input (P := P))
    (state : raft_data (P := P)) :
    List (raft_output (P := P)) × raft_data (P := P) × List (name (P := P) × msg (P := P)) :=
  match inp with
  | .ClientRequest client id c => handleClientRequest me state client id c
  | .Timeout => handleTimeout me state

/-- `Raft.v:449-455` -/
def RaftInputHandler (me : name (P := P)) (inp : raft_input (P := P))
    (state : raft_data (P := P)) :
    List (raft_output (P := P)) × raft_data (P := P) × List (name (P := P) × msg (P := P)) :=
  let (handlerOut, state, pkts) := handleInput me inp state
  let (leaderOut, state, leaderPkts) := doLeader state me
  let (genericOut, state, genericPkts) := doGenericServer me state
  (handlerOut ++ leaderOut ++ genericOut, state, pkts ++ leaderPkts ++ genericPkts)

/-- `Raft.v:457-471` — crash persistence model: term/vote/log/state
machine/client cache survive; leader/candidate volatile state resets. -/
def reboot (state : raft_data (P := P)) : raft_data (P := P) :=
  { currentTerm := state.currentTerm
    votedFor := state.votedFor
    leaderId := state.leaderId
    log := state.log
    commitIndex := state.commitIndex
    lastApplied := state.lastApplied
    stateMachine := state.stateMachine
    nextIndex := []
    matchIndex := []
    shouldSend := false
    votesReceived := []
    type := .Follower
    clientCache := state.clientCache
    electoralVictories := state.electoralVictories }

/-- `Raft.v:473-487` -/
def init_handlers (_h : name (P := P)) : raft_data (P := P) :=
  { currentTerm := 0
    votedFor := none
    leaderId := none
    log := []
    commitIndex := 0
    lastApplied := 0
    stateMachine := O.init
    nextIndex := []
    matchIndex := []
    shouldSend := false
    votesReceived := []
    type := .Follower
    clientCache := []
    electoralVictories := [] }

/-- `Raft.v:489-494`. Verdi registers these as typeclass instances (via
`Hint Extern`); here they are plain reducible definitions used
explicitly — no global instances, no resolution surprises. -/
@[reducible] def raft_base_params : BaseParams where
  data := raft_data (P := P)
  input := raft_input (P := P)
  output := raft_output (P := P)

/-- `Raft.v:496-508` -/
@[reducible] def raft_multi_params : MultiParams (raft_base_params (P := P)) where
  name := name (P := P)
  msg := msg (P := P)
  msg_eq_dec := inferInstance
  name_eq_dec := inferInstance
  nodes := nodes
  all_names_nodes := fun n => allFin_all n
  no_dup_nodes := allFin_NoDup _
  init_handlers := init_handlers
  net_handlers := fun me src m st => RaftNetHandler me src m st
  input_handlers := fun me inp st => RaftInputHandler me inp st

/-- `Raft.v:510-513` -/
@[reducible] def raft_failure_params : FailureParams (raft_multi_params (P := P)) where
  reboot := reboot

/-- `Raft.v:515-554` — reachability closed under handler applications and
`step_failure`; the safety theorem (`StateMachineSafetyInterface.v:30-36`)
is stated over exactly this predicate. -/
inductive raft_intermediate_reachable :
    Network (raft_base_params (P := P)) raft_multi_params → Prop
  | RIR_init : raft_intermediate_reachable (step_async_init _ _)
  | RIR_step_failure :
      ∀ failed (net : Network (raft_base_params (P := P)) raft_multi_params)
        failed' net' out,
        raft_intermediate_reachable net →
        step_failure _ _ raft_failure_params (failed, net) (failed', net') out →
        raft_intermediate_reachable net'
  | RIR_handleInput :
      ∀ (net : Network (raft_base_params (P := P)) raft_multi_params)
        h inp out d l ps' st',
        raft_intermediate_reachable net →
        handleInput h inp (net.nwState h) = (out, d, l) →
        (∀ h', st' h' = update net.nwState h d h') →
        (∀ p', p' ∈ ps' → p' ∈ net.nwPackets ∨ p' ∈ send_packets h l) →
        raft_intermediate_reachable ⟨ps', st'⟩
  | RIR_handleMessage :
      ∀ (p : Packet (raft_base_params (P := P)) raft_multi_params)
        (net : Network (raft_base_params (P := P)) raft_multi_params)
        xs ys st' ps' d l,
        raft_intermediate_reachable net →
        handleMessage p.pSrc p.pDst p.pBody (net.nwState p.pDst) = (d, l) →
        net.nwPackets = xs ++ p :: ys →
        (∀ h, st' h = update net.nwState p.pDst d h) →
        (∀ p', p' ∈ ps' → p' ∈ (xs ++ ys) ∨ p' ∈ send_packets p.pDst l) →
        raft_intermediate_reachable ⟨ps', st'⟩
  | RIR_doLeader :
      ∀ (net : Network (raft_base_params (P := P)) raft_multi_params)
        st' ps' h os d' ms,
        raft_intermediate_reachable net →
        doLeader (net.nwState h) h = (os, d', ms) →
        (∀ h', st' h' = update net.nwState h d' h') →
        (∀ p, p ∈ ps' → p ∈ net.nwPackets ∨ p ∈ send_packets h ms) →
        raft_intermediate_reachable ⟨ps', st'⟩
  | RIR_doGenericServer :
      ∀ (net : Network (raft_base_params (P := P)) raft_multi_params)
        st' ps' os d' ms h,
        raft_intermediate_reachable net →
        doGenericServer h (net.nwState h) = (os, d', ms) →
        (∀ h', st' h' = update net.nwState h d' h') →
        (∀ p, p ∈ ps' → p ∈ net.nwPackets ∨ p ∈ send_packets h ms) →
        raft_intermediate_reachable ⟨ps', st'⟩

/-- `Raft.v:850-854` — same one-step proof as the Coq (`reflexivity`). -/
theorem reboot_init_handlers (h : name (P := P)) :
    reboot (init_handlers h) = init_handlers h := rfl

omit O in
/-- `Raft.v:856-860` -/
theorem reboot_idem (d : raft_data (P := P)) :
    reboot (reboot d) = reboot d := rfl

omit O in
/-- Not in Raft.v — a spike sanity lemma exercising real case analysis:
a `true` RequestVote grant always leaves the voter with
`votedFor = some candidateId`. -/
theorem handleRequestVote_grant_votedFor
    (me : name (P := P)) (state : raft_data (P := P))
    (t : term) (cand : name (P := P)) (lli : logIndex) (llt : term)
    (st' : raft_data (P := P))
    (h : handleRequestVote me state t cand lli llt = (st', .RequestVoteReply t' true)) :
    st'.votedFor = some cand := by
  unfold handleRequestVote at h
  split at h
  · simp_all
  · -- zeta-reduce the Coq-mirroring `let state := advanceCurrentTerm state t`
    simp only [] at h
    split at h
    · split at h
      · simp only [Prod.mk.injEq, msg.RequestVoteReply.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rfl
      · rename_i c' heq
        simp only [Prod.mk.injEq, msg.RequestVoteReply.injEq, decide_eq_true_eq] at h
        obtain ⟨rfl, -, rfl⟩ := h
        exact heq
    · simp_all

end RaftSection

end Raft

end VerdiCompat
