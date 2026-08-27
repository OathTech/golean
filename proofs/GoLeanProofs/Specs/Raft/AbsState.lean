import GoLean.GoCore.State

/-!
# `absState` v1 — the twin heap's raft-state projection (campaign Arc 4, A4-U1)

LAYERING (seam design §2(A), TCB doctrine): this module is PROOF
INFRASTRUCTURE — the abstraction-function layer of the Arc-4 seam. It
is NEVER imported by the statement modules (`Specs/RaftAgreement.lean`
and its pin); T1's meaning does not touch it. It imports only the
machine's state vocabulary.

## What v1 reads (grounded in instrumented contact, 2026-08-22)

Probe of the pinned twin under the compiled interpreter
(`artifacts/probe/probe2.out` (untracked scratch), arc log entry of the same date): one
raft node lives in ONE heap cell — a `.struct ⟨"raft.raft"⟩` value of
~33 named fields, behind the `*raft` pointer every handler receives
(node 1's cell at `Loc.base 389` on the canonical run). Scalar
raft-state fields (`Term`, `Vote`, `lead`, `state` — all
`uint64`-kinded ints) are direct struct fields; the log lives behind
the `raftLog` pointer field, whose target cell is a
`.struct ⟨"raft.raftLog"⟩` carrying the `committed`/`applying`/
`applied` scalars (entries deeper still, behind `unstable`/`storage`).

`absRaftNode σ a` is a TOTAL first-order reader: `Option`-valued,
`none` on any shape mismatch (fail closed — a heap not in twin shape
projects to nothing, never to a wrong answer).

**OQ-A (Option vs WF-pack), answered from contact: BOTH, layered.**
The reader itself is `Option` — `absRaftNode σ a = some N` is the
equation's clean pre/post vocabulary, and `none`-on-mismatch is the
fail-closed direction. But the handler equations additionally need
executable facts the projection deliberately does NOT determine
(`electionTimeout = 10`, the tracker's key set, unstable/storage shape
for `lastIndex`) — those enter as separate hypotheses per equation
(the kit's conditioned-hypothesis style), not as projection fields: a
WF-PACK BESIDE the Option reader, never a partiality bookkeeping
scheme inside it.

## v1 gaps (numbered; omissions, not errors — each is a projection
this version deliberately does not attempt)

- **GAP-V1-1**: log ENTRIES are not projected — only the raftLog
  cell's `committed`/`applied` scalars (the tail summary). The entry
  list (unstable slice + MemoryStorage `ents` behind an interface
  field + mutex) is A4-U2+ work; S2/S3 checker-implication needs it.
- **GAP-V1-2**: the tracker (`trk.Progress`/`Votes` maps, per-peer
  `Progress` cells) is not projected. Election bookkeeping
  (`votesReceived` in Verdi vocabulary) therefore has no abstract
  image yet.
- **GAP-V1-3**: the outboxes (`msgs`, `msgsAfterAppend`) are not
  projected — the abstract in-flight multiset (seam design layer (A),
  `t.net`/`t.live`) is future work; v1 is a NODE projection only.
- **GAP-V1-4**: no `AbstractNet` — one node's raft-state view, not
  the three-node network + checker bookkeeping the round induction
  needs.
- **GAP-V1-5**: `electionElapsed`/`heartbeatElapsed`/
  `randomizedElectionTimeout` are deliberately unprojected — the
  jitter field is latitude-bearing (D-11), and the spec layer's
  handlers do not read them.
-/

namespace GoLean.RaftSeam

open GoLean.GoCore

/-- One node's abstract raft state, v1: the scalar projection of the
`raft.raft` struct plus the log-tail summary read through the
`raftLog` pointer. Values are the machine's `Int` carrier (all four
scalars are `uint64`-kinded on the heap; `state` is etcd's `StateType`
numeral — 0 follower, 1 candidate, 2 leader, 3 pre-candidate,
`raftsubject/raft/raft.go:48-55`). -/
structure AbsRaftState where
  term : Int
  vote : Int
  lead : Int
  state : Int
  committed : Int
  applied : Int
  deriving Repr, DecidableEq

/-- A `uint64`-kinded machine int, or nothing (fail closed on any
other value shape). -/
def asU64 : GoValue → Option Int
  | .int v .uint64 => some v
  | _ => none

/-- Field read + `uint64` decode in one step. -/
def fieldU64 (fs : Array (String × GoValue)) (name : String) : Option Int :=
  (StructFields.lookup fs name).bind asU64

/-- THE READER (total, first-order, fail-closed): project the raft
node whose `raft.raft` struct cell sits at `Loc.base a`. `none` on any
shape mismatch — wrong struct tag, missing field, non-`uint64` scalar,
dangling or mis-shaped `raftLog` pointer. -/
def absRaftNode (σ : ExecState) (a : Addr) : Option AbsRaftState := do
  let cell ← Heap.lookup σ.heap (.base a)
  match cell.value with
  | .struct ⟨"raft.raft"⟩ fs => do
      let term ← fieldU64 fs "Term"
      let vote ← fieldU64 fs "Vote"
      let lead ← fieldU64 fs "lead"
      let state ← fieldU64 fs "state"
      match StructFields.lookup fs "raftLog" with
      | some (.addr rl) => do
          let rlCell ← Heap.lookup σ.heap rl
          match rlCell.value with
          | .struct ⟨"raft.raftLog"⟩ rfs => do
              let committed ← fieldU64 rfs "committed"
              let applied ← fieldU64 rfs "applied"
              pure { term, vote, lead, state, committed, applied }
          | _ => none
      | _ => none
  | _ => none

/-- **The pilot's spec handler**: `becomeFollower(term, lead)`, at the
abstract state. Re-grounded 1:1 from the subject
(`raftsubject/raft/raft.go:910-919` with `reset`'s term/vote clause,
`:800-804`): term is overwritten unconditionally; the vote is cleared
exactly when the term CHANGES; the node becomes a follower of `lead`;
the log summary is untouched.

Relation to the ported Verdi spec (recorded, NOT imported —
constitution §5 Plan A: `compat/verdi` is a read-only reference, never
an import; statements re-ground in harness vocabulary): on the
`st.term ≤ t` inputs every reachable call site uses, this is exactly
`{ advanceCurrentTerm st t with type := .Follower, leaderId := lead }`
(`VerdiCompat/Raft.lean:135-140`, mirroring verdi-raft `Raft.v:141-148`
— `advanceCurrentTerm` composed with the Follower/leaderId override,
the composite `handleAppendEntries`/`handleRequestVoteReply` use). At
`t < st.term` the subject (unlike `advanceCurrentTerm`) still lowers
the term — this function mirrors the SUBJECT, which is what the
interpreter-run equation is about; the Verdi correspondence carries
the `st.term ≤ t` side condition and lives with the invariant layer
that supplies it. -/
def specBecomeFollower (st : AbsRaftState) (t lead : Int) : AbsRaftState :=
  { st with
      term := t
      vote := if st.term = t then st.vote else 0
      lead := lead
      state := 0 }

/-! ## Wave-1 spec handlers (A4-U4; re-grounded from the SUBJECT,
compat/verdi cited but never imported — constitution §5 Plan A) -/

/-- **becomeCandidate spec** (`raftsubject/raft/raft.go:921-934`,
with `reset(r.Term+1)`'s term/vote clause `:800-804`): the term
increments (always ≠ the old term, so reset clears the vote), then
the node votes for ITSELF (`r.Vote = r.id`, after reset), the lead is
cleared by reset (`r.lead = None`), and the state becomes
`StateCandidate` (numeral 1, `:46-53`). The log summary is untouched.
The `r.state == StateLeader` panic guard is a PRECONDITION of the
handler equation's fixture (state concrete ≠ 2), not of this spec
function. Verdi correspondence (read-only cite): this is the
state-transition core of verdi-raft's `tryToBecomeLeader`
(`Raft.v`, candidate step: `currentTerm + 1`, `votedFor := Some me`,
`type := Candidate` — `VerdiCompat/Raft.lean`); vote-collection
bookkeeping lives in the tracker, unprojected at v1 (GAP-V1-2). -/
def specBecomeCandidate (st : AbsRaftState) (id : Int) : AbsRaftState :=
  { st with
      term := st.term + 1
      vote := id
      lead := 0
      state := 1 }

/-- **becomePreCandidate spec** (`raftsubject/raft/raft.go:936-951`):
NO reset — the term and vote are deliberately unchanged (the
function's own comment); `ResetVotes` touches only the tracker
(unprojected, GAP-V1-2); the lead clears and the state becomes
`StatePreCandidate` (numeral 3). Same panic-guard precondition note
as `specBecomeCandidate`. PreVote is an etcd extension with no Verdi
counterpart — grounded in the subject alone. -/
def specBecomePreCandidate (st : AbsRaftState) : AbsRaftState :=
  { st with
      lead := 0
      state := 3 }

/-! ## The storage projection (A4-U4 wave 1 — an ADDITIVE AbsState
extension; the charter's per-handler verification found the storage
leaves need the ENTRIES, which v1 deliberately did not project).

**GAP-V1-1 status update (renumbered as instructed):** the
MemoryStorage half of the entry projection closes here
(**GAP-V1-1a**: the stable `ents` array behind the storage interface,
read by `absStorageEnts` below). The UNSTABLE half (**GAP-V1-1b**:
`unstable.entries` + the offset arithmetic, needed for the raftLog
view the message handlers read) remains open — wave-2 work, exactly
where the U3 verdict placed the absState extension. -/

/-- Dereference one plainpb pointer-scalar (`*uint64`): `.addr` →
the target cell's `uint64`; `.nil` → 0 (the shim's nil-getter
semantics, `GetIndex`/`GetTerm` on a nil field). Fail closed
otherwise. -/
def derefU64 (σ : ExecState) : GoValue → Option Int
  | .nil => some 0
  | .addr l => (Heap.lookup σ.heap l).bind (fun c => asU64 c.value)
  | _ => none

/-- One `raftpb.Entry` cell → its `(index, term)` pair (plainpb
shape: `Index`/`Term` are pointer scalars). Fail closed on any shape
mismatch. -/
def absEntry (σ : ExecState) : GoValue → Option (Int × Int)
  | .addr l => do
      let cell ← Heap.lookup σ.heap l
      match cell.value with
      | .struct ⟨"raftpb.Entry"⟩ fs => do
          let idx ← (StructFields.lookup fs "Index").bind (derefU64 σ)
          let term ← (StructFields.lookup fs "Term").bind (derefU64 σ)
          pure (idx, term)
      | _ => none
  | _ => none

/-- **THE STORAGE READER** (total, first-order, fail-closed): the
`(index, term)` list of the `MemoryStorage` at `Loc.base a` — the
`ents` slice walked through its backing array, each element's Entry
cell dereferenced. `none` on any shape mismatch. `callStats` is
deliberately unread (the instrumented counters are real heap effects
of storage "reads" but carry no raft state). -/
def absEntsFrom (σ : ExecState) (vs : Array GoValue) :
    Nat → Nat → Option (List (Int × Int))
  | _, 0 => some []
  | i, n + 1 => do
      let v ← vs[i]?
      let p ← absEntry σ v
      let rest ← absEntsFrom σ vs (i + 1) n
      pure (p :: rest)

def absStorageEnts (σ : ExecState) (a : Addr) : Option (List (Int × Int)) := do
  let cell ← Heap.lookup σ.heap (.base a)
  match cell.value with
  | .struct ⟨"raft.MemoryStorage"⟩ fs =>
      match StructFields.lookup fs "ents" with
      | some (.slice sv) => do
          let base ← sv.base
          let arrCell ← Heap.lookup σ.heap base
          match arrCell.value with
          | .array vs => absEntsFrom σ vs sv.offset sv.len
          | _ => none
      | _ => none
  | _ => none

/-- **`MemoryStorage.firstIndex` spec** (`raftsubject/raft/storage.go`:
`ms.ents[0].GetIndex() + 1` — the dummy-entry convention). `none` on
an empty list (the subject indexes unconditionally; an empty `ents`
never occurs — the dummy entry is an invariant). -/
def specFirstIndex (es : List (Int × Int)) : Option Int :=
  es.head?.map (fun p => p.1 + 1)

/-- **`MemoryStorage.Term` spec, the NON-ERROR branch**
(`storage.go`: `offset = ents[0].GetIndex()`; requires
`offset ≤ i < offset + len`, else the subject returns
`ErrCompacted`/`ErrUnavailable` — the error branches are OUTSIDE this
spec (`none` here), and their equations are a recorded residual: the
lowered error path loads package-level error vars at STATIC twin
addresses the leaf fixture does not carry. -/
def specTermAt (es : List (Int × Int)) (i : Int) : Option Int := do
  let hd ← es.head?
  let offset := hd.1
  if i < offset then none
  else match es[(i - offset).toNat]? with
    | some p => some p.2
    | none => none

end GoLean.RaftSeam
