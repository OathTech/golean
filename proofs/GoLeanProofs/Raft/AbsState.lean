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
(`artifacts/probe/probe2.out`, arc log entry of the same date): one
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

end GoLean.RaftSeam
