import GoLeanProofs.Specs.Raft.AbsTwinCheckerRead
import GoLeanProofs.Specs.Raft.NativeCheckerBridge
import GoLeanProofs.Frame.Plug

/-! # W3 U3.0c — THE INVARIANT MODULE: `I`, per the adopted design

The driver-loop invariant of the adopted contract
(`docs/2026-08-27_w25-invariant-design.md`), faithfully:

    I σ := Base σ ∧ Pair σ ∧ Hygiene σ ∧ Stream σ
         ∧ (Electing σ ∨ Elected σ)

with `CheckerCorr ⊆ Pair` and `NetCorr ⊆ Pair` (the note's C3/C4 are
sub-clauses of the pairing; here the shared existential witnesses —
the ghost-completed abstract net and the two event histories — are
HOISTED into one pack (`AbsCarrier`) so every sub-clause speaks about
the same carrier; this hoisting is the one structural departure from
the note's surface syntax, recorded in the W3 log).

**U3.0d (charter Amendment 1, the census addenda — folded in):**
(1) THE TERM-BOUND CLAUSE — `AbsCarrier` gains the campaign term
`tm`; `Pair.tmPos`/`Pair.terms` bound every abstract node term into
`{0, tm}` and `NetCorr.netTerms` pins every live net message's term
to exactly `tm` (the two halves that kill `raft.Step`'s
`m.Term < r.Term` block, census §2.2.1); the Elected phase's term IS
`A.tm` (pinned in `I.pair`'s Elected branch). (2) PROBE-STATE
VOCABULARY — `Pair.progress` carries every node's tracker Progress
data (U3.0d readers `absProgressOf`/`absRaftLogOf`) with the `ProgOk`
consistency facts (the snapshot-family-death chain, census §2.4) and
the tracker population = voters. (3) POPULATION TIGHTENED —
`NetCorr.population` is the census-proved four-type wire alphabet
(§3.1); the design note's five-type list is corrected on the record.
(4) C5/U4 — verdict recorded at `I`'s docstring: the landed
Stream/Hygiene clauses absorb the D-11 dead draws unchanged.

**DEFINITIONS ONLY (the unit charter):** this module defines `I` and
proves cheap sanity lemmas (definedness projections, the
trace-forgetting map, the electing-phase counter collapses, the
S1-chain plug-in). PRESERVATION is the W3 handler waves' work;
ESTABLISHMENT (the base case at the loop head) is W3.2f's; the
LOOP INSTANCE is W4's. `I` therefore has NO inhabitation witness yet
— by charter, not by accident; W3.2f owes it.

**QUANTIFIER LINE (the wave's):** defining `I` advances no
end-theorem quantifier; `I` is the contract the loop rule (∀
iterations), the body specs (∀ states), and the seam assembly (W5)
discharge against.

**THE NAMED JOINTS (parameters later waves must supply — never
silent `True` stubs; each is load-bearing in the clauses below):**

- `dataEnc : List Int → Nat → Prop` — the data-encoding relation
  between concrete command bytes (message `Data` / checker-map
  strings) and the abstract data ids of `Hist`/`AEv` (the harvest
  arc4d `encGS` seam). Supplied by W3.2d (the checker reshape);
  consumed here by `ByIndexCorr`, `GotCorr`, and the Elected payload
  clause. `I` is parameterized by it.
- The `certified` instantiation is ALREADY supplied (U3.0a's
  `ackCertified`) and is wired into the Elected carrier's `Star
  (HStep …)` verbatim — W3.2b discharges its premises at the
  commit-advance; nothing here assumes them.

Statement-hygiene notes: the constant 31 (statics count) and the
node-id convention (ids 1..n at list positions 0..n-1) are shape
constants of the REFLECTED PROGRAM (the twin's global table and
`newTwin`'s id loop), not subject-run measurements; the message-type
and entry-type numerals are `raftpb` enum constants
(raftsubject/raftpb/raft.pb.go:74-99, 33). Map correspondences are
LOOKUP-vocabulary only (map order is latitude — the U3.0b module
docstring).

LINEAGE: inductive network invariants over a ghost-completed
abstraction relation — the Verdi `votes_nw`/`leaderLogs` stratum
(named by the professor's Gap 1) composed with separation-logic
placement data (FrameSim) and history/auxiliary-variable refinement
(Abadi–Lamport) for the Elected carrier. No new mechanism class. -/

namespace GoLean.RaftSeam.Inv

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Lens GoLean.Frame
open GoLean.RaftSeam
open GoLean.RaftSeam.NativeSpec

/-! ## Vocabulary constants (raftpb enum numerals, cited) -/

/-- `MessageType_MsgProp = 2` (raft.pb.go:77; LOCAL — never wire). -/
def msgProp : Int := 2
/-- `MessageType_MsgApp = 3` (raft.pb.go:78). -/
def msgApp : Int := 3
/-- `MessageType_MsgAppResp = 4` (raft.pb.go:79). -/
def msgAppResp : Int := 4
/-- `MessageType_MsgVote = 5` (raft.pb.go:80). -/
def msgVote : Int := 5
/-- `MessageType_MsgVoteResp = 6` (raft.pb.go:81). -/
def msgVoteResp : Int := 6
/-- `EntryType_EntryNormal = 0` (raft.pb.go:33). -/
def entryNormalTy : Int := 0

/-- A concrete (machine-Int) value IS the Nat `n` — the precise
Int↔Nat bridge (used instead of `Int.toNat`, whose negative-collapse
would let a mis-shaped negative value alias 0; fail closed). -/
def asNat (i : Int) (n : Nat) : Prop := i = (n : Int)

/-- A `GoString`'s bytes in the message-data vocabulary. -/
def gsBytes (s : GoString) : List Int :=
  s.bytes.toList.map (fun b => (b.toNat : Int))

/-- First-match lookup on an Int-keyed association list (the map
readers' lookup vocabulary; keys are unique in a Go map, so
first-match = the map's lookup). -/
def lookupI {ν : Type} : List (Int × ν) → Int → Option ν
  | [], _ => none
  | p :: rest, t => if p.1 = t then some p.2 else lookupI rest t

/-! ## The carrier pack — the hoisted existential witnesses -/

/-- The abstract carrier `I` pairs the concrete state with: the
ghost-completed S1 net (C2's ∃-ghost), the two event histories
(C3's ∃-histories), and — U3.0d, charter Amendment 1 — the single
campaign's term `tm` (the term-bound clause's witness, shared by the
node/net term bounds and forced onto `ElectedAt`'s term in the
Elected phase). One pack so Pair/CheckerCorr/NetCorr and the phase
split all constrain the SAME witnesses. -/
structure AbsCarrier where
  N : SNet
  evsS1 : List (Nat × Nat)
  evsA : List AEv
  tm : Nat

/-! ## C1 — Base (the init-spec product, maintained) -/

/-- **`Base`**: the init-spec product at loop heads — the 31 statics
materialized at their true addresses (`initSetup_establishes`' export
shape; 31 = the twin wire's global count, a reflected-program
constant), the logger INSTALLED (`⟨30⟩` reads `true` — post-
`installLogger`, the stage-A spec's `false` flipped by the setup
prefix), and lift-definedness AS A CLAUSE: the twin/node/net/checker
structures are well-shaped enough that every reader of the pairing
vocabulary is defined (the big-step square decision). -/
structure Base (σ : ExecState) (tl : Loc) : Prop where
  statics : ∀ g : Nat, g < 31 → ∃ v, loadLoc σ (.base ⟨g⟩) = .ok v
  loggerInstalled : loadLoc σ (.base ⟨30⟩) = .ok (.bool true)
  twinRead : ∃ tv, absTwinRead σ tl = some tv
  leaderOfRead : ∃ m, absLeaderOf σ tl = some m
  byIndexRead : ∃ m, absByIndex σ tl = some m
  nodeReads : ∀ tv, absTwinRead σ tl = some tv →
    ∀ i, i < tv.nodes.length →
      (∃ p, absNodeCursors σ tl i = some p) ∧
      (∃ g, absNodeGot σ tl i = some g)
  netMetaRead : ∀ tv, absTwinRead σ tl = some tv →
    ∃ ms, absNetMeta σ tl = some ms ∧ ms.length = tv.net.length

/-! ## C2 — the footprint-carrier pairing -/

/-- Deep-reader agreement on the S1 axes — state/term/vote/lead.
`committed`/`applied` are DELIBERATELY OUTSIDE (the
stutter-provability condition the professor flagged: commit movement
must be a provable stutter on the S1 carrier; the commit axes pair
against the Elected H-carrier instead). -/
def s1Agrees (st : AbsRaftState) (r : ENode) : Prop :=
  st.state = (r.state : Int) ∧ st.term = (r.term : Int) ∧
  st.vote = (r.vote : Int) ∧ st.lead = (r.lead : Int)

/-- **The ∃-placement clause** (W1 Leg-B finding 3, made structural):
node `i`'s deep raft cell at concrete address `raftAddr` is the
FrameSim image of a footprint CARRIER at a placement `(ρ, fr)` — the
invariant carries the placement data the handler CallSpecs consume
(spec at canonical anchor + FrameSim + plug + reader congruence, the
W2-gate recipe) — and the deep reader ON THE CARRIER agrees with the
abstract node on the S1 axes. -/
def NodePlaced (σ : ExecState) (raftAddr : Nat) (r : ENode) : Prop :=
  ∃ (ρ : Nat → Nat) (na₀ na : Nat) (fr : Heap) (σc : ExecState)
    (a : Nat) (st : AbsRaftState),
    FrameSim ρ na₀ na fr σc σ ∧ ρ a = raftAddr ∧
    absRaftNode σc ⟨a⟩ = some st ∧ s1Agrees st r

/-- The SHELL-SYNC sub-clause: at loop heads every node is locally
quiesced, so the harness-observed shell agrees with the abstract node
on exactly the fields ClaimTrace speaks — state and term (`commit`
outside, as above; `applied` pairs through CheckerCorr's cursors). -/
def shellSync (sh : Int × Int × Int × Int) (r : ENode) : Prop :=
  sh.1 = (r.state : Int) ∧ sh.2.1 = (r.term : Int)

/-- The Progress consistency facts (U3.0d, charter Amendment 1;
census §2.4's snapshot-death chain + §2.6's live-arm set), per
tracker entry, against the OWNER's concrete log view
(`li` = the owner's `AbsLog.lastIndex`):

- `matchLB`/`matchLog`: `0 ≤ Match ≤ lastIndex` (the amendment's
  "Match ≤ log length").
- `nextMatch`/`nextLB`: `Next ≥ Match + 1` and `Next ≥ 2` — the
  amendment's chain "Next ≥ Match+1 ≥ 2" read DISTRIBUTIVELY: at a
  fresh `reset` a follower's Match is 0 (raft.go:815-820), so the
  literal chain `Match+1 ≥ 2` is unsatisfiable; the census's own
  §2.4 argument uses exactly the two separate bounds (design delta,
  recorded in the W3 log).
- `nextUB` ([AGENT] addition beyond the amendment's letter):
  `Next ≤ lastIndex + 1` — without it `raftLog.term(Next-1)` can
  return `ErrUnavailable` (log.go:401-403) and `maybeSendSnapshot`
  is NOT refuted; the amendment's named facts alone kill only the
  `ErrCompacted` route. Recorded as a design delta, not silently
  absorbed.
- `stateWire`: `State ∈ {StateProbe=0, StateReplicate=1}` — the
  snapshot family's death makes `BecomeSnapshot` unreachable
  (census §2.6); the handler specs consume this to refute the
  `StateSnapshot` arms (stepLeader:1550-1564, `IsPaused`). -/
structure ProgOk (li : Int) (p : AbsProgress) : Prop where
  matchLB : 0 ≤ p.matchIdx
  matchLog : p.matchIdx ≤ li
  nextMatch : p.matchIdx + 1 ≤ p.nextIdx
  nextLB : 2 ≤ p.nextIdx
  nextUB : p.nextIdx ≤ li + 1
  stateWire : p.state = 0 ∨ p.state = 1

/-- **`Pair`** (C2): the seeded S1 reach carrier plus, per concrete
node `i` (id `i+1` — `newTwin`'s id loop, a reflected-program
constant), the ∃-placement and the shell-sync against the SAME
abstract net. `count`/`ids` record the driver's configuration shape
(concrete node list ↔ the voter set). U3.0d additions (charter
Amendment 1): `tmPos`/`terms` — the node half of the term-bound
clause (every abstract node term ∈ {0, A.tm}; concrete terms follow
through `s1Agrees`/`shellSync`) — and `progress`, the probe-state
vocabulary on C2's concrete side (every node's tracker entries
satisfy the `ProgOk` consistency facts against that node's own
concrete log view, with the tracker population = the voter set —
what kills `RawNode.Step`'s `pr == nil` arm). -/
structure Pair (voters : List Nat) (N₀ : SNet) (σ : ExecState) (tl : Loc)
    (tv : AbsTwinV0) (A : AbsCarrier) : Prop where
  seed : Seed N₀
  reach : ReachRel (EStep voters) N₀ A.N
  count : tv.nodes.length = voters.length
  ids : ∀ i, i < tv.nodes.length → (i + 1) ∈ voters
  nodes : ∀ i, i < tv.nodes.length →
    ∃ ra, absTwinNodeRaft σ tl i = some ra ∧
      NodePlaced σ ra.id (A.N.node (i + 1))
  shells : ∀ i sh, tv.nodes[i]? = some sh →
    shellSync sh (A.N.node (i + 1))
  tmPos : 1 ≤ A.tm
  terms : ∀ i, (A.N.node i).term = 0 ∨ (A.N.node i).term = A.tm
  progress : ∀ i, i < tv.nodes.length →
    ∃ ra L li pm,
      absTwinNodeRaft σ tl i = some ra ∧
      absRaftLogOf σ ra = some L ∧
      L.lastIndex = some li ∧
      absProgressOf σ ra = some pm ∧
      (∀ q ∈ pm, ProgOk li q.2) ∧
      (∀ q ∈ pm, ∃ v ∈ voters, q.1 = (v : Int)) ∧
      (∀ v ∈ voters, ∃ p, lookupI pm (v : Int) = some p)

/-! ## C3 — the checker-state correspondence (`CheckerCorr ⊆ Pair`) -/

/-- `ClaimTrace` with a NAMED ENDPOINT: the observation trace's last
net reaches `Nf`. The landed `ClaimTrace` (NativeS1CheckerLeaf)
truncates anywhere — sufficient for the leaf, but preservation needs
to EXTEND the trace at a new harvest claim, which requires knowing
the trace's frontier reaches the current carrier. Forgetting the
endpoint recovers the landed form (`toClaimTrace` below), so every
leaf consumer is served. -/
inductive ClaimTraceTo (step : SNet → SNet → Prop) :
    SNet → List (Nat × Nat) → SNet → Prop where
  | done {N Nf : SNet} : ReachRel step N Nf → ClaimTraceTo step N [] Nf
  | obs {N N' Nf : SNet} {t l : Nat} {cls : List (Nat × Nat)} :
      ReachRel step N N' →
      (N'.node l).state = 2 → (N'.node l).term = t →
      ClaimTraceTo step N' cls Nf →
      ClaimTraceTo step N ((t, l) :: cls) Nf

theorem ClaimTraceTo.toClaimTrace {step : SNet → SNet → Prop} :
    ∀ {N Nf : SNet} {cls : List (Nat × Nat)},
      ClaimTraceTo step N cls Nf → ClaimTrace step N cls := by
  intro N Nf cls h
  induction h with
  | done _ => exact .done _
  | obs hr hst htm _ ih => exact .obs hr hst htm ih

/-- The endpoint is reachable from the trace start (the preservation
hook: extending the trace at the frontier). -/
theorem ClaimTraceTo.reach {step : SNet → SNet → Prop} :
    ∀ {N Nf : SNet} {cls : List (Nat × Nat)},
      ClaimTraceTo step N cls Nf → ReachRel step N Nf := by
  intro N Nf cls h
  induction h with
  | done hr => exact hr
  | obs hr _ _ _ ih => exact hr.trans ih

/-- Concrete `leaderOf` ↔ the S1 fold's map: Nat-ranged keys/values
and lookup agreement at every term (both directions — the `none`
cases coincide because the equation is between the full Options). -/
def LeaderOfCorr (conc : List (Int × Int))
    (model : List (Nat × Nat)) : Prop :=
  (∀ p ∈ conc, ∃ t l : Nat, p = ((t : Int), (l : Int))) ∧
  ∀ t : Nat, lookupI conc (t : Int)
    = (lookupTerm model t).map (fun l => (l : Int))

/-- Concrete `byIndex` ↔ the S2/S3 fold's map, through the data
encoding joint: Nat-ranged keys, domain agreement, and per-index
agreement on (term, data-via-`dataEnc`, first node). -/
def ByIndexCorr (dataEnc : List Int → Nat → Prop)
    (conc : List (Int × (Int × GoString × Int)))
    (model : List (Nat × Nat × Nat × Nat)) : Prop :=
  (∀ p ∈ conc, ∃ i : Nat, p.1 = (i : Int)) ∧
  ∀ i : Nat,
    ((lookupI conc (i : Int)).isSome ↔ (lookupIdx model i).isSome) ∧
    (∀ s t' d' n', lookupI conc (i : Int) = some s →
      lookupIdx model i = some (t', d', n') →
      s.1 = (t' : Int) ∧ dataEnc (gsBytes s.2.1) d' ∧ s.2.2 = (n' : Int))

/-- Concrete per-node `got` ↔ the applied events: exactly the
non-noop data this node applied (both directions, through
`dataEnc`; the checker only ever stores `true`). -/
def GotCorr (dataEnc : List Int → Nat → Prop)
    (conc : List (GoString × Bool)) (nodeId : Nat)
    (evsA : List AEv) : Prop :=
  (∀ p ∈ conc, p.2 = true) ∧
  (∀ s : GoString, (s, true) ∈ conc →
    ∃ e ∈ evsA, e.node = nodeId ∧ e.data ≠ 0 ∧ dataEnc (gsBytes s) e.data) ∧
  (∀ e ∈ evsA, e.node = nodeId → e.data ≠ 0 →
    ∃ s : GoString, (s, true) ∈ conc ∧ dataEnc (gsBytes s) e.data)

/-- **`CheckerCorr`** (C3): ∃ event histories (in the carrier pack)
with (a) the claims as an endpoint-named observation trace; (b) the
S1 fold-state equations (`leaderOf`, claims counter); (c) the S2/S3
fold-state equations (`byIndex`, per-node cursors, `got`); (e) the
violation counter EQUAL to the model folds' violation sum — the
"+ 0" of the design note is this equation's preservation shape:
every non-model guard (S3 anomaly, the harness guards) must stay
silent for the equation to be maintained, and each such silence is a
named W3 spec conclusion per the T1-V census. (Clause (d) — the
apply events against the H-carrier's applied logs — is
Elected-scoped and lives in `ElectedAt.appliedLogs`.) -/
structure CheckerCorr (dataEnc : List Int → Nat → Prop)
    (voters : List Nat) (N₀ : SNet) (σ : ExecState) (tl : Loc)
    (tv : AbsTwinV0) (A : AbsCarrier) : Prop where
  trace : ClaimTraceTo (EStep voters) N₀ A.evsS1 A.N
  leaderOf : ∀ m, absLeaderOf σ tl = some m →
    LeaderOfCorr m (s1Run A.evsS1).leaderOf
  claims : tv.claims = ((s1Run A.evsS1).claims : Int)
  byIndex : ∀ m, absByIndex σ tl = some m →
    ByIndexCorr dataEnc m (s23Run A.evsA).byIndex
  cursors : ∀ i, i < tv.nodes.length →
    absNodeCursors σ tl i
      = some (((s23Run A.evsA).applied (i + 1) : Int),
              ((s23Run A.evsA).lastTrm (i + 1) : Int))
  got : ∀ i g, i < tv.nodes.length → absNodeGot σ tl i = some g →
    GotCorr dataEnc g (i + 1) A.evsA
  violations : tv.violations
    = (((s1Run A.evsS1).viols + (s23Run A.evsA).violS2
        + (s23Run A.evsA).violS3 : Nat) : Int)

/-! ## C4 — NetCorr (`⊆ Pair`; the professor's Gap 1) -/

/-- **`NetCorr`**, the phase-shared half (population + entry typing +
hgen). Payload and ack/Match are Elected-scoped (they speak the
H-carrier) — `ElectedNet` below; in `Electing` the population is
restricted to the vote family, so those clauses are vacuous there BY
POPULATION, not by stub.

- `population` (U3.0d TIGHTENED, charter Amendment 1 item 3): every
  LIVE message is one of the FOUR wire types
  Vote/VoteResp/App/AppResp — in particular NO
  MsgTimeoutNow/TransferLeader/Hup: the second-election exclusion as
  a PRESERVED fact (the library can campaign on receipt; the driver
  never emits the trigger). CORRECTION against the design note's C4
  (which listed five, incl. Prop(local)): the census §3.1 proves the
  net alphabet is exactly {3,4,5,6} — the only MsgProp forwarding
  site (`stepFollower:1748`) is unreachable in T1, and the harvest
  folds only `rd.Messages`. Recorded in the W3 log.
- `netTerms` (U3.0d, the net half of the term-bound clause): every
  live message carries EXACTLY the campaign term `A.tm` — stronger
  than the amendment's "∈ {0, tm}" spelling, and deliberately so
  ([AGENT], logged): every wire emission is term-stamped with its
  sender's term (`send:562`) and no node at term 0 ever emits (nodes
  2/3 emit only inside a `Step` whose prelude has already bumped
  them to the message's term); the exact form kills BOTH
  `raft.Step`'s `m.Term < r.Term` block (census §2.2.1) AND the
  spurious `m.Term == 0` local-prelude branch at deliveries.
- `entryTypes`: all entries EntryNormal (feeds the S3-anomaly
  guard's silence), via the U3.0b metadata reader, positionally
  aligned with `tv.net` (`metaLen`).
- `hgen`: term-aware grant provenance against `ghost.votes` —
  discharging `EStep.recvVoteResp`'s premise at delivery. -/
structure NetCorr (dataEnc : List Int → Nat → Prop)
    (σ : ExecState) (tl : Loc) (tv : AbsTwinV0) (A : AbsCarrier) :
    Prop where
  metaLen : ∀ ms, absNetMeta σ tl = some ms → ms.length = tv.net.length
  population : ∀ lm ∈ tv.net, lm.1 = true →
    lm.2.typ = msgVote ∨ lm.2.typ = msgVoteResp ∨ lm.2.typ = msgApp ∨
    lm.2.typ = msgAppResp
  netTerms : ∀ lm ∈ tv.net, lm.1 = true → asNat lm.2.term A.tm
  entryTypes : ∀ ms, absNetMeta σ tl = some ms →
    ∀ (j : Nat) (lm : Bool × AbsMessage) (mta : List (Int × List Int)),
      tv.net[j]? = some lm → ms[j]? = some mta →
      lm.1 = true → ∀ em ∈ mta, em.1 = entryNormalTy
  hgen : ∀ lm ∈ tv.net, lm.1 = true → lm.2.typ = msgVoteResp →
    lm.2.reject = false →
    ∃ t c s : Nat, asNat lm.2.term t ∧ asNat lm.2.dst c ∧
      asNat lm.2.src s ∧ (t, c) ∈ A.N.ghost.votes s

/-! ## The phase split -/

/-- **`Electing`**: no leader EVER — victory record empty, no claims,
no applies, the net vote-family only (which is what makes the
Elected-scoped clauses vacuous here by population rather than by
stub). -/
structure Electing (tv : AbsTwinV0) (A : AbsCarrier) : Prop where
  noVictory : A.N.ghost.victories = []
  noClaims : A.evsS1 = []
  noApplies : A.evsA = []
  votesOnly : ∀ lm ∈ tv.net, lm.1 = true →
    lm.2.typ = msgVote ∨ lm.2.typ = msgVoteResp

/-- The newest-first/oldest-first log-convention bridge: an `ENode`
log (newest-first `(index, term)` pairs) from a `Hist` (oldest-first
`(index, term, data)` triples). -/
def hlogBridge (H : Hist) : List (Nat × Nat) :=
  (H.map (fun e => (e.1, e.2.1))).reverse

/-- **The Elected net clauses** (C4's payload + ack/Match, stated
against the H-carrier):

- `payload`: a live MsgApp's entries ARE the history slice starting
  after its `index` (MsgApp `Index` = the entry preceding the
  appended batch, so hist POSITION `index` — the seed snapshot at
  index 1 occupies position 0), on the `(index, term)` axes via
  `absMessage` and on the data axis via the metadata reader +
  `dataEnc`; its commit bound ≤ the leader's — discharging
  `HStep.deliverAppend`'s premises.
- `ack`: a live genuine AppResp is ghost-recorded (U3.0a's acks —
  the C4 ack clause) AND its index is within the sender's log — the
  Match evidence `certified` is instantiated from at the leader's
  commit-advance (W3.2b). -/
structure ElectedNet (dataEnc : List Int → Nat → Prop)
    (σ : ExecState) (tl : Loc) (tv : AbsTwinV0) (A : AbsCarrier)
    (ldr tm : Nat) (NH : HNet) : Prop where
  payload : ∀ ms, absNetMeta σ tl = some ms →
    ∀ (j : Nat) (lm : Bool × AbsMessage) (mta : List (Int × List Int)),
      tv.net[j]? = some lm → ms[j]? = some mta →
      lm.1 = true → lm.2.typ = msgApp →
      ∃ idx : Nat, asNat lm.2.index idx ∧
        lm.2.entries
          = ((NH.hist.drop idx).take lm.2.entries.length).map
              (fun e => ((e.1 : Int), (e.2.1 : Int))) ∧
        mta.length = lm.2.entries.length ∧
        (∀ (kk : Nat) (em : Int × List Int) (e : Nat × Nat × Nat),
          mta[kk]? = some em →
          ((NH.hist.drop idx).take lm.2.entries.length)[kk]? = some e →
          dataEnc em.2 e.2.2) ∧
        (∃ c : Nat, asNat lm.2.commit c ∧ c ≤ (NH.node ldr).committed)
  ack : ∀ lm ∈ tv.net, lm.1 = true → lm.2.typ = msgAppResp →
    lm.2.reject = false →
    ∃ t k s : Nat, asNat lm.2.term t ∧ asNat lm.2.index k ∧
      asNat lm.2.src s ∧
      (t, k) ∈ A.N.ghost.acks s ∧ k ≤ (NH.node s).log.length

/-- **`ElectedAt`** — the Elected phase at leader `ldr`, term `tm`,
with the H-carrier `(H₀, NH)`:

- the ghost VICTORY justifies the phase (the election happened — on
  the record, not asserted);
- `HistInv ldr tm H₀` + `Star (HStep ldr tm (ackCertified …))` — the
  history chain from the establishment point (H₀ = the
  winning-delivery postcondition's carrier, the noop-as-first-
  propose with the snapshot offset absorbed by the projection),
  `certified` instantiated at U3.0a's ghost-acks VERBATIM;
- the S1↔H pairing: per-node log/commit ties through the
  newest/oldest bridge; the deep reader's commit/applied axes pair
  against the H-carrier (the axes `s1Agrees` deliberately omits —
  read DIRECTLY on σ, which coincides with the carrier read by
  `absRaftNode_frameSim`);
- C3(d): the apply events are the H-carrier's applied logs;
- the Elected net clauses. -/
structure ElectedAt (dataEnc : List Int → Nat → Prop)
    (voters : List Nat) (σ : ExecState) (tl : Loc) (tv : AbsTwinV0)
    (A : AbsCarrier) (ldr tm : Nat) (H₀ NH : HNet) : Prop where
  victory : ∃ q, isQuorum voters q ∧ (tm, ldr, q) ∈ A.N.ghost.victories
  histInv : HistInv ldr tm H₀
  star : Star (HStep ldr tm (ackCertified voters A.N.ghost tm)) H₀ NH
  logBridge : ∀ i, (A.N.node i).log = hlogBridge (NH.node i).log
  commitTie : ∀ i, (A.N.node i).committed = (NH.node i).committed
  deepCommit : ∀ i, i < tv.nodes.length →
    ∀ ra st, absTwinNodeRaft σ tl i = some ra →
      absRaftNode σ ra = some st →
      st.committed = ((NH.node (i + 1)).committed : Int) ∧
      st.applied = ((NH.node (i + 1)).applied : Int)
  appliedLogs : ∀ i, (NH.node i).appliedLog = nodeEvents i A.evsA
  net : ElectedNet dataEnc σ tl tv A ldr tm NH

/-! ## C5 — hygiene and the stream -/

/-- **`Hygiene`** (C5's context half): the driver's loop-head
continuation is `mapIterFree` and recover-refuting — so every
plug-rule application in the body discharges its two §7 premises by
rfl (the W2-measured shape). -/
structure Hygiene (k : Cont) : Prop where
  mapFree : mapIterFree k = true
  recoverRefuting : recoverThroughWrappers k = none

/-! ## `I` -/

/-- **THE INVARIANT `I`** (the adopted note's §1, assembled):

    I = Base ∧ Pair ∧ Hygiene ∧ Stream ∧ (Electing ∨ Elected)

over a loop-head configuration `(σ, k, ch)` with parameters: the
voter configuration, the abstract seed `N₀`, the twin location `tl`
(located once by shape — an invariant of the seeded run, carried not
re-derived), the initial stream `ch₀`, and the `dataEnc` joint.
`CheckerCorr`/`NetCorr` sit inside the `pair` conjunct (the note's
`⊆ Pair`), sharing the carrier pack's witnesses — including `A.tm`,
which the Elected branch pins as `ElectedAt`'s term (the term-bound
clause and the phase term are the SAME witness). `Stream` is the
standing threading discipline's state half: the current stream is a
SUFFIX of the initial one (per-round suffix accounting — the shape
`mapPickLoop_generic` realizes; span-level ∀ch/draw-quantification
lives in the specs, not in the state).

**U3.0d C5/U4 verdict (charter Amendment 1 item 4, recorded):** the
D-11 jitter draw runs on every `reset` but is unobservable in T1
(census U4 — `pastElectionTimeout` unreachable). The clauses AS
LANDED absorb such dead draws with no amendment: `Stream` is
draw-count-agnostic (any span leaves a suffix), and the span-level
judgment's ∀ch discipline (`headD 0`/`tail` forms, `ch' <:+ ch`)
constrains nothing about a consumed draw's VALUE. The landed
demonstration is `becomeFollower_callSpec` itself, whose span already
consumes the jitter draw among its stream pops (becomeFollower →
`reset` → `resetRandomizedElectionTimeout`) and whose statement is
value-agnostic in it. -/
structure I (dataEnc : List Int → Nat → Prop) (voters : List Nat)
    (N₀ : SNet) (tl : Loc) (ch₀ : Choices)
    (σ : ExecState) (k : Cont) (ch : Choices) : Prop where
  base : Base σ tl
  pair : ∃ (tv : AbsTwinV0) (A : AbsCarrier),
    absTwinRead σ tl = some tv ∧
    Pair voters N₀ σ tl tv A ∧
    CheckerCorr dataEnc voters N₀ σ tl tv A ∧
    NetCorr dataEnc σ tl tv A ∧
    (Electing tv A ∨
      ∃ (ldr : Nat) (H₀ NH : HNet),
        ElectedAt dataEnc voters σ tl tv A ldr A.tm H₀ NH)
  hygiene : Hygiene k
  stream : ch <:+ ch₀

/-! ## Sanity lemmas (cheap; definedness/projection/collapse only —
preservation and establishment are later waves', by charter) -/

/-- Definedness projection: `I` implies the twin lift is defined
(C1's lift-definedness clause, surfaced). -/
theorem I.twinRead {dataEnc voters N₀ tl ch₀ σ k ch}
    (h : I dataEnc voters N₀ tl ch₀ σ k ch) :
    ∃ tv, absTwinRead σ tl = some tv :=
  h.base.twinRead

/-- **The S1 chain plugs in**: any `I`-state's abstract carrier
satisfies `oneLeaderPerTerm` — the etcd discharge + the native chain
applied to the pair clause's seed/reach. (A consistency check that
the carrier is the chain's subject, not a proof of any end-theorem
quantifier.) -/
theorem I.abs_oneLeaderPerTerm {dataEnc voters N₀ tl ch₀ σ k ch}
    (h : I dataEnc voters N₀ tl ch₀ σ k ch) :
    ∃ (tv : AbsTwinV0) (A : AbsCarrier),
      absTwinRead σ tl = some tv ∧ oneLeaderPerTerm A.N := by
  obtain ⟨tv, A, htv, hp, -, -, -⟩ := h.pair
  exact ⟨tv, A, htv,
    native_one_leader_per_term (etcd_discharges voters) hp.seed hp.reach⟩

/-- The endpoint-named trace serves every landed-`ClaimTrace`
consumer (the forgetting map, applied at the S1 leaf's premise
shape). -/
theorem CheckerCorr.claimTrace {dataEnc voters N₀ σ tl tv A}
    (h : CheckerCorr dataEnc voters N₀ σ tl tv A) :
    ClaimTrace (EStep voters) N₀ A.evsS1 :=
  h.trace.toClaimTrace

/-- Electing-phase collapse: the claims counter reads 0 (the fold
equation composed with the phase's empty history — the C3 equations
have computational teeth). -/
theorem claims_zero_of_electing {dataEnc voters N₀ σ tl tv A}
    (hc : CheckerCorr dataEnc voters N₀ σ tl tv A)
    (he : Electing tv A) : tv.claims = 0 := by
  have h := hc.claims
  rw [he.noClaims] at h
  simpa [s1Run] using h

/-- Electing-phase collapse: the violation counter reads 0. -/
theorem violations_zero_of_electing {dataEnc voters N₀ σ tl tv A}
    (hc : CheckerCorr dataEnc voters N₀ σ tl tv A)
    (he : Electing tv A) : tv.violations = 0 := by
  have h := hc.violations
  rw [he.noClaims, he.noApplies] at h
  simpa [s1Run, s23Run] using h

/-- Term-bound collapse (U3.0d): every abstract node term is bounded
by the campaign term — the usable one-sided form of the `terms`
disjunction. -/
theorem Pair.term_le {voters N₀ σ tl tv A}
    (hp : Pair voters N₀ σ tl tv A) (i : Nat) :
    (A.N.node i).term ≤ A.tm := by
  rcases hp.terms i with h | h
  · rw [h]; exact Nat.zero_le _
  · exact Nat.le_of_eq h

/-- Term-bound collapse (U3.0d): a live net message is never
term-local — its term is the campaign term, which is positive
(what refutes the `m.Term == 0` prelude branch at wire deliveries). -/
theorem NetCorr.net_term_pos {dataEnc voters N₀ σ tl tv A}
    (hn : NetCorr dataEnc σ tl tv A) (hp : Pair voters N₀ σ tl tv A)
    {lm : Bool × AbsMessage} (hmem : lm ∈ tv.net) (hlive : lm.1 = true) :
    (1 : Int) ≤ lm.2.term := by
  have h := hn.netTerms lm hmem hlive
  rw [show lm.2.term = (A.tm : Int) from h]
  exact_mod_cast hp.tmPos

/-- An Elected `I`-state's leader really is the carrier's unique
same-term leader candidate: the victory is on the ghost record (the
phase is justified by C4/ghost evidence, never by assertion). -/
theorem ElectedAt.victory_recorded {dataEnc voters σ tl tv A ldr tm H₀ NH}
    (h : ElectedAt dataEnc voters σ tl tv A ldr tm H₀ NH) :
    ∃ q, isQuorum voters q ∧ (tm, ldr, q) ∈ A.N.ghost.victories :=
  h.victory

/-- The Elected H-carrier maintains the history invariant at `NH`
(the chain's own preservation, surfaced as a projection — what the
S2/S3 leaves consume at W5). -/
theorem ElectedAt.histInv_end {dataEnc voters σ tl tv A ldr tm H₀ NH}
    (h : ElectedAt dataEnc voters σ tl tv A ldr tm H₀ NH) :
    HistInv ldr tm NH :=
  histInv_reachable h.histInv h.star

end GoLean.RaftSeam.Inv
