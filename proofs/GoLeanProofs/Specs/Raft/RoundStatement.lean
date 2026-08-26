import GoLeanProofs.Specs.Raft.RoundHbLit
import GoLeanProofs.Specs.Raft.AbsStateV2
import GoLeanProofs.Specs.Raft.AllocEq
import GoLeanProofs.FuelMeasure

/-! # The ROUND-LEMMA statement form (R-form) + the heartbeat-round
witness (A4-U18 = layer-C C1; design of record: the campaign
worktree's `docs/2026-08-25_campaign-layerc-design.md` §2 as refined
by the seam note §4c's R-form flag)

## What this module pins (C1's statement work)

1. **`Fam` membership** (`RoundFam`): the round induction's carried
   family is FIXTURE-FAMILY membership — a `FrameSim` placement of the
   round-kind's canonical loop-head state — exactly the arm equations'
   placement premise, one ring up. No new relation class: membership
   IS the alloc-primary FrameSim form the equations already ship
   (LINEAGE: refinement mapping over an inductive invariant,
   Abadi–Lamport; the placement quantifier is the U6 `frameSim_relocate`
   pattern).
2. **`AbsTwinV0` / `absTwinRead`** (A3's round-boundary reader, v0):
   total, fail-closed, first-order lens reads of the twin at the loop
   head — the checker counters, the harness-observed per-node shells
   (the §7 projection's source), and the net multiset through
   `absMessage`. The deep per-node reader (`absTwinNodeRaft`) reaches
   the delivered node's raft cell through nodes[i]→rn→raft.
3. **`RoundLemmaShape`**: the R-form round-lemma STATEMENT former —
   self-returning loop-head config (census-verified: the driver's
   `round < 400` anchor config recurs IDENTICALLY each round),
   placement-quantified pre, closure (successor-family membership) in
   the conclusion. Round-kind instances add their readout conjuncts;
   C2 proves them. THE GENERAL LEMMA IS NOT PROVED HERE — C1 ships
   the form + one witness instance, per the design gate's charter.

## The witness (statement-form validation, NOT a general lemma)

ONE concrete deliver-heartbeat round — loop head to loop head through
the driver glue (live-map rebuild, the mapIter pick, trace building),
`deliverIdx`, `RawNode.Step`, the `raft.raft.Step` glue, the
`stepFollower × MsgHeartbeat` arm, the harvest Ready cycle, and the
driver suffix — **10,964 steps, 4 choices, SELF-RETURNING** at the
generated 26-cell fixture (`RoundHbLit.lean`; the twin's REAL first
loop-head state, heartbeat-doctored and pruned to the round's
read-before-write set — probes
`artifacts/probe/{TwinRoundFixProbe,RoundFixDump}.lean`). §4 states
exactly which parts are kernel-checked (the 300-step driver-glue
sliver incl. the round's pick crossing, + the endpoint readouts) and
which are generator-verified pending C2's mirror chain (the full
replay — its naive kernel form is MEASURED-BLOCKED, the unit's
route finding). The readout theorems state the abstract round delta:
node 2's `lead` 0 → 1 (the SfHb headline at twin scale), the
MsgHeartbeatResp (typ 9, 2 → 1) appended live with the heartbeat
marked dead, and the checker counters UNCHANGED (violations 0 → 0).

CAVEATS (stated so the docstring never overclaims):
- the witness round-kind (deliver-heartbeat) is REACHABILITY-VACUOUS
  for T1 (the driver never ticks, so no stream ever nets a
  MsgHeartbeat — the U18 census finding); it validates the STATEMENT
  FORM on landed arm machinery, and the form is round-kind-independent.
- `RoundLemmaShape`'s SCAFFOLD marker is DISCHARGED (A4-U22 / C2d):
  the first proved instance is `RoundMa.roundMa_lemma`
  (`RoundMaLemma.lean`) — the REACHABLE MsgApp append-family round,
  via the canonical mirror-chain run + the weak `stepFnIter_sim`
  transport. (Original caveat, kept for the record: the C1-era form
  had no proved instance; the heartbeat witness below remains the
  form-validation artifact it always was.)
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Frame GoLean.Surface

/-! ## 1. Fam membership (the R-form's carried family) -/

/-- Fixture-family membership, pinned (design §2 / seam §4c flag):
`σF` is a member of round-family `canon` iff it is a FrameSim
placement of it. What the LANDED round induction
(`RoundInduction.lean`, A4-U26) carries per boundary is EXACTLY this
membership (`FamTrace.cons`'s `hfam` conjunct) — NOT the layer-C §3
paired form `RoundFam canon σF ∧ absTwinRead … = some N`. The
per-boundary abs-pairing (absTwinRead ↔ SNet projection) is an OPEN
obligation — census item O5b of the T1 open-obligation census
(`docs/campaign-arc4-log.md`, landing fix-round entry); until it
lands, the induction's abstract nets are witness DATA. (This
paragraph previously asserted the paired form as the carried
relation — corrected at the landing fix round, 2026-08-26.) -/
def RoundFam (canon : ExecState) (σF : ExecState) : Prop :=
  ∃ (r : Nat → Nat) (na₀ na : Nat) (fr : GoCore.Heap),
    FrameSim r na₀ na fr canon σF

/-- Every twin-program state is a member of its own family at the
identity placement (`ρT nextAddr 0` — the shift-0 renaming, pointwise
identity; the equations' identity-corollary construction, packaged
for the round vocabulary). The bodies premise is discharged by
`renameStmt_ρT_zero` — shift-0 renames every body to itself. -/
theorem RoundFam.self (σ : ExecState) : RoundFam σ σ :=
  ⟨ρT σ.nextAddr 0, σ.nextAddr, σ.nextAddr, [],
   frameSim_seed rfl (fun f _ => renameStmt_ρT_zero σ.nextAddr f.body)⟩

/-! ## 2. The round-boundary reader (A3, v0) -/

/-- The abstract twin view at a round boundary, v0: the checker
counters, the harness-observed per-node shells (state, term, commit,
applied — the §7 projection's exact source fields), and the net
multiset with liveness flags. -/
structure AbsTwinV0 where
  violations : Int
  claims : Int
  committed : Int
  nodes : List (Int × Int × Int × Int)
  net : List (Bool × AbsMessage)
  deriving Repr, DecidableEq

/-- Read a plain integer field, fail closed: anything but an `.int`
value — including `.nil` — is `none`. (The landing fix round removed a
`.nil ↦ 0` clause: the twin's shell fields are non-pointer scalars
(`uint64`/`StateType`/`int`, twin-lib.go), whose machine zero value is
`.int 0 _`, never `.nil` (Ops.lean `defaultValue`) — so a `.nil` here
can only be a mis-located or mis-shaped read and must refuse. The
protobuf pointer-scalar nil→0 convention belongs to `AbsStateV2.derefI32`
ONLY, where it is documented against pointer fields.) -/
private def readIntField (fs : Array (String × GoValue)) (n : String) :
    Option Int :=
  match StructFields.lookup fs n with
  | some (.int v _) => some v
  | _ => none

/-- The twin struct's TypeId and the shell node's — pinned so the
readers below refuse mis-located cells (landing fix round; previously
`.struct _ fs` matched ANY struct). -/
def twinTid : TypeId := ⟨"main.twin"⟩
def twinNodeTid : TypeId := ⟨"main.twinNode"⟩
def rawNodeTid : TypeId := ⟨"raft.RawNode"⟩

/-- One twinNode shell (harness-observed fields only — the deep raft
state is `absTwinNodeRaft`'s). -/
private def readShell (σ : ExecState) : GoValue → Option (Int × Int × Int × Int)
  | .addr l => do
      let c ← Heap.lookup σ.heap l
      match c.value with
      | .struct tid fs => do
          guard (tid == twinNodeTid)
          let st ← readIntField fs "state"
          let tm ← readIntField fs "term"
          let cm ← readIntField fs "commit"
          let ap ← readIntField fs "applied"
          pure (st, tm, cm, ap)
      | _ => none
  | _ => none

private def sliceElems (σ : ExecState) : GoValue → Option (List GoValue)
  | .slice sv => do
      match sv.base with
      | none => if sv.len == 0 then some [] else none
      | some b => do
          let c ← Heap.lookup σ.heap b
          match c.value with
          | .array vs =>
              let l := (vs.toList.drop sv.offset).take sv.len
              if l.length == sv.len then some l else none
          | _ => none
  | _ => none

private def readBool : GoValue → Option Bool
  | .bool b => some b
  | _ => none

/-- **THE ROUND-BOUNDARY READER, v0** (total, fail-closed; every
access through value-level lens reads — A3's deliverable; the landing
fix round hardened the fail-closed claim: the twin and shell struct
TypeIds are now CHECKED (`twinTid`/`twinNodeTid`) and the integer
reader refuses `.nil`, so a mis-located or mis-shaped cell reads back
`none`, never a well-formed abstract state). `tl` is the twin
struct's location (located once by shape; an invariant of the seeded
run, carried not re-derived). -/
def absTwinRead (σ : ExecState) (tl : Loc) : Option AbsTwinV0 := do
  let tc ← Heap.lookup σ.heap tl
  match tc.value with
  | .struct tid fs => do
      guard (tid == twinTid)
      let violations ← readIntField fs "violations"
      let claims ← readIntField fs "claims"
      let committed ← readIntField fs "committed"
      let ndPtrs ← (StructFields.lookup fs "nodes").bind (sliceElems σ)
      let nodes ← ndPtrs.mapM (readShell σ)
      let netPtrs ← (StructFields.lookup fs "net").bind (sliceElems σ)
      let msgs ← netPtrs.mapM (absMessage σ)
      let liveVs ← (StructFields.lookup fs "live").bind (sliceElems σ)
      let lives ← liveVs.mapM readBool
      if msgs.length == lives.length then
        pure { violations, claims, committed, nodes,
               net := lives.zip msgs }
      else none
  | _ => none

/-- The deep per-node reader: `twin.nodes[i] → .rn → .raft` — the
delivered node's raft cell address (then read with the lens). -/
def absTwinNodeRaft (σ : ExecState) (tl : Loc) (i : Nat) : Option Addr := do
  let tc ← Heap.lookup σ.heap tl
  match tc.value with
  | .struct tid fs => do
      guard (tid == twinTid)
      let ndPtrs ← (StructFields.lookup fs "nodes").bind (sliceElems σ)
      let ndv ← ndPtrs[i]?
      match ndv with
      | .addr ndl => do
          let nc ← Heap.lookup σ.heap ndl
          match nc.value with
          | .struct ntid nfs => do
              guard (ntid == twinNodeTid)
              match StructFields.lookup nfs "rn" with
              | some (.addr rnl) => do
                  let rc ← Heap.lookup σ.heap rnl
                  match rc.value with
                  | .struct rtid rfs => do
                      guard (rtid == rawNodeTid)
                      match StructFields.lookup rfs "raft" with
                      | some (.addr (.base a)) => some a
                      | _ => none
                  | _ => none
              | _ => none
          | _ => none
      | _ => none
  | _ => none

/-! ## 3. The round-lemma statement form (R-form) -/

/-- **THE ROUND-LEMMA STATEMENT FORMER** (SCAFFOLD marker DISCHARGED,
A4-U22/C2d — four proved instances have landed: `roundMa_lemma`,
`roundVote_lemma`, `roundMar_lemma`, `roundVr_lemma`; this docstring
previously still read "no proved instance yet", contradicting the
module header — corrected at the landing fix round). An instance for a
round kind supplies: the canonical loop-head state `canon`, the
successor canonical state `canon'`, the (shared, census-verified
self-returning) loop-head config `C0`, the round span `Δ`, and the
censused choice prefix `π`. The lemma's content, in the arm
equations' exact vocabulary one ring up: from ANY placement of the
family, the run returns to the SAME loop-head configuration with the
choice prefix consumed, and the post-state is a placement of the
successor family (closure — the R-form's membership re-established).
Instances add readout conjuncts (absTwinRead deltas) beside the
closure; the FORMER pins only the route-independent skeleton. -/
def RoundLemmaShape (canon canon' : ExecState) (C0 : Config) (Δ : Nat)
    (π : Choices) : Prop :=
  ∀ (r : Nat → Nat) (na₀ na : Nat) (fr : GoCore.Heap) (σF : ExecState),
    FrameSim r na₀ na fr canon σF →
    ∀ ch, ∃ σF',
      stepFnIter Δ σF (renameConfig r C0) (π ++ ch)
        = .ok (renameConfig r C0, σF', ch)
      ∧ ∃ na' fr', FrameSim r na₀ na' fr' canon' σF'

/-! ## 4. The heartbeat-round witness — what IS and IS NOT
kernel-checked (stated bluntly so nothing overclaims)

The full 10,964-step round replay is VERIFIED BY THE COMPILED
interpreter (probes `TwinRoundFixProbe`/`RoundFixDump`: the doctored
round walks loop-head → loop-head, self-returning config, 4 choices,
na 6,079 → 6,669; the pruned 26-cell walk step-count-identical to the
unpruned 6,079-cell walk). Its KERNEL form is MEASURED-BLOCKED on the
naive `stepFnIter`-literal route: a single 1,400-step chunk at this
fixture reached 41 GB RSS in 90 s and was cgroup-killed at 48 GB —
the same heap-linear kernel wall Arc 2's unit 2 measured
(2.22 s/step, 157 MB/step at 19k cells; seg-500 OOM), reproduced
here at a 26-cell heap: the wall is per-step TERM growth, not heap
width. The C1 verdict routes the round replay through the MIRROR
(symEvalWindow chains — the landed equations' instrument, measured
~30-40 steps/s WITHOUT the blowup) as C2's first slice.

What ships kernel-checked TODAY:
  - `rhb_glue100` / `rhb_glue300` — the round's first 100/300 steps
    (the DRIVER-GLUE head: loop-head cond, the live-map rebuild over
    the net slice, into the pick machinery — exactly the span no arm
    equation covers), kernel-replayed over the generated literals;
  - the endpoint READOUT theorems (§5): kernel-evaluated statements
    about the generated literals themselves.
The post-state literal (`rhbHeap3`)'s provenance is the generator's
compiled walk — the readouts over it are kernel-checked statements
about THAT literal, and the literal-to-fixture link beyond step 300
is generator-verified only, pending C2's mirror chain. -/

/-- The witness states over the generated literals: `wBase`'s program
tables + the pruned loop-head heap. -/
def rhbσ (h : GoCore.Heap) (na : Nat) : ExecState :=
  { wBase with heap := h, nextAddr := na }

set_option maxRecDepth 4000000

/-- The driver-glue head, steps [0,100) — kernel-replayed. -/
theorem rhb_glue100 :
    stepFnIter 100 (rhbσ rhbHeap0 rhbNa0) rhbC0 rhbCh0
      = .ok (rhbC1, rhbσ rhbHeap1 rhbNa1, rhbCh1) := by kernel_rfl

/-- Steps [100,300) — kernel-replayed. -/
theorem rhb_glue300 :
    stepFnIter 200 (rhbσ rhbHeap1 rhbNa1) rhbC1 rhbCh1
      = .ok (rhbC2, rhbσ rhbHeap2 rhbNa2, rhbCh2) := by kernel_rfl

/-- The composed 300-step driver-glue sliver (`stepFnIter_chain`). -/
theorem rhb_glue :
    stepFnIter 300 (rhbσ rhbHeap0 rhbNa0) rhbC0 rhbCh0
      = .ok (rhbC2, rhbσ rhbHeap2 rhbNa2, rhbCh2) :=
  Surface.stepFnIter_chain rhb_glue100 rhb_glue300

/-! ## 5. The witness's abstract round delta (the readouts) -/

/-- The twin struct's cell in the fixture (shape-located by the
generator; the readouts below re-verify every consequence). -/
def rhbTwinLoc : Loc := .base ⟨121⟩

/-- PRE readout: checker counters zero, three follower shells, ONE
live heartbeat (typ 8, 1 → 2) in flight. -/
theorem roundHb_pre_read :
    (absTwinRead (rhbσ rhbHeap0 rhbNa0) rhbTwinLoc).map
      (fun a => (a.violations, a.claims, a.committed,
                 a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))
      = some (0, 0, 0, [(true, 8, 1, 2)]) := by kernel_rfl

/-- POST readout: counters UNCHANGED (violations 0 — the checker held
through the round), the heartbeat marked DEAD, and the
MsgHeartbeatResp (typ 9, 2 → 1) appended LIVE — the abstract round
delta's net half. -/
theorem roundHb_post_read :
    (absTwinRead (rhbσ rhbHeap3 rhbNa3) rhbTwinLoc).map
      (fun a => (a.violations, a.claims, a.committed,
                 a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))
      = some (0, 0, 0, [(false, 8, 1, 2), (true, 9, 2, 1)]) := by kernel_rfl

/-- POST readout, the delivered node: node 2's raft `lead` field
became 1 (`lead := m.From` — the SfHb arm's headline conclusion,
now read at TWIN scale through the nodes[1]→rn→raft chain). -/
theorem roundHb_post_lead :
    (absTwinNodeRaft (rhbσ rhbHeap3 rhbNa3) rhbTwinLoc 1).bind
      (fun a => GoLean.Lens.fieldReadU64 (rhbσ rhbHeap3 rhbNa3) a
        ⟨"raft.raft"⟩ "lead") = some 1 := by kernel_rfl

/-- PRE readout, the delivered node: `lead` was 0 (no known leader). -/
theorem roundHb_pre_lead :
    (absTwinNodeRaft (rhbσ rhbHeap0 rhbNa0) rhbTwinLoc 1).bind
      (fun a => GoLean.Lens.fieldReadU64 (rhbσ rhbHeap0 rhbNa0) a
        ⟨"raft.raft"⟩ "lead") = some 0 := by kernel_rfl

end GoLean.RaftSeam
