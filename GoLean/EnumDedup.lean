import Std.Data.HashMap
import GoLean.GoCore.EnumDedupCheck
import GoLean.GoCore.MachineEqb

/-!
# The dedup ENGINE (POR slice P4 — the untrusted half)

The optimized enumerator (design note
`docs/2026-08-21_w32-por-design.md` §3): a worklist search over the
pool's `(MultiConfig, RaceState)` state graph, deduplicating states so
schedule-path multiplicity collapses to the grid. UNTRUSTED and
DELETABLE — nothing in `GoLean/GoCore/**` or `proofs/**` imports this
file (the deletion test; only the CLI does), no theorem mentions it,
and its output is only ever consumed through the VERIFIED checker
(`checkCert`, `EnumDedupCheck.lean`): a bug here can at worst make the
checker refuse (or waste work), never certify a wrong set —
`checkCert_slowObs` is about the checker alone.

Internals, all performance-only: the visited map keys a hand-rolled
cheap hash (collisions resolved by the COMPILED derived `BEq` — the
logically-opaque instance, fine here: the checker re-validates every
edge against the SOUND equality `dedupNodeEqb`); witness streams are
the discovery-path edge vectors (an `execProgLoop` replay artifact the
checker re-runs — a wrong witness is a refused certificate).
-/

namespace GoLean.EnumDedup

open GoLean.GoCore GoLean.GoCore.Machine

/-- Cheap structural summary hash (performance only). -/
private def configTag : Config → UInt64
  | .exec _ _ _ => 1
  | .evalE _ _ _ => 2
  | .retV _ _ => 3
  | .next _ => 4
  | .breaking _ => 5
  | .continuing _ => 6
  | .returning _ => 7
  | .breakingTo _ _ => 8
  | .continuingTo _ _ => 9
  | .panicking _ _ => 10
  | .panicked _ => 11
  | .blockedSend _ _ _ => 12
  | .blockedRecv _ _ _ _ _ => 13
  | .blockedSelect _ _ _ => 14
  | .opDone _ _ => 15
  | .blockedSync _ _ _ _ => 16

private def contDepth : Nat → Cont → Nat
  | 0, _ => 0
  | fuel + 1, k =>
    match k with
    | .stop => 0
    | .seq _ _ k => contDepth fuel k + 1
    | .loop _ _ _ k => contDepth fuel k + 1
    | .frame _ _ _ _ k _ => contDepth fuel k + 1
    | .breakableK k => contDepth fuel k + 1
    | .labelK _ k => contDepth fuel k + 1
    | _ => 1

private def configHash : Config → UInt64
  | c =>
    let tag := configTag c
    let d : UInt64 :=
      match c with
      | .exec _ _ k => UInt64.ofNat (contDepth 64 k)
      | .evalE _ _ k => UInt64.ofNat (contDepth 64 k)
      | .retV _ k => UInt64.ofNat (contDepth 64 k)
      | .next k => UInt64.ofNat (contDepth 64 k)
      | .opDone _ inner => 31 + configTag inner
      | _ => 0
    tag * 131 + d

private def nodeHash (nd : DedupNode) : UInt64 :=
  let hThreads := nd.m.threads.foldl
    (fun (h : UInt64) c => h * 1099511628211 + configHash c) 14695981039346656037
  let cellHash : ShadowCell → UInt64 := fun sc =>
    sc.reads.foldl (fun (h : UInt64) e =>
        h * 31 + UInt64.ofNat e.1 * 7 + UInt64.ofNat e.2) 3
      + sc.writes.foldl (fun (h : UInt64) e =>
          h * 37 + UInt64.ofNat e.1 * 11 + UInt64.ofNat e.2) 5
      + sc.atomicReads.foldl (fun (h : UInt64) e =>
          h * 41 + UInt64.ofNat e.1 * 13 + UInt64.ofNat e.2) 7
      + sc.atomicWrites.foldl (fun (h : UInt64) e =>
          h * 43 + UInt64.ofNat e.1 * 17 + UInt64.ofNat e.2) 11
  let hClocks := nd.r.clocks.foldl
    (fun (h : UInt64) vc =>
      vc.foldl (fun (h : UInt64) n => h * 1000003 + UInt64.ofNat n) (h * 31))
    (UInt64.ofNat nd.r.shadow.length)
  let hShadow := nd.r.shadow.foldl
    (fun (h : UInt64) e => h * 262147 + cellHash e.2) 17
  let hChans := nd.r.chans.foldl
    (fun (h : UInt64) e =>
      e.2.slots.foldl (fun (h : UInt64) vc =>
        vc.foldl (fun (h : UInt64) n => h * 179 + UInt64.ofNat n) (h * 23))
        (h * 29 + UInt64.ofNat e.2.sendCount * 41
          + UInt64.ofNat e.2.recvCount * 59)) 13
  hThreads * 131
    + UInt64.ofNat nd.m.cur * 1009
    -- `nextAddr` IS `heap.size` on the dense heap (A2); both terms kept so
    -- the hash values are unchanged (they were always equal on a dense heap).
    + UInt64.ofNat nd.m.shared.nextAddr * 10007
    + UInt64.ofNat nd.m.shared.heap.size * 100003
    + hClocks + hShadow * 3 + hChans * 7

/-- The engine's node equality for dedup: the SOUND tower equality
(`dedupNodeEqb`, MachineEqb) — here it is a performance choice, not a
trust surface (a fuel-exhausted `false` only duplicates a node). -/
private def nodeBEq (a b : DedupNode) : Bool :=
  dedupNodeEqb a b

/-- Engine-side refusal diagnostics (mirrors `innerVecs`' branches;
performance/reporting only — the checker's refusal stays authoritative). -/
private def refusalReason (s : ExecState) (ts : Array Config) (i : Nat) :
    String :=
  match ts[i]? with
  | none => s!"goroutine {i}: index out of range"
  | some c =>
    if isBlockedConfig c then s!"goroutine {i}: blocked shape not wake-certified (poolThreadOblivious false)"
    else if consumesSelect c then
      match arrivalCases s ts i c with
      | .ok .cellPath => s!"goroutine {i}: consuming select apply (multi-ready .picks — L2 entry pick)"
      | .ok (.single _ _) => s!"goroutine {i}: partnered select arrival (.single)"
      | .ok (.multi _) => s!"goroutine {i}: multi-ready select arrival (L2 .multi)"
      | .error e => s!"goroutine {i}: select arrival analysis error: {e.message}"
    else if consumesAppendSlice c then s!"goroutine {i}: append spill capacity pick"
    else if consumesTryLock c then s!"goroutine {i}: TryLock/TryRLock apply (the tryLock spurious-failure site — outside the dedup checker's certified fragment; use the default enumerator)"
    else if isMapIterNext c then s!"goroutine {i}: mapIterK iteration pick"
    else if consumesNilValueMethod s c then s!"goroutine {i}: frame-entry panic-text pick (nilValueMethodText, BUG-087)"
    else
      match arrivalCases s ts i c with
      | .ok (.multi _) => s!"goroutine {i}: multi-ready select arrival (L2 .multi)"
      | .error e => s!"goroutine {i}: arrival analysis error: {e.message}"
      | _ => s!"goroutine {i}: unclassified refusal (config tag {configTag c})"

private def nodeRefusal (m : MultiConfig) : String :=
  match m.threads[m.cur]? with
  | none => "running goroutine out of range"
  | some c =>
    if c.atBoundary then
      match schedSlots m.shared m.threads m.cur c.boundarySite with
      | [] => "empty scheduling menu"
      | rs =>
          String.intercalate "; " ((rs.filter
            (fun i => (innerVecs m.shared m.threads i).isNone)).map
            (refusalReason m.shared m.threads))
    else refusalReason m.shared m.threads m.cur

/-- Per-node observation (the terminal classification `checkNode`
mirrors), or `none` for a stepping node; `.error` = a shape the lane
fails loud on (deadlock / readout failure / non-normal outcome). -/
private def nodeObs (resultLocs : List Loc) (nd : DedupNode) :
    Except String (Option (Obs × Bool)) := do
  -- the Bool: does the node ALSO step (the L5 window)?
  if nd.m.threads.isEmpty then throw "thread pool without a main goroutine"
  else
    match nd.m.panicMsg? with
    | some msg => return some (.terminal (.panic msg), false)
    | none =>
      match nd.m.mainOutcome? with
      | some (.normal σf) =>
          match loadMany σf resultLocs with
          | .error e => throw s!"result readout failed at a terminal: {e.message}"
          | .ok vs =>
              match runnableIdxs nd.m.shared nd.m.threads with
              | [] => return some (.ok vs, false)
              | _ :: _ => return some (.ok vs, true)
      | some _ => throw "main terminal outside its barrier frame"
      | none =>
          if (runnableIdxs nd.m.shared nd.m.threads).isEmpty then
            throw "deadlock state reached — deadlocking members have no membership handling (fail loud)"
          else
            return none

structure EngineStats where
  nodes : Nat := 0
  edges : Nat := 0
  dedupHits : Nat := 0
  members : Nat := 0

structure EngineState where
  nodes : Array DedupNode := #[]
  /-- Discovery info per node: the witness stream REACHING it and its
  pool-step count (for witness fuel). -/
  paths : Array (List Nat × Nat) := #[]
  succ : Array (Array Nat) := #[]
  members : Array (Obs × Choices × Nat) := #[]
  visited : Std.HashMap UInt64 (List Nat) := {}
  stats : EngineStats := {}

private def recordMember (st : EngineState) (o : Obs) (w : Choices)
    (fuel : Nat) : EngineState :=
  if st.members.any (fun t => Obs.eqb t.1 o) then st
  else { st with
         members := st.members.push (o, w, fuel)
         stats := { st.stats with members := st.stats.members + 1 } }

/-- Find-or-insert a node; returns its index and whether it was new. -/
private def internNode (st : EngineState) (nd : DedupNode)
    (path : List Nat × Nat) : EngineState × Nat × Bool :=
  let h := nodeHash nd
  let bucket := st.visited.getD h []
  match bucket.find? (fun k => match st.nodes[k]? with
    | some nd' => nodeBEq nd nd'
    | none => false) with
  | some k =>
      ({ st with stats := { st.stats with dedupHits := st.stats.dedupHits + 1 } },
       k, false)
  | none =>
      let k := st.nodes.size
      ({ st with
         nodes := st.nodes.push nd
         paths := st.paths.push path
         succ := st.succ.push #[]
         visited := st.visited.insert h (k :: bucket)
         stats := { st.stats with nodes := st.stats.nodes + 1 } },
       k, true)

/-- Explore the graph to closure (worklist DFS; `budget` bounds
node+edge work, fail loud). -/
private partial def explore (resultLocs : List Loc) (budget : Nat)
    (st : EngineState) (stack : List Nat) :
    Except String EngineState := do
  match stack with
  | [] => return st
  | k :: stack =>
    if st.stats.nodes + st.stats.edges > budget then
      let maxBucket := st.visited.fold (fun acc _ v => max acc v.length) 0
      throw s!"dedup work budget exceeded ({st.stats.nodes} nodes, {st.stats.edges} edges, {st.stats.dedupHits} hits, {st.visited.size} hashes, maxBucket {maxBucket}) — raise the row's work cap"
    else
      match st.nodes[k]?, st.paths[k]? with
      | some nd, some (path, steps) => do
        -- terminal classification (members + whether the node steps)
        let stepping ← do
          match ← nodeObs resultLocs nd with
          | some (o, alsoSteps) =>
              -- witness: reach the node, then (at an open L5 window)
              -- pick exit 0 — the empty tail's default covers it, so
              -- the reaching stream itself is the witness.
              pure (some (recordMember st o path (steps + 1), alsoSteps))
          | none => pure (some (st, true))
        match stepping with
        | none => explore resultLocs budget st stack   -- unreachable
        | some (st, false) => explore resultLocs budget st stack
        | some (st, true) =>
          -- branch: the CHECKER's own vector enumeration
          match nodeVecs nd.m with
          | none =>
              throw s!"refused consumption shape at node {k} (outside the certified fragment): {nodeRefusal nd.m} — this row cannot use engine=dedup"
          | some vecs => do
            -- at an open L5 window, edge streams need the continue pick
            let window ←
              match ← nodeObs resultLocs nd with
              | some (_, true) => pure true
              | _ => pure false
            let mut stM := st
            let mut newIdxs : List Nat := []
            let mut succs : Array Nat := #[]
            for vec in vecs do
              match stepMulti nd.m vec with
              | .error e =>
                  throw s!"machine step failed at node {k} under vector {vec}: {e.message}"
              | .ok (m', chRem, ev) =>
                if !chRem.isEmpty then
                  throw s!"vector not fully consumed at node {k}: {vec} left {chRem}"
                else if !ev.out.isEmpty then
                  -- Output is a TRACE, not state (stdlib slice 3; G-OUT): this
                  -- engine keys nodes on (pool, detector) alone, so two paths
                  -- printing "ab" and "ba" would MERGE and the certified set
                  -- would lose a member. Refuse by name; the default (path)
                  -- enumerator carries printing rows.
                  throw s!"output event at node {k} (a print/println step wrote {ev.out.length} chunk(s)): engine=dedup keys nodes on state and output is a trace — this row cannot use engine=dedup (use the default enumerator)"
                else
                  let edgeStream := path ++ (if window then 1 :: vec else vec)
                  match raceUpdate nd.m.shared nd.m.threads ev m' nd.r with
                  | .ok r' =>
                      let (st', k', isNew) := internNode stM ⟨m', r'⟩
                        (edgeStream, steps + 1)
                      stM := { st' with stats :=
                        { st'.stats with edges := st'.stats.edges + 1 } }
                      succs := succs.push k'
                      if isNew then newIdxs := k' :: newIdxs
                  | .error .raceDetected =>
                      stM := recordMember stM (.terminal .raceDetected) edgeStream (steps + 2)
                      stM := { stM with stats :=
                        { stM.stats with edges := stM.stats.edges + 1 } }
                      succs := succs.push 0
                  | .error e =>
                      throw s!"race-detector update failed at node {k}: {e.message}"
            stM := { stM with succ := stM.succ.set! k succs }
            explore resultLocs budget stM (newIdxs ++ stack)
      | _, _ => throw "internal: dangling worklist index"

/-- Run the engine from a seeded pool: the certificate plus stats.
The caller (CLI) MUST pass the result through `checkCert` — nothing
here is trusted. -/
def buildCert (resultLocs : List Loc) (m₀ : MultiConfig) (r₀ : RaceState)
    (budget : Nat) : Except String (DedupCert × EngineStats) := do
  let root : DedupNode := ⟨m₀, r₀⟩
  let (st, _, _) := internNode {} root ([], 0)
  let st ← explore resultLocs budget st [0]
  return (⟨st.nodes, st.succ, st.members⟩, st.stats)

end GoLean.EnumDedup
