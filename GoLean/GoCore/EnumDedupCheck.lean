import GoLean.GoCore.MultiStreams
import GoLean.GoCore.EnumSpec
import GoLean.GoCore.StateEqb

/-!
# The dedup-certificate CHECKER (POR slice P3 — the verified half)

Design note `docs/2026-08-21_w32-por-design.md` §3. The optimized
enumerator (`GoLean/EnumDedup.lean` — untrusted, deletable) emits a
`DedupCert`: the closed state graph (nodes = `MultiConfig × RaceState`
pairs, root at index 0), per-node successor-index hints for each of the
checker's OWN branch vectors, and the observation members each with a
realizing witness stream + fuel. This file is the total, fail-closed
checker; `EnumDedupSound.lean` proves `checkCert = true` ⟹ the member
set EQUALS `SlowObs` (set equality — completeness is the dangerous
direction, and it rests on the per-node branch-vector coverage lemmas
there, never on the engine).

The certified shape classes (the fragment, §4 of the note):
- **N-OBL** — the stepping target satisfies `poolThreadOblivious`
  (the ∀-streams checker's flags): one vector, no inner picks.
- **N-L4** — the target is a single-arrival multi-candidate pairing
  (`arrivalCases = .ok (.single _ cs)`, `2 ≤ cs.length`): one vector
  per waiter pick.
Everything else — L2 `.multi` arrivals, consuming selects, `mapIterK`
picks, append spills — REFUSES (`none`), the Sym quit mold: a row
needing a refused shape stays on the DFS engine with its existing
trust story.

The node-equality function is a PARAMETER (`nodeEqb`) with its
soundness (`nodeEqb a b = true → a = b`) a hypothesis of the theorem —
the concrete instance (the `MachineEqb` state tower) plugs in at the
end; only SOUNDNESS is needed, so a too-weak equality (fuel
exhaustion) refuses certificates, never accepts wrong ones.
-/

namespace GoLean.GoCore.Machine

open GoLean

/-- One certificate node: a reachable pool state with its detector
state. -/
structure DedupNode where
  m : MultiConfig
  r : RaceState

/-- The dedup certificate (engine-emitted, checker-validated). -/
structure DedupCert where
  /-- The closed state graph's nodes; index 0 must be the seeded
  root. -/
  nodes : Array DedupNode
  /-- Per node, per branch vector (in `nodeVecs`' order), the
  SUCCESSOR's node index — the engine's dedup knowledge handed over as
  hints, so the checker never needs a map. Race-refusing edges still
  carry an entry (ignored). -/
  succ : Array (Array Nat)
  /-- The observation members, each with a realizing choice stream and
  a fuel that completes it (witnesses — the soundness direction is
  their replay). -/
  members : Array (Obs × Choices × Nat)

/-- The claimed observation set. -/
def DedupCert.obsSet (cert : DedupCert) : List Obs :=
  cert.members.toList.map (·.1)

/-- Structural observation equality (sound; `GoValue.eqb` under the
hood). -/
def Obs.eqb : Obs → Obs → Bool
  | .ok vs, .ok ws => eqbListP GoValue.eqb vs ws
  | .panic a, .panic b => a == b
  | .race, .race => true
  | _, _ => false

/-- Is `o` among the members? -/
def obsMem (mems : Array (Obs × Choices × Nat)) (o : Obs) : Bool :=
  mems.toList.any fun t => Obs.eqb t.1 o

/-- Does this `appendSlice` apply avoid the spill's capacity pick —
i.e. is the step stream-oblivious? Mirrors `applyStmtOp`'s own spill
analysis (`valueAsSlice` → `sliceVisibleValues` → `newLen ≤ cap`);
every ERROR path of the arm is stream-free, so `true` on them is
still oblivious, and only the genuine spill branch (the one
`Choices.consumeAt .appendSpill` consult) refuses. -/
def appendApplyNoSpill (s : ExecState) : List GoValue → Bool
  | [_, sliceV, elemsV] =>
      (match valueAsSlice sliceV, valueAsSlice elemsV with
      | .ok slice, .ok elems =>
          (match sliceVisibleValues s elems with
          | .ok elemValues => slice.len + elemValues.size ≤ slice.cap
          | .error _ => true)
      | _, _ => true)
  | _ => true

/-- The INNER branch vectors for stepping goroutine `i`: the pick
suffix each enumerated branch feeds to the goroutine-step, or `none`
when the target's consumption shape is outside the certified fragment
(fail closed). `[[]]` for an oblivious target (the step consumes
nothing — `stepThread_oblivious`); one singleton vector per waiter
pick at an N-L4 pairing. -/
def innerVecs (s : ExecState) (ts : Array Config) (i : Nat) :
    Option (List (List Nat)) :=
  if poolThreadOblivious s ts i then some [[]]
  else
    match ts[i]? with
    | none => none
    | some c =>
      if isBlockedConfig c then none
      else if (opDoneInner c).isSome then none
      else if (spawnPlan c).isSome then none
      else if consumesSelect c then none
      else if consumesAppendSlice c then
        -- N-APP: the non-spilling append apply is stream-oblivious
        -- (`stepFn_append_nospill`); a spilling one refuses.
        (match c with
         | .retV v (.stmtOpK (.appendSlice _) _ done [] _ _) =>
             if appendApplyNoSpill s ((v :: done).reverse) then some [[]]
             else none
         | _ => none)
      -- Q-TRYLOCK: the TRY heads' `tryLock` pick is outside the certified
      -- fragment (fail closed; the CLI enumerator carries such rows).
      else if consumesTryLock c then none
      else if isMapIterNext c then none
      else if consumesNilValueMethod s c then none
      else
        match arrivalCases s ts i c with
        | .ok (.single _ cs) =>
            if 2 ≤ cs.length then
              some ((List.range cs.length).map fun p => [p])
            else none
        | _ => none

/-- Branch vectors for a ≥2-slot boundary menu, slot-prefixed:
`slotVecsAux s ts rs p₀` enumerates, for the slot suffix `rs` whose
first element is menu position `p₀`, every `pick :: innerSuffix`. -/
def slotVecsAux (s : ExecState) (ts : Array Config) :
    List Nat → Nat → Option (List (List Nat))
  | [], _ => some []
  | i :: rest, pick => do
      let ivs ← innerVecs s ts i
      let tail ← slotVecsAux s ts rest (pick + 1)
      pure (ivs.map (pick :: ·) ++ tail)

/-- The node's branch vectors: every choice stream's `stepMulti` from
this node is realized by one of these explicit finite vectors (the
coverage lemma, `EnumDedupSound.lean`), or the shape is refused. -/
def nodeVecs (m : MultiConfig) : Option (List (List Nat)) :=
  match m.threads[m.cur]? with
  | none => none
  | some c =>
    if c.atBoundary then
      match schedSlots m.shared m.threads m.cur c.boundarySite with
      | [] => none
      | [i] => innerVecs m.shared m.threads i
      | r0 :: r1 :: rest => slotVecsAux m.shared m.threads (r0 :: r1 :: rest) 0
    else innerVecs m.shared m.threads m.cur

/-- One edge: the REAL `stepMulti` at the explicit vector must succeed
consuming it exactly; the detector verdict then either lands on the
hinted node (up to the sound `nodeEqb`) or refuses with `.race ∈
members`. Any other error refuses. -/
def checkEdge (nodeEqb : DedupNode → DedupNode → Bool)
    (mems : Array (Obs × Choices × Nat)) (nodes : Array DedupNode)
    (nd : DedupNode) (vec : List Nat) (succIdx : Nat) : Bool :=
  match stepMulti nd.m vec with
  | .ok (m', chRem, ev) =>
      chRem.isEmpty &&
      (match raceUpdate nd.m.shared nd.m.threads ev m' nd.r with
       | .ok r' =>
           (match nodes[succIdx]? with
            | some ndS => nodeEqb ⟨m', r'⟩ ndS
            | none => false)
       | .error .raceDetected => obsMem mems .race
       | .error _ => false)
  | .error _ => false

/-- All of a node's branch vectors, each against its successor hint. -/
def checkStep (nodeEqb : DedupNode → DedupNode → Bool)
    (mems : Array (Obs × Choices × Nat)) (nodes : Array DedupNode)
    (succs : Array Nat) (nd : DedupNode) : Bool :=
  match nodeVecs nd.m with
  | none => false
  | some vecs =>
      vecs.length == succs.size &&
      (List.range vecs.length).all fun j =>
        match vecs[j]?, succs[j]? with
        | some vec, some k => checkEdge nodeEqb mems nodes nd vec k
        | _, _ => false

/-- One node: terminal classification mirrors `execProgLoop`'s arms
(panic / main-normal (+ the L5 window's BOTH branches) / deadlock
refused / non-normal outcomes refused), stepping nodes run
`checkStep`. -/
def checkNode (nodeEqb : DedupNode → DedupNode → Bool)
    (mems : Array (Obs × Choices × Nat)) (nodes : Array DedupNode)
    (resultLocs : List Loc) (succs : Array Nat) (nd : DedupNode) : Bool :=
  if nd.m.threads.isEmpty then false
  else
    match nd.m.panicMsg? with
    | some msg => obsMem mems (.panic msg)
    | none =>
      match nd.m.mainOutcome? with
      | some (.normal σf) =>
          (match loadMany σf resultLocs with
           | .error _ => false
           | .ok vs =>
              match runnableIdxs nd.m.shared nd.m.threads with
              | [] => obsMem mems (.ok vs)
              | _ :: _ =>
                  obsMem mems (.ok vs)
                    && checkStep nodeEqb mems nodes succs nd)
      | some _ => false
      | none =>
          if (runnableIdxs nd.m.shared nd.m.threads).isEmpty then false
          else checkStep nodeEqb mems nodes succs nd

/-- Witness-replay comparison (soundness's whole content). -/
def obsOfEqb : Option Obs → Option Obs → Bool
  | some a, some b => Obs.eqb a b
  | _, _ => false

/-- **THE CHECKER** (design note §3): root at index 0, every node
checked, every member's witness replayed through the UNMODIFIED driver.
`nodeEqb` is the sound node equality (parameter; the theorem takes its
soundness as a hypothesis). -/
def checkCert (nodeEqb : DedupNode → DedupNode → Bool)
    (resultLocs : List Loc) (m₀ : MultiConfig) (r₀ : RaceState)
    (cert : DedupCert) : Bool :=
  (match cert.nodes[0]? with
   | some nd0 => nodeEqb nd0 ⟨m₀, r₀⟩
   | none => false) &&
  cert.succ.size == cert.nodes.size &&
  ((List.range cert.nodes.size).all fun k =>
     match cert.nodes[k]?, cert.succ[k]? with
     | some nd, some succs =>
         checkNode nodeEqb cert.members cert.nodes resultLocs succs nd
     | _, _ => false) &&
  (cert.members.toList.all fun t =>
     obsOfEqb (obsOf? resultLocs (execProgLoop t.2.2 m₀ r₀ t.2.1))
       (some t.1))

end GoLean.GoCore.Machine
