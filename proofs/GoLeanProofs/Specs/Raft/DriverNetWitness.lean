import GoLeanProofs.Specs.Raft.DriverNet

/-!
# A4-U20 (C2b): the driver-net span WITNESSES (non-vacuity gate)

Every premise of `rebuildLoop_span` and `liveCountLoop_span`
discharged on a concrete state (`wσ`: a 9-cell heap carrying the
twin route, the control cells, the live map, and the counter, at
`bs = [true, false]`), plus the CENSUS CROSS-CHECK: the compiled
walk's exact step counts (`152` rebuild = 63 + 58 + 31;
`157` liveCount = 68 + 58 + 31 — `#eval`-verified first, per the
`#eval`-before-`decide` rule) are kernel-replayed and shown to sit
INSIDE the spans' bounds (`165 = 67·2 + 31`, `175 = 72·2 + 31`),
with the abstract readouts delivered: the live map holds exactly
`[0]` (`liveIdx [true, false] 2`), the counter exactly `1`
(`countTrue [true, false] 2`).

The genuinely-external premises left open: none — every hypothesis
of both spans is discharged below (`decide`/`rfl`/`simp` on the
concrete state), so neither law is a scaffold.
-/

namespace GoLean.RaftSeam.DriverNet

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceWalk

set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

/-! ## The witness state -/

def wFs : Array (String × GoValue) :=
  #[("live", .slice ⟨some (.base ⟨2⟩), 0, 2, 2⟩)]

def wHeap : Heap :=
  [(.base ⟨0⟩, ⟨some (.pointer tyTwin), .addr (.base ⟨1⟩)⟩),
   (.base ⟨1⟩, ⟨some tyTwin, .struct tidTwin wFs⟩),
   (.base ⟨2⟩, ⟨some (.slice .bool), .array #[.bool true, .bool false]⟩),
   (.base ⟨3⟩, ⟨some .bool, .bool true⟩),
   (.base ⟨4⟩, ⟨some tI, .int 0 .int⟩),
   (.base ⟨5⟩, ⟨some tI, .int 2 .int⟩),
   (.base ⟨6⟩, ⟨some (.map tI .bool), .map ⟨some (.base ⟨7⟩)⟩⟩),
   (.base ⟨7⟩, ⟨none, .mapData #[]⟩),
   (.base ⟨8⟩, ⟨some tI, .int 0 .int⟩)]

def wEnv : LocalEnv :=
  [[("t", .base ⟨0⟩), ("live", .base ⟨6⟩), ("c", .base ⟨8⟩),
    ("$rfirst", .base ⟨3⟩), ("$ridx", .base ⟨4⟩), ("$rlen", .base ⟨5⟩)]]

def wσ : ExecState := { heap := wHeap, nextAddr := 9 }

def wBs : List Bool := [true, false]

/-- The witness heap misses every address at or past the frontier. -/
theorem lookup_of_freshKeys {x : Nat} (hx : wσ.nextAddr ≤ x) :
    Heap.lookup wσ.heap (.base ⟨x⟩) = none :=
  GoLean.Surface.lookup_of_keysBelow (by decide) hx

/-! ## The invariant seeds -/

theorem wRebuildInv0 :
    RebuildInv 3 4 5 0 1 2 6 7
      (some (.pointer tyTwin)) (some tyTwin) (some (.slice .bool))
      (some (.map tI .bool)) wFs wBs 9 0 wσ := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro x hx
  exact lookup_of_freshKeys hx

theorem wLiveCountInv0 :
    LiveCountInv 3 4 5 0 1 2 8
      (some (.pointer tyTwin)) (some tyTwin) (some (.slice .bool))
      wFs wBs 9 0 wσ := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro x hx
  exact lookup_of_freshKeys hx

/-! ## The span discharges (THE WITNESSES) -/

/-- **The rebuild-span witness**: every premise discharged at `wσ`. -/
theorem rebuild_span_witness :
    ∃ m ≤ 67 * wBs.length + 31, ∃ σf,
      RebuildInv 3 4 5 0 1 2 6 7
        (some (.pointer tyTwin)) (some tyTwin) (some (.slice .bool))
        (some (.map tI .bool)) wFs wBs 9 wBs.length σf
      ∧ stepFnIter m wσ
          (headCfg "$rfirst" "$ridx" "$rlen" "j" (guardedBody "j" rebThn)
            wEnv .stop) []
          = .ok (.next .stop, glueState 3 4 wBs.length σf, []) := by
  have h := rebuildLoop_span (envW := wEnv) (k := .stop)
    (lf := 3) (li := 4) (ll := 5) (lt := 0) (tw := 1) (lb := 2)
    (lm := 6) (bMap := 7)
    (dtyT := some (.pointer tyTwin)) (dtyTw := some tyTwin)
    (dtyB := some (.slice .bool)) (dtyM := some (.map tI .bool))
    (fs := wFs) (bs := wBs) (cap := 2) (na0 := 9)
    (by decide) (by decide)
    (by intro x hx <;> simp at hx <;> omega)
    (by intro x hx <;> simp at hx <;> omega)
    rfl rfl rfl rfl rfl rfl (by decide) (by decide)
    wσ [] wRebuildInv0
  exact h

/-- **The liveCount-span witness.** -/
theorem liveCount_span_witness :
    ∃ m ≤ 72 * wBs.length + 31, ∃ σf,
      LiveCountInv 3 4 5 0 1 2 8
        (some (.pointer tyTwin)) (some tyTwin) (some (.slice .bool))
        wFs wBs 9 wBs.length σf
      ∧ stepFnIter m wσ
          (headCfg "$rfirst" "$ridx" "$rlen" "i" (guardedBody "i" incThn)
            wEnv .stop) []
          = .ok (.next .stop, glueState 3 4 wBs.length σf, []) := by
  have h := liveCountLoop_span (envW := wEnv) (k := .stop)
    (lf := 3) (li := 4) (ll := 5) (lt := 0) (tw := 1) (lb := 2)
    (lc := 8)
    (dtyT := some (.pointer tyTwin)) (dtyTw := some tyTwin)
    (dtyB := some (.slice .bool))
    (fs := wFs) (bs := wBs) (cap := 2) (na0 := 9)
    (by decide) (by decide)
    (by intro x hx <;> simp at hx <;> omega)
    (by intro x hx <;> simp at hx <;> omega)
    rfl rfl rfl rfl rfl rfl (by decide) (by decide)
    wσ [] wLiveCountInv0
  exact h

/-! ## The census cross-check (kernel-replayed exact runs)

The compiled walk (`artifacts/probe/C2bWitnessGen.lean`, `#eval`-run
first): rebuild reaches `.next .stop` in exactly 152 steps
(63 first/true + 58 subsequent/false + 31 exit), liveCount in 157
(68 + 58 + 31) — the composed schema costs, reproduced step-exact on
a state the schema was never fitted to. -/

def rebuildPost : Option (Heap × Nat) :=
  match stepFnIter 152 wσ
    (headCfg "$rfirst" "$ridx" "$rlen" "j" (guardedBody "j" rebThn)
      wEnv .stop) [] with
  | .ok (.next .stop, σf, []) => some (σf.heap, σf.nextAddr)
  | _ => none

def lcPost : Option (Heap × Nat) :=
  match stepFnIter 157 wσ
    (headCfg "$rfirst" "$ridx" "$rlen" "i" (guardedBody "i" incThn)
      wEnv .stop) [] with
  | .ok (.next .stop, σf, []) => some (σf.heap, σf.nextAddr)
  | _ => none

theorem rebuild_census_link :
    rebuildPost.map (fun p => (Heap.lookup p.1 (.base ⟨7⟩),
      Heap.lookup p.1 (.base ⟨4⟩), p.2))
      = some (some ⟨none, .mapData (bEntries (liveIdx wBs 2))⟩,
          some (idxCell 2), 11) := by
  kernel_rfl

theorem liveCount_census_link :
    lcPost.map (fun p => (Heap.lookup p.1 (.base ⟨8⟩), p.2))
      = some (some (idxCell (countTrue wBs 2 : Int)), 11) := by
  kernel_rfl

end GoLean.RaftSeam.DriverNet
