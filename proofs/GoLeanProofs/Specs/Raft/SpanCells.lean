import GoLeanProofs.Specs.Raft.UtoaSpan
import GoLeanProofs.MapMem
import GoLeanProofs.Specs.Raft.DriverNet

/-!
# The checker's cell vocabulary + the `viol` span (A4d-SM1 item 3a)

The S1 record span (`SpanS1.lean`) reads and writes the twin struct's
counter/trace/map fields at SYMBOLIC payloads. This module carries the
shared machinery:

1. **`twinFs`** — the twin struct's field array, spelled at the
   pinned declaration's exact field order
   (`artifacts/probe/twintypes.out`), symbolic in every payload the
   checker touches. The int-typed fields must carry `.int` payloads
   (the normalization arm demands it); every other field is an opaque
   `GoValue` — `normalizeValueForTyFuel` is the identity at
   slice/map/string/bool types (no arm matches, the catch-all
   returns the value), measured off the definition, so the struct
   store's whole-struct re-normalization only touches the four int
   fields.
2. **`normalize_twinFs`** — the whole-struct normalization identity
   at in-range counters (the cost center of every field store: a
   store to a `declaredTy = main.twin` cell re-normalizes the whole
   struct against the type table).
3. **Field-store singles** (`storeTarget_twin_claims`/`_violations`/
   `_trace`) — `storeTarget` through the `fieldAddr` chain, one per
   field the checker writes.
4. **The `viol` pin + span** — `main.twin.viol` (twin-lib.go:180)
   verbatim (`utoa_pinned`'s whole-`Func` pattern) and its call span:
   `violations` incremented EXACTLY, `trace` replaced by SOME string
   (the banked weak form — the counters never depend on the text).

LINEAGE: conditioned-single machine facts (the StepKit/SliceMem
discipline); the viol span is a P-H call-span instance.
-/

namespace GoLean.RaftSeam.SpanCells

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceWalk (envB flagCell flagSet stepFn_ref normalize_bool
  lookup_pushScope)
open GoLean.CondFor
open GoLean.RaftSeam.UtoaSpan
open GoLean.RaftSeam.DriverNet (tyTwin tidTwin applyStrictOp_deref
  applyStrictOp_fieldGet)
open GoLean.Examples.RaftTwin (twinLowered)
open GoLean.StringMem (gs)
open GoLean.MapMem (toEntries idxOf? cnt setk)

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-! ## 1. The twin struct at symbolic payloads -/

/-- The twin struct's field array at the pinned declaration's order —
symbolic in every checker-relevant payload. `lm` is the `leaderOf`
map's data-cell address; the four int fields carry `.int` payloads
(the normalization arm demands the shape); everything else is opaque. -/
def twinFs (nodesV netV liveV : GoValue) (lm : Nat) (byV : GoValue)
    (c cm w : Int) (pendV drvV : GoValue) (sq : Int) (tr : GoString)
    (hlV : GoValue) : Array (String × GoValue) :=
  #[("nodes", nodesV), ("net", netV), ("live", liveV),
    ("leaderOf", .map ⟨some (.base ⟨lm⟩)⟩), ("byIndex", byV),
    ("claims", .int c .int), ("committed", .int cm .int),
    ("violations", .int w .int), ("pending", pendV), ("driven", drvV),
    ("seq", .int sq .int), ("trace", .string tr), ("halt", hlV)]

/-- The twin declaration, spelled (pin below). -/
def twinDecl : Array FieldDef :=
  #[⟨"nodes", .slice (.pointer (.defined ⟨"main.twinNode"⟩)), false⟩,
    ⟨"net", .slice (.pointer (.defined ⟨"raftpb.Message"⟩)), false⟩,
    ⟨"live", .slice .bool, false⟩,
    ⟨"leaderOf", .map (.int .uint64) (.int .uint64), false⟩,
    ⟨"byIndex", .map (.int .uint64) (.defined ⟨"main.slot"⟩), false⟩,
    ⟨"claims", .int .int, false⟩,
    ⟨"committed", .int .int, false⟩,
    ⟨"violations", .int .int, false⟩,
    ⟨"pending", .slice .string, false⟩,
    ⟨"driven", .slice .string, false⟩,
    ⟨"seq", .int .int, false⟩,
    ⟨"trace", .string, false⟩,
    ⟨"halt", .bool, false⟩]

/-- **PIN**: the type table's `main.twin` IS the spelled declaration
(`artifacts/probe/twintypes.out`). -/
theorem twinDecl_pinned :
    TypeEnv.lookup twinTypes ⟨"main.twin"⟩ = some (.struct twinDecl) := by
  kernel_rfl

/-! The twin field lookups, on the spelled array (all `rfl` — the
names are concrete). -/
section FieldLookups

variable {nodesV netV liveV byV pendV drvV hlV : GoValue} {lm : Nat}
  {c cm w sq : Int} {tr : GoString}

theorem twinFs_claims :
    StructFields.lookup (twinFs nodesV netV liveV lm byV c cm w pendV
      drvV sq tr hlV) "claims" = some (.int c .int) := rfl

theorem twinFs_violations :
    StructFields.lookup (twinFs nodesV netV liveV lm byV c cm w pendV
      drvV sq tr hlV) "violations" = some (.int w .int) := rfl

theorem twinFs_trace :
    StructFields.lookup (twinFs nodesV netV liveV lm byV c cm w pendV
      drvV sq tr hlV) "trace" = some (.string tr) := rfl

theorem twinFs_leaderOf :
    StructFields.lookup (twinFs nodesV netV liveV lm byV c cm w pendV
      drvV sq tr hlV) "leaderOf"
      = some (.map ⟨some (.base ⟨lm⟩)⟩) := rfl

end FieldLookups

/-! ## 2. The whole-struct normalization identity -/

/-- In-range counters make the spelled struct its own normal form at
the twin type (the identity every field store routes through). -/
theorem normalize_twinFs {σ : ExecState}
    (htypes : σ.types = twinTypes)
    {nodesV netV liveV byV pendV drvV hlV : GoValue} {lm : Nat}
    {c cm w sq : Int} {tr : GoString}
    (hc0 : -(2 ^ 63) ≤ c) (hc1 : c < 2 ^ 63)
    (hm0 : -(2 ^ 63) ≤ cm) (hm1 : cm < 2 ^ 63)
    (hw0 : -(2 ^ 63) ≤ w) (hw1 : w < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63) :
    normalizeValueForTy σ (.defined ⟨"main.twin"⟩)
        (.struct ⟨"main.twin"⟩ (twinFs nodesV netV liveV lm byV c cm w
          pendV drvV sq tr hlV))
      = .ok (.struct ⟨"main.twin"⟩ (twinFs nodesV netV liveV lm byV
          c cm w pendV drvV sq tr hlV)) := by
  cases σ with
  | mk types functions methods methodSets heap nextAddr =>
    simp only at htypes
    subst htypes
    have hraw : normalizeValueForTy
        ⟨twinTypes, functions, methods, methodSets, heap, nextAddr⟩
        (.defined ⟨"main.twin"⟩)
        (.struct ⟨"main.twin"⟩ (twinFs nodesV netV liveV lm byV c cm w
          pendV drvV sq tr hlV))
        = .ok (.struct ⟨"main.twin"⟩ (twinFs nodesV netV liveV lm byV
            (IntKind.normalize .int c) (IntKind.normalize .int cm)
            (IntKind.normalize .int w) pendV drvV
            (IntKind.normalize .int sq) tr hlV)) := by
      kernel_rfl
    rw [hraw, GoLean.SliceMem.inorm_of_range hc0 hc1,
      GoLean.SliceMem.inorm_of_range hm0 hm1,
      GoLean.SliceMem.inorm_of_range hw0 hw1,
      GoLean.SliceMem.inorm_of_range hq0 hq1]

/-! ## 3. The pointer-field read segment -/

/-- `p.f` through a pointer variable (`fieldGet (deref (var x))`):
5 steps from the expression to the delivered field value, state
untouched. The workhorse read of every checker span. -/
theorem read_field_seg {σ : ExecState} {x : String} {env : LocalEnv}
    {K : Cont} {ch : Choices} {lp lw : Nat} {ty1 : Ty}
    {dty1 dty2 : Option Ty} {tid' : TypeId}
    {fs : Array (String × GoValue)} {f : String} {v : GoValue}
    (henv : LocalEnv.lookup env x = some (.base ⟨lp⟩))
    (hp : Heap.lookup σ.heap (.base ⟨lp⟩)
      = some ⟨dty1, .addr (.base ⟨lw⟩)⟩)
    (hw : Heap.lookup σ.heap (.base ⟨lw⟩)
      = some ⟨dty2, .struct tid' fs⟩)
    (hf : StructFields.lookup fs f = some v) :
    stepFnIter 5 σ
        (.evalE (.fieldGet (.deref (.var x) ty1) tid' f) env K) ch
      = .ok (.retV v K, σ, ch) := by
  have h1 : stepFnIter 2 σ
      (.evalE (.fieldGet (.deref (.var x) ty1) tid' f) env K) ch
      = .ok (.evalE (.var x) env
          (.strictK (.deref ty1) [] [] env
            (.strictK (.fieldGet tid' f) [] [] env K)), σ, ch) := by
    with_unfolding_all rfl
  have h2 : stepFnIter 1 σ (.evalE (.var x) env
      (.strictK (.deref ty1) [] [] env
        (.strictK (.fieldGet tid' f) [] [] env K))) ch
      = .ok (.retV (.addr (.base ⟨lw⟩))
          (.strictK (.deref ty1) [] [] env
            (.strictK (.fieldGet tid' f) [] [] env K)), σ, ch) :=
    stepFnIter_one (stepFn_var (henv := henv) (hlook := hp))
  have h3 : stepFnIter 1 σ (.retV (.addr (.base ⟨lw⟩))
      (.strictK (.deref ty1) [] [] env
        (.strictK (.fieldGet tid' f) [] [] env K))) ch
      = .ok (.retV (.struct tid' fs)
          (.strictK (.fieldGet tid' f) [] [] env K), σ, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.addr (.base ⟨lw⟩)])
      = [GoValue.addr (.base ⟨lw⟩)] from rfl]
    exact applyStrictOp_deref (c := ⟨dty2, .struct tid' fs⟩) hw
  have h4 : stepFnIter 1 σ (.retV (.struct tid' fs)
      (.strictK (.fieldGet tid' f) [] [] env K)) ch
      = .ok (.retV v K, σ, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.struct tid' fs])
      = [GoValue.struct tid' fs] from rfl]
    exact applyStrictOp_fieldGet hf
  exact stepFnIter_chain h1 (stepFnIter_chain h2
    (stepFnIter_chain h3 h4))

/-! ## 4. The twin field stores -/

section Stores

variable {σ : ExecState} {tw : Nat}
  {nodesV netV liveV byV pendV drvV hlV : GoValue} {lm : Nat}
  {c cm w sq : Int} {tr : GoString}

/-- The struct cell payload shorthand. -/
abbrev twCell (nodesV netV liveV : GoValue) (lm : Nat)
    (byV : GoValue) (c cm w : Int) (pendV drvV : GoValue) (sq : Int)
    (tr : GoString) (hlV : GoValue) : HeapCell :=
  ⟨some (.defined ⟨"main.twin"⟩),
    .struct ⟨"main.twin"⟩ (twinFs nodesV netV liveV lm byV c cm w
      pendV drvV sq tr hlV)⟩

/-- `t.claims = v'` through the `fieldAddr` chain: the whole-struct
re-normalization routed through `normalize_twinFs`. -/
theorem storeTarget_twin_claims
    (htypes : σ.types = twinTypes)
    (hTw : Heap.lookup σ.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV c cm w pendV drvV sq
          tr hlV))
    {c' : Int}
    (hc0 : -(2 ^ 63) ≤ c') (hc1 : c' < 2 ^ 63)
    (hm0 : -(2 ^ 63) ≤ cm) (hm1 : cm < 2 ^ 63)
    (hw0 : -(2 ^ 63) ≤ w) (hw1 : w < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63) :
    storeTarget σ (.chain (.addr (.base ⟨tw⟩)) []
        [.field ⟨"main.twin"⟩ "claims"]) (.int c' .int)
      = .ok { σ with heap := Heap.set σ.heap (.base ⟨tw⟩) (twCell nodesV netV liveV lm byV c' cm w pendV drvV sq tr hlV) } := by
  have hset : StructFields.set (twinFs nodesV netV liveV lm byV c cm w
      pendV drvV sq tr hlV) "claims" (.int c' .int)
      = .ok (twinFs nodesV netV liveV lm byV c' cm w pendV drvV sq
          tr hlV) := by
    with_unfolding_all rfl
  simp only [storeTarget, resolveChain, valueAsLoc, Bind.bind,
    Except.bind, pure, Except.pure, storeLoc, loadLoc, hTw]
  rw [show ((⟨"main.twin"⟩ : TypeId) != (⟨"main.twin"⟩ : TypeId))
    = false from rfl]
  simp only [Bool.false_and, Bool.false_eq_true, if_false, hset,
    Bind.bind, Except.bind, pure, Except.pure, hTw,
    normalize_twinFs htypes hc0 hc1 hm0 hm1 hw0 hw1 hq0 hq1]

/-- `t.violations = v'`. -/
theorem storeTarget_twin_violations
    (htypes : σ.types = twinTypes)
    (hTw : Heap.lookup σ.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV c cm w pendV drvV sq
          tr hlV))
    {w' : Int}
    (hc0 : -(2 ^ 63) ≤ c) (hc1 : c < 2 ^ 63)
    (hm0 : -(2 ^ 63) ≤ cm) (hm1 : cm < 2 ^ 63)
    (hw0 : -(2 ^ 63) ≤ w') (hw1 : w' < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63) :
    storeTarget σ (.chain (.addr (.base ⟨tw⟩)) []
        [.field ⟨"main.twin"⟩ "violations"]) (.int w' .int)
      = .ok { σ with heap := Heap.set σ.heap (.base ⟨tw⟩) (twCell nodesV netV liveV lm byV c cm w' pendV drvV sq tr hlV) } := by
  have hset : StructFields.set (twinFs nodesV netV liveV lm byV c cm w
      pendV drvV sq tr hlV) "violations" (.int w' .int)
      = .ok (twinFs nodesV netV liveV lm byV c cm w' pendV drvV sq
          tr hlV) := by
    with_unfolding_all rfl
  simp only [storeTarget, resolveChain, valueAsLoc, Bind.bind,
    Except.bind, pure, Except.pure, storeLoc, loadLoc, hTw]
  rw [show ((⟨"main.twin"⟩ : TypeId) != (⟨"main.twin"⟩ : TypeId))
    = false from rfl]
  simp only [Bool.false_and, Bool.false_eq_true, if_false, hset,
    Bind.bind, Except.bind, pure, Except.pure, hTw,
    normalize_twinFs htypes hc0 hc1 hm0 hm1 hw0 hw1 hq0 hq1]

/-- `t.trace = s'`. -/
theorem storeTarget_twin_trace
    (htypes : σ.types = twinTypes)
    (hTw : Heap.lookup σ.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV c cm w pendV drvV sq
          tr hlV))
    {tr' : GoString}
    (hc0 : -(2 ^ 63) ≤ c) (hc1 : c < 2 ^ 63)
    (hm0 : -(2 ^ 63) ≤ cm) (hm1 : cm < 2 ^ 63)
    (hw0 : -(2 ^ 63) ≤ w) (hw1 : w < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63) :
    storeTarget σ (.chain (.addr (.base ⟨tw⟩)) []
        [.field ⟨"main.twin"⟩ "trace"]) (.string tr')
      = .ok { σ with heap := Heap.set σ.heap (.base ⟨tw⟩) (twCell nodesV netV liveV lm byV c cm w pendV drvV sq tr' hlV) } := by
  have hset : StructFields.set (twinFs nodesV netV liveV lm byV c cm w
      pendV drvV sq tr hlV) "trace" (.string tr')
      = .ok (twinFs nodesV netV liveV lm byV c cm w pendV drvV sq
          tr' hlV) := by
    with_unfolding_all rfl
  simp only [storeTarget, resolveChain, valueAsLoc, Bind.bind,
    Except.bind, pure, Except.pure, storeLoc, loadLoc, hTw]
  rw [show ((⟨"main.twin"⟩ : TypeId) != (⟨"main.twin"⟩ : TypeId))
    = false from rfl]
  simp only [Bool.false_and, Bool.false_eq_true, if_false, hset,
    Bind.bind, Except.bind, pure, Except.pure, hTw,
    normalize_twinFs htypes hc0 hc1 hm0 hm1 hw0 hw1 hq0 hq1]

end Stores

/-! ## 5. The `viol` pin and span -/

/-- `main.twin.viol`'s body, spelled
(`artifacts/probe/harvestdump.out`): `violations++`,
`trace += " !" + s`. -/
def violBody : Stmt :=
  .block #[]
    #[.assign (.addr (.fieldAddr (.var "t") ⟨"main.twin"⟩ "violations"))
        (.add (.fieldGet (.deref (.var "t") (.defined ⟨"main.twin"⟩))
            ⟨"main.twin"⟩ "violations")
          (.intLit 1 .int)),
      .assign (.addr (.fieldAddr (.var "t") ⟨"main.twin"⟩ "trace"))
        (.add (.fieldGet (.deref (.var "t") (.defined ⟨"main.twin"⟩))
            ⟨"main.twin"⟩ "trace")
          (.add (.stringLit (gs [32, 33])) (.var "s")))]

/-- The whole `main.twin.viol` `Func`, spelled. -/
def violFunc : Func :=
  { id := ⟨"main.twin.viol"⟩,
    args := #[{ id := "t", typ := .pointer (.defined ⟨"main.twin"⟩) },
      { id := "s", typ := .string }],
    results := #[],
    body := violBody }

/-- **PIN**: the pinned lowering's `main.twin.viol` IS the spelled
function. -/
theorem viol_pinned :
    findFunctionIn? twinLowered.funcs ⟨"main.twin.viol"⟩
      = some violFunc := by
  kernel_rfl

/-- The `viol` frame environment. -/
def violEnv (na : Nat) : LocalEnv :=
  [[("s", .base ⟨na + 1⟩), ("t", .base ⟨na⟩)]]

/-- Raw `enterFrame` at `viol` (twin tables, symbolic everything —
pointer and string arguments normalize as identities). -/
theorem viol_enterFrame (h : Heap) (na : Nat) (tw : Nat)
    (sv : GoString) :
    enterFrame (twinSt h na) ⟨"main.twin.viol"⟩
        [.addr (.base ⟨tw⟩), .string sv]
      = .ok (violFunc, violEnv na, [],
          twinSt
            (Heap.set (Heap.set h (.base ⟨na⟩)
                ⟨some (.pointer (.defined ⟨"main.twin"⟩)),
                  .addr (.base ⟨tw⟩)⟩)
              (.base ⟨na + 1⟩) (sCell sv))
            (na + 2)) := by
  kernel_rfl

section ViolSpan

variable {nodesV netV liveV byV pendV drvV hlV : GoValue} {lm : Nat}
  {c cm w sq : Int} {tr : GoString}

/-- The `t`-parameter frame cell. -/
abbrev tParCell (tw : Nat) : HeapCell :=
  ⟨some (.pointer (.defined ⟨"main.twin"⟩)), .addr (.base ⟨tw⟩)⟩

/-- **THE `viol` CALL SPAN** (42 steps): from the delivered string
argument under the targetless call continuation to the caller's
resumption — `violations` incremented EXACTLY, `trace` appended (the
S1 span consumes it existentially), the two dead frame cells between
the frontiers, nothing else moved. -/
theorem viol_call_span {envC : LocalEnv} {Kc : Cont} {tw : Nat}
    (σ : ExecState) (ch : Choices) (sv : GoString)
    (hag : bfTB.Agrees σ)
    (hTw : Heap.lookup σ.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV c cm w pendV drvV sq
          tr hlV))
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (hc0 : -(2 ^ 63) ≤ c) (hc1 : c < 2 ^ 63)
    (hm0 : -(2 ^ 63) ≤ cm) (hm1 : cm < 2 ^ 63)
    (hw0 : -(2 ^ 63) ≤ w) (hw1 : w + 1 < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63) :
    stepFnIter 42 σ (.retV (.string sv)
        (.callArgsK ⟨"main.twin.viol"⟩ [] [.addr (.base ⟨tw⟩)] []
          envC Kc)) ch
      = .ok (.next Kc,
        twinSt (Heap.set (Heap.set (Heap.set σ.heap
              (.base ⟨σ.nextAddr⟩) (tParCell tw))
              (.base ⟨σ.nextAddr + 1⟩) (sCell sv))
            (.base ⟨tw⟩)
            (twCell nodesV netV liveV lm byV c cm (w + 1) pendV drvV
              sq (GoString.append tr (GoString.append (gs [32, 33])
                sv)) hlV))
          (σ.nextAddr + 2), ch) := by
  have htwna : tw < σ.nextAddr := by
    rcases Nat.lt_or_ge tw σ.nextAddr with h | h
    · exact h
    · rw [hfr tw h] at hTw
      cases hTw
  have hσ := twinSt_of_agrees hag
  -- V1: the frame entry
  have henter : enterFrame σ ⟨"main.twin.viol"⟩
      [.addr (.base ⟨tw⟩), .string sv]
      = .ok (violFunc, violEnv σ.nextAddr, [],
        twinSt (Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
            (tParCell tw)) (.base ⟨σ.nextAddr + 1⟩) (sCell sv))
          (σ.nextAddr + 2)) := by
    have h0 := viol_enterFrame σ.heap σ.nextAddr tw sv
    rw [← hσ] at h0
    exact h0
  -- the three states
  let h₁ : Heap := Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
    (tParCell tw)) (.base ⟨σ.nextAddr + 1⟩) (sCell sv)
  let σ₁ : ExecState := twinSt h₁ (σ.nextAddr + 2)
  let tr' : GoString := GoString.append tr
    (GoString.append (gs [32, 33]) sv)
  let σ₂ : ExecState := { σ₁ with heap := Heap.set σ₁.heap (.base ⟨tw⟩) (twCell nodesV netV liveV lm byV c cm (w + 1) pendV drvV sq tr hlV) }
  let σ₃ : ExecState := { σ₂ with heap := Heap.set σ₂.heap (.base ⟨tw⟩) (twCell nodesV netV liveV lm byV c cm (w + 1) pendV drvV sq tr' hlV) }
  -- cell reads at the entered state
  have hTw1 : Heap.lookup σ₁.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV c cm w pendV drvV sq
          tr hlV) := by
    show Heap.lookup h₁ (.base ⟨tw⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ tw),
      lookup_set_other (by omega : σ.nextAddr ≠ tw)]
    exact hTw
  have ht1 : Heap.lookup σ₁.heap (.base ⟨σ.nextAddr⟩)
      = some (tParCell tw) := by
    show Heap.lookup h₁ (.base ⟨σ.nextAddr⟩) = _
    rw [lookup_set_other (by omega : σ.nextAddr + 1 ≠ σ.nextAddr)]
    exact lookup_set_self
  have hs1 : Heap.lookup σ₁.heap (.base ⟨σ.nextAddr + 1⟩)
      = some (sCell sv) := lookup_set_self
  have hTw2 : Heap.lookup σ₂.heap (.base ⟨tw⟩)
      = some (twCell nodesV netV liveV lm byV c cm (w + 1) pendV drvV
          sq tr hlV) := lookup_set_self
  have ht2 : Heap.lookup σ₂.heap (.base ⟨σ.nextAddr⟩)
      = some (tParCell tw) := by
    show Heap.lookup (Heap.set σ₁.heap (.base ⟨tw⟩) _)
      (.base ⟨σ.nextAddr⟩) = _
    rw [lookup_set_other (by omega : tw ≠ σ.nextAddr)]
    exact ht1
  have hs2 : Heap.lookup σ₂.heap (.base ⟨σ.nextAddr + 1⟩)
      = some (sCell sv) := by
    show Heap.lookup (Heap.set σ₁.heap (.base ⟨tw⟩) _)
      (.base ⟨σ.nextAddr + 1⟩) = _
    rw [lookup_set_other (by omega : tw ≠ σ.nextAddr + 1)]
    exact hs1
  -- the frame continuation and scopes
  let FKv : Cont := .frame [] envC [] [] Kc false
  let env2v : LocalEnv := [] :: violEnv σ.nextAddr
  let vAssign1 : Stmt := .assign (.addr (.fieldAddr (.var "t")
    ⟨"main.twin"⟩ "violations"))
    (.add (.fieldGet (.deref (.var "t") (.defined ⟨"main.twin"⟩))
      ⟨"main.twin"⟩ "violations") (.intLit 1 .int))
  let vAssign2 : Stmt := .assign (.addr (.fieldAddr (.var "t")
    ⟨"main.twin"⟩ "trace"))
    (.add (.fieldGet (.deref (.var "t") (.defined ⟨"main.twin"⟩))
      ⟨"main.twin"⟩ "trace")
      (.add (.stringLit (gs [32, 33])) (.var "s")))
  -- V1
  have hV1 : stepFnIter 1 σ (.retV (.string sv)
      (.callArgsK ⟨"main.twin.viol"⟩ [] [.addr (.base ⟨tw⟩)] []
        envC Kc)) ch
      = .ok (.exec violBody (violEnv σ.nextAddr) FKv, σ₁, ch) :=
    stepFnIter_one (stepFn_call_enter
      (vals := [.addr (.base ⟨tw⟩)]) (v := .string sv)
      (h := henter))
  -- V2: block + pop
  have hV2 : stepFnIter 2 σ₁
      (.exec violBody (violEnv σ.nextAddr) FKv) ch
      = .ok (.exec vAssign1 env2v (.seq [vAssign2] env2v FKv),
        σ₁, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_block)
      (stepFnIter_one stepFn_seq_pop)
  -- V3-V10: the violations assign up to the store (13 steps)
  let K1v : Cont := .tgtOpK (.chain [.field ⟨"main.twin"⟩ "violations"])
    [] [] [] [] .vals
    [.add (.fieldGet (.deref (.var "t") (.defined ⟨"main.twin"⟩))
      ⟨"main.twin"⟩ "violations") (.intLit 1 .int)] []
    (.seqn #[]) env2v (.seq [vAssign2] env2v FKv)
  have hV3 : stepFnIter 1 σ₁
      (.exec vAssign1 env2v (.seq [vAssign2] env2v FKv)) ch
      = .ok (.evalE (.var "t") env2v K1v, σ₁, ch) := by
    with_unfolding_all rfl
  have hV4 : stepFnIter 1 σ₁ (.evalE (.var "t") env2v K1v) ch
      = .ok (.retV (.addr (.base ⟨tw⟩)) K1v, σ₁, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope (violEnv σ.nextAddr) "t").trans rfl)
      (hlook := ht1))
  have hV5 : stepFnIter 2 σ₁ (.retV (.addr (.base ⟨tw⟩)) K1v) ch
      = .ok (.evalE (.fieldGet (.deref (.var "t")
            (.defined ⟨"main.twin"⟩)) ⟨"main.twin"⟩ "violations") env2v
          (.strictK .add [] [.intLit 1 .int] env2v
            (.rhsK .vals
              [.chain (.addr (.base ⟨tw⟩)) []
                [.field ⟨"main.twin"⟩ "violations"]] [] []
              (.seqn #[]) env2v (.seq [vAssign2] env2v FKv))),
        σ₁, ch) := by
    with_unfolding_all rfl
  have hV7 : stepFnIter 5 σ₁
      (.evalE (.fieldGet (.deref (.var "t")
          (.defined ⟨"main.twin"⟩)) ⟨"main.twin"⟩ "violations") env2v
        (.strictK .add [] [.intLit 1 .int] env2v
          (.rhsK .vals
            [.chain (.addr (.base ⟨tw⟩)) []
              [.field ⟨"main.twin"⟩ "violations"]] [] []
            (.seqn #[]) env2v (.seq [vAssign2] env2v FKv)))) ch
      = .ok (.retV (.int w .int)
          (.strictK .add [] [.intLit 1 .int] env2v
            (.rhsK .vals
              [.chain (.addr (.base ⟨tw⟩)) []
                [.field ⟨"main.twin"⟩ "violations"]] [] []
              (.seqn #[]) env2v (.seq [vAssign2] env2v FKv))),
        σ₁, ch) :=
    read_field_seg
      (henv := (lookup_pushScope (violEnv σ.nextAddr) "t").trans rfl)
      (hp := ht1) (hw := hTw1) (hf := twinFs_violations)
  have hV8 : stepFnIter 2 σ₁ (.retV (.int w .int)
      (.strictK .add [] [.intLit 1 .int] env2v
        (.rhsK .vals
          [.chain (.addr (.base ⟨tw⟩)) []
            [.field ⟨"main.twin"⟩ "violations"]] [] []
          (.seqn #[]) env2v (.seq [vAssign2] env2v FKv)))) ch
      = .ok (.retV (.int 1 .int)
          (.strictK .add [.int w .int] [] env2v
            (.rhsK .vals
              [.chain (.addr (.base ⟨tw⟩)) []
                [.field ⟨"main.twin"⟩ "violations"]] [] []
              (.seqn #[]) env2v (.seq [vAssign2] env2v FKv))),
        σ₁, ch) := by
    with_unfolding_all rfl
  have hV9 : stepFnIter 1 σ₁ (.retV (.int 1 .int)
      (.strictK .add [.int w .int] [] env2v
        (.rhsK .vals
          [.chain (.addr (.base ⟨tw⟩)) []
            [.field ⟨"main.twin"⟩ "violations"]] [] []
          (.seqn #[]) env2v (.seq [vAssign2] env2v FKv)))) ch
      = .ok (.retV (.int (w + 1) .int)
          (.rhsK .vals
            [.chain (.addr (.base ⟨tw⟩)) []
              [.field ⟨"main.twin"⟩ "violations"]] [] []
            (.seqn #[]) env2v (.seq [vAssign2] env2v FKv)),
        σ₁, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.int 1 .int, GoValue.int w .int])
      = [GoValue.int w .int, GoValue.int 1 .int] from rfl]
    exact GoLean.SliceWalk.applyStrictOp_add_int (by omega) (by omega)
  have hV10 : stepFnIter 1 σ₁ (.retV (.int (w + 1) .int)
      (.rhsK .vals
        [.chain (.addr (.base ⟨tw⟩)) []
          [.field ⟨"main.twin"⟩ "violations"]] [] []
        (.seqn #[]) env2v (.seq [vAssign2] env2v FKv))) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨tw⟩)) []
            [.field ⟨"main.twin"⟩ "violations"]]
          [.int (w + 1) .int] (.seqn #[]) env2v
          (.seq [vAssign2] env2v FKv)), σ₁, ch) := by
    with_unfolding_all rfl
  -- V11: the violations store
  have hV11 : stepFnIter 1 σ₁ (.next (.storeK
      [.chain (.addr (.base ⟨tw⟩)) []
        [.field ⟨"main.twin"⟩ "violations"]]
      [.int (w + 1) .int] (.seqn #[]) env2v
      (.seq [vAssign2] env2v FKv))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) env2v
          (.seq [vAssign2] env2v FKv)), σ₂, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_twin_violations (σ := σ₁) rfl hTw1
        hc0 hc1 hm0 hm1 (by omega) hw1 hq0 hq1))
  -- V12+V13: drain + pop to the trace assign
  have hV13 : stepFnIter 3 σ₂ (.next (.storeK [] [] (.seqn #[]) env2v
      (.seq [vAssign2] env2v FKv))) ch
      = .ok (.exec vAssign2 env2v (.seq [] env2v FKv), σ₂, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
      (stepFnIter_splice_pop (ss := #[]) rfl)
  -- V14-V25: the trace assign (18 steps)
  let K2v : Cont := .tgtOpK (.chain [.field ⟨"main.twin"⟩ "trace"])
    [] [] [] [] .vals
    [.add (.fieldGet (.deref (.var "t") (.defined ⟨"main.twin"⟩))
      ⟨"main.twin"⟩ "trace")
      (.add (.stringLit (gs [32, 33])) (.var "s"))] []
    (.seqn #[]) env2v (.seq [] env2v FKv)
  have hV14 : stepFnIter 1 σ₂
      (.exec vAssign2 env2v (.seq [] env2v FKv)) ch
      = .ok (.evalE (.var "t") env2v K2v, σ₂, ch) := by
    with_unfolding_all rfl
  have hV15 : stepFnIter 1 σ₂ (.evalE (.var "t") env2v K2v) ch
      = .ok (.retV (.addr (.base ⟨tw⟩)) K2v, σ₂, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope (violEnv σ.nextAddr) "t").trans rfl)
      (hlook := ht2))
  let K3v : Cont := .rhsK .vals
    [.chain (.addr (.base ⟨tw⟩)) [] [.field ⟨"main.twin"⟩ "trace"]]
    [] [] (.seqn #[]) env2v (.seq [] env2v FKv)
  have hV16 : stepFnIter 2 σ₂ (.retV (.addr (.base ⟨tw⟩)) K2v) ch
      = .ok (.evalE (.fieldGet (.deref (.var "t")
            (.defined ⟨"main.twin"⟩)) ⟨"main.twin"⟩ "trace") env2v
          (.strictK .add []
            [.add (.stringLit (gs [32, 33])) (.var "s")] env2v K3v),
        σ₂, ch) := by
    with_unfolding_all rfl
  have hV18 : stepFnIter 5 σ₂
      (.evalE (.fieldGet (.deref (.var "t")
          (.defined ⟨"main.twin"⟩)) ⟨"main.twin"⟩ "trace") env2v
        (.strictK .add []
          [.add (.stringLit (gs [32, 33])) (.var "s")] env2v K3v)) ch
      = .ok (.retV (.string tr)
          (.strictK .add []
            [.add (.stringLit (gs [32, 33])) (.var "s")] env2v K3v),
        σ₂, ch) :=
    read_field_seg
      (henv := (lookup_pushScope (violEnv σ.nextAddr) "t").trans rfl)
      (hp := ht2) (hw := hTw2) (hf := twinFs_trace)
  have hV19 : stepFnIter 4 σ₂ (.retV (.string tr)
      (.strictK .add []
        [.add (.stringLit (gs [32, 33])) (.var "s")] env2v K3v)) ch
      = .ok (.evalE (.var "s") env2v
          (.strictK .add [.string (gs [32, 33])] [] env2v
            (.strictK .add [.string tr] [] env2v K3v)), σ₂, ch) := by
    with_unfolding_all rfl
  have hV22 : stepFnIter 1 σ₂ (.evalE (.var "s") env2v
      (.strictK .add [.string (gs [32, 33])] [] env2v
        (.strictK .add [.string tr] [] env2v K3v))) ch
      = .ok (.retV (.string sv)
          (.strictK .add [.string (gs [32, 33])] [] env2v
            (.strictK .add [.string tr] [] env2v K3v)), σ₂, ch) :=
    stepFnIter_one (stepFn_var
      (henv := (lookup_pushScope (violEnv σ.nextAddr) "s").trans rfl)
      (hlook := hs2))
  have hV23 : stepFnIter 1 σ₂ (.retV (.string sv)
      (.strictK .add [.string (gs [32, 33])] [] env2v
        (.strictK .add [.string tr] [] env2v K3v))) ch
      = .ok (.retV (.string (GoString.append (gs [32, 33]) sv))
          (.strictK .add [.string tr] [] env2v K3v), σ₂, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.string sv,
        GoValue.string (gs [32, 33])])
      = [GoValue.string (gs [32, 33]), GoValue.string sv] from rfl]
    exact applyStrictOp_add_string
  have hV24 : stepFnIter 1 σ₂
      (.retV (.string (GoString.append (gs [32, 33]) sv))
        (.strictK .add [.string tr] [] env2v K3v)) ch
      = .ok (.retV (.string tr') K3v, σ₂, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.string (GoString.append
        (gs [32, 33]) sv), GoValue.string tr])
      = [GoValue.string tr, GoValue.string (GoString.append
          (gs [32, 33]) sv)] from rfl]
    exact applyStrictOp_add_string
  have hV25 : stepFnIter 1 σ₂ (.retV (.string tr') K3v) ch
      = .ok (.next (.storeK
          [.chain (.addr (.base ⟨tw⟩)) []
            [.field ⟨"main.twin"⟩ "trace"]]
          [.string tr'] (.seqn #[]) env2v (.seq [] env2v FKv)),
        σ₂, ch) := by
    with_unfolding_all rfl
  -- V26: the trace store
  have hV26 : stepFnIter 1 σ₂ (.next (.storeK
      [.chain (.addr (.base ⟨tw⟩)) [] [.field ⟨"main.twin"⟩ "trace"]]
      [.string tr'] (.seqn #[]) env2v (.seq [] env2v FKv))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) env2v
          (.seq [] env2v FKv)), σ₃, ch) :=
    stepFnIter_one (stepFn_store_step
      (storeTarget_twin_trace (σ := σ₂) rfl hTw2
        hc0 hc1 hm0 hm1 (by omega) hw1 hq0 hq1))
  -- V27-V30: drain + block exit + frame exit (4 steps)
  have hV27 : stepFnIter 4 σ₃ (.next (.storeK [] [] (.seqn #[]) env2v
      (.seq [] env2v FKv))) ch
      = .ok (.next Kc, σ₃, ch) := by
    have s1 : stepFnIter 2 σ₃ (.next (.storeK [] [] (.seqn #[]) env2v
        (.seq [] env2v FKv))) ch
        = .ok (.next (.seq [] env2v FKv), σ₃, ch) :=
      stepFnIter_chain (stepFnIter_one stepFn_storeK_nil)
        (stepFnIter_one stepFn_seqn_splice)
    have s2 : stepFnIter 2 σ₃ (.next (.seq [] env2v FKv)) ch
        = .ok (.next Kc, σ₃, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain s1 s2
  -- collapse the double store at the twin cell
  have hfin : σ₃ = twinSt (Heap.set (Heap.set (Heap.set σ.heap
        (.base ⟨σ.nextAddr⟩) (tParCell tw))
        (.base ⟨σ.nextAddr + 1⟩) (sCell sv))
      (.base ⟨tw⟩)
      (twCell nodesV netV liveV lm byV c cm (w + 1) pendV drvV
        sq (GoString.append tr (GoString.append (gs [32, 33])
          sv)) hlV))
    (σ.nextAddr + 2) := by
    show twinSt (Heap.set (Heap.set h₁ (.base ⟨tw⟩)
        (twCell nodesV netV liveV lm byV c cm (w + 1) pendV drvV sq
          tr hlV)) (.base ⟨tw⟩)
        (twCell nodesV netV liveV lm byV c cm (w + 1) pendV drvV sq
          tr' hlV)) (σ.nextAddr + 2) = _
    rw [set_set]
  rw [← hfin]
  -- assemble
  exact stepFnIter_chain hV1 (stepFnIter_chain hV2 (stepFnIter_chain hV3 (stepFnIter_chain hV4 (stepFnIter_chain hV5 (stepFnIter_chain hV7 (stepFnIter_chain hV8 (stepFnIter_chain hV9 (stepFnIter_chain hV10 (stepFnIter_chain hV11 (stepFnIter_chain hV13 (stepFnIter_chain hV14 (stepFnIter_chain hV15 (stepFnIter_chain hV16 (stepFnIter_chain hV18 (stepFnIter_chain hV19 (stepFnIter_chain hV22 (stepFnIter_chain hV23 (stepFnIter_chain hV24 (stepFnIter_chain hV25 (stepFnIter_chain hV26 (hV27)))))))))))))))))))))

end ViolSpan

end GoLean.RaftSeam.SpanCells
