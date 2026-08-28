import GoLeanProofs.SliceWalk
import GoLeanProofs.Specs.TwinProgram
import GoLeanProofs.Sym.KernelRfl
import GoLean.GoCore.SyntaxEqb

/-!
# A4-U20 (C2b): THE DRIVER-LOOP SYMBOLIC-NET INSTANCES

The two |net|-dependent driver-glue spans the U18 census measured
(+141 steps per net entry, `3,578 → 7,250` across the run — the C1
verdict's A2 refinement) are the live-map REBUILD walk in
`runTwinChoice` and the `liveCount` walk inside `projection`. Both
carry the frontend's range-desugar shape (`SliceWalk`) with the SAME
guard (`t.live[idx]`) and differ only in the action (map insert vs
counter increment).

This module instantiates the `SliceWalk.sliceWalk_loop` schema at the
twin: the guard/action body facts, the loop invariants (`RebuildInv`,
`LiveCountInv`), and the two SYMBOLIC-NET span lemmas —
`rebuildLoop_span` and `liveCountLoop_span` — whose statements are
symbolic in the net length `n = bs.length` AND the liveness payload
`bs` (compositional mode I2: symbolic preconditions,
bounded-completion conclusions; never one literal chain per net
shape). (Triage hygiene 2026-08-27, P-2/K-4: the former
`DriverNetWitness.lean` discharge module was W0-killed — its
premise discharges are archived at `archive/fixed-trajectory-era`.
`RebuildInv`/`LiveCountInv` are NOT witness-less survivors: they are
the loop-invariant PARAMETERS of the kept span lemmas below
(`rebuildLoop_span` concludes/consumes them). Witness owed on first
consumption of the span lemmas by the tier-3 driver-loop work.)

The SHAPE-PIN theorems (`drvRebuild_pinned`, `lc_pinned`) prove the
module's statement vocabulary is EXACTLY the pinned lowering's — the
while statements proved here occur verbatim in `runTwinChoice` and
`main.twin.liveCount` (collected recursively, compared by the sound
structural `Stmt.eqbF`); a frontend re-lowering that reshapes either
loop turns the pins red (drift alarm), like the equation modules'
window links.

Census anchors (`artifacts/probe/c2bloopcensus2.out` (untracked scratch)): rebuild
iterations 63/67 (first/subsequent, guard true), 54/58 (guard false),
exit 29/33; liveCount 68/72 and 54/58. The composed kit bounds
reproduce these exactly: `43 + bB` = 67 at `bB = 24` (rebuild), 72 at
`bB = 29` (liveCount).

LINEAGE: instances of the SliceWalk schema (Floyd/Hoare loop
invariant); the map-insert lemma mirrors
`MapMem.mapAssignValue_toEntries` (fresh-key branch) at the
`int → bool` vocabulary.
-/

namespace GoLean.RaftSeam.DriverNet

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceWalk
open GoLean.Examples.RaftTwin (twinLowered)

set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

/-! ## 1. The twin's guarded bodies (statement vocabulary) -/

def tyTwin : Ty := .defined ⟨"main.twin"⟩
def tidTwin : TypeId := ⟨"main.twin"⟩

/-- The shared guard: `t.live[uV]`. -/
def guardExpr (uV : String) : Expr :=
  .indexGet (.fieldGet (.deref (.var "t") tyTwin) tidTwin "live") (.var uV)

/-- The rebuild body: `if t.live[j] { live[j] = true }`. -/
def rebuildBody : Stmt :=
  .block #[] #[.ifThenElse (guardExpr "j")
    (.block #[] #[.mapAssign (.var "live") (.var "j") (.boolLit true)
      tI .bool])
    (.seqn #[])]

/-- The liveCount body: `if t.live[i] { c = c + 1 }`. -/
def lcBody : Stmt :=
  .block #[] #[.ifThenElse (guardExpr "i")
    (.block #[] #[.assign (.var "c") (.add (.var "c") (.intLit 1 .int))])
    (.seqn #[])]

/-- The rebuild loop, in the schema's vocabulary. -/
def rebuildWhile : Stmt := rwhile "$rfirst" "$ridx" "$rlen" "j" rebuildBody

/-- The liveCount loop, in the schema's vocabulary. -/
def lcWhile : Stmt := rwhile "$rfirst" "$ridx" "$rlen" "i" lcBody

/-! ## 2. THE SHAPE PINS — the vocabulary IS the pinned lowering -/

/-- Collect every `while` statement (recursively), fuel-structural
(no `let rec` — the lifted auxiliary blocks KERNEL reduction, and the
shape pins are kernel-evaluated). -/
def collectWhilesF : Nat → Stmt → List Stmt
  | 0, _ => []
  | fuel + 1, s =>
      match s with
      | .while c b => .while c b :: collectWhilesF fuel b
      | .block _ ss => ss.toList.flatMap (collectWhilesF fuel)
      | .seqn ss => ss.toList.flatMap (collectWhilesF fuel)
      | .ifThenElse _ t e =>
          collectWhilesF fuel t ++ collectWhilesF fuel e
      | .labeled _ b => collectWhilesF fuel b
      | .breakable b => collectWhilesF fuel b
      | .mapRange _ _ _ _ _ b => collectWhilesF fuel b
      | _ => []

/-- The whiles of a pinned function's body. -/
def funcWhiles (name : String) : List Stmt :=
  match findFunctionIn? twinLowered.funcs ⟨name⟩ with
  | some f => collectWhilesF 64 f.body
  | none => []

/-- **SHAPE PIN (rebuild)**: the schema spelling `rebuildWhile` occurs
verbatim among `runTwinChoice`'s while statements. -/
theorem drvRebuild_pinned :
    (funcWhiles "runTwinChoice").any
      (fun s => Stmt.eqbF 4096 s rebuildWhile) = true := by
  kernel_rfl

/-- **SHAPE PIN (liveCount)**: `lcWhile` occurs verbatim in
`main.twin.liveCount`. -/
theorem lc_pinned :
    (funcWhiles "main.twin.liveCount").any
      (fun s => Stmt.eqbF 4096 s lcWhile) = true := by
  kernel_rfl

/-- The Prop form (via `Stmt.eqbF_sound`): the real lowered driver
CONTAINS the proved loop statement. -/
theorem drvRebuild_pinned_prop :
    ∃ s ∈ funcWhiles "runTwinChoice", s = rebuildWhile := by
  obtain ⟨s, hmem, hb⟩ := List.any_eq_true.mp drvRebuild_pinned
  exact ⟨s, hmem, Stmt.eqbF_sound _ _ _ hb⟩

theorem lc_pinned_prop :
    ∃ s ∈ funcWhiles "main.twin.liveCount", s = lcWhile := by
  obtain ⟨s, hmem, hb⟩ := List.any_eq_true.mp lc_pinned
  exact ⟨s, hmem, Stmt.eqbF_sound _ _ _ hb⟩

/-! ## 3. The live-map model -/

/-- The live index list after `i` iterations: indices `j < i` with
`bs[j] = true`, in walk order. -/
def liveIdx (bs : List Bool) : Nat → List Nat
  | 0 => []
  | i + 1 => liveIdx bs i ++ (if bs.getD i false then [i] else [])

@[simp] theorem liveIdx_succ {bs : List Bool} {i : Nat} :
    liveIdx bs (i + 1)
      = liveIdx bs i ++ (if bs.getD i false then [i] else []) := rfl

/-- Every member of `liveIdx bs i` is `< i`. -/
theorem liveIdx_lt {bs : List Bool} : ∀ {i j : Nat},
    j ∈ liveIdx bs i → j < i := by
  intro i
  induction i with
  | zero => intro j h; cases h
  | succ m ih =>
      intro j h
      unfold liveIdx at h
      rcases List.mem_append.mp h with h1 | h2
      · exact Nat.lt_succ_of_lt (ih h1)
      · by_cases hb : bs.getD m false
        · rw [if_pos hb] at h2
          cases h2 with
          | head => exact Nat.lt_succ_self m
          | tail _ hh => cases hh
        · rw [if_neg hb] at h2; cases h2

/-- The machine entry array for a `map[int]bool` holding exactly
`js ↦ true`. -/
def bEntries (js : List Nat) : Array (GoValue × GoValue) :=
  (js.map (fun (j : Nat) => ((GoValue.int (j : Int) IntKind.int),
    (GoValue.bool true)))).toArray

/-- `true`-count below `i`. -/
def countTrue (bs : List Bool) : Nat → Nat
  | 0 => 0
  | i + 1 => countTrue bs i + (if bs.getD i false then 1 else 0)

@[simp] theorem countTrue_succ {bs : List Bool} {i : Nat} :
    countTrue bs (i + 1)
      = countTrue bs i + (if bs.getD i false then 1 else 0) := rfl

/-! ## 4. Machine facts the bodies consume -/

/-- `valueEq` at signed int is the `Int` beq (state-free). -/
theorem valueEq_int (σ : ExecState) (l r : Int) :
    valueEq σ tI (.int l .int) (.int r .int) = .ok (l == r) := by
  simp [valueEq, valueEqFuel, typeResolutionFuel]

/-- The key-scan loop over `bEntries js` at a key off every entry
(the `MapMem.scan_generic` pattern at this module's model). -/
private theorem scan_fresh {i : Nat}
    (f : GoValue × GoValue → Option (Option Nat) × Nat →
      Except GoError (ForInStep (Option (Option Nat) × Nat)))
    (hf : ∀ (j : Nat) (v : GoValue) (r : Option (Option Nat) × Nat),
      j ≠ i →
      f (.int (j : Int) .int, v) r = .ok (.yield ⟨none, r.snd + 1⟩)) :
    ∀ (js : List Nat) (c : Nat), (∀ j ∈ js, j ≠ i) →
    (forIn (m := Except GoError) (bEntries js)
      (⟨none, c⟩ : Option (Option Nat) × Nat) f)
      = pure ⟨none, c + js.length⟩ := by
  intro js
  induction js with
  | nil =>
      intro c _
      simp [bEntries, List.forIn_toArray]
  | cons j rest ih =>
      intro c hne
      have hji : j ≠ i := hne j (by simp)
      have hrest := ih (c + 1)
        (fun x hx => hne x (List.mem_cons_of_mem _ hx))
      simp only [bEntries, List.map_cons, List.forIn_toArray]
        at hrest ⊢
      rw [List.forIn_cons, hf j _ _ hji]
      simp only [Bind.bind, Except.bind]
      rw [hrest]
      simp only [List.length_cons]
      rw [show c + 1 + rest.length = c + (rest.length + 1) from by omega]

/-- The whole `mapEntryIndex?` at a fresh int key: no hit. -/
theorem mapEntryIndex?_bEntries_fresh (σ : ExecState) {js : List Nat}
    {i : Nat} (hne : ∀ j ∈ js, j ≠ i) :
    mapEntryIndex? σ tI (bEntries js) (.int (i : Int) .int) true
      = .ok none := by
  unfold mapEntryIndex?
  rw [show checkKeyHashable σ (.int (i : Int) .int) true
      (!(bEntries js).isEmpty) = .ok () from by
    simp [checkKeyHashable, valueHashability]]
  simp only [letFun, Bind.bind, Except.bind]
  rw [scan_fresh _ ?hf js 0 hne]
  case hf =>
    intro j v r hji
    have hjb : (((j : Nat) : Int) == ((i : Nat) : Int)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      omega
    simp [valueEq_int, hjb, Bind.bind, Except.bind]
  rfl

/-- The map-insert apply at a fresh int key (mirrors
`mapAssignValue_toEntries`'s push branch at `int → bool`). -/
theorem mapAssignValue_bEntries_fresh {σ : ExecState} {a : Addr}
    {js : List Nat} {i : Nat}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨none, .mapData (bEntries js)⟩)
    (hne : ∀ j ∈ js, j ≠ i) (hi63 : (i : Int) < 2 ^ 63) :
    mapAssignValue σ tI .bool
      (.map ⟨some (.base a)⟩) (.int (i : Int) .int) (.bool true)
      = .ok { σ with heap := (Heap.set σ.heap (.base a)
          ⟨none, .mapData (bEntries (js ++ [i]))⟩) } := by
  simp only [mapAssignValue, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show normalizeValueForTy σ tI (.int (i : Int) .int)
      = .ok (.int (i : Int) .int) from
    normalize_int_signed (by omega) hi63]
  rw [show normalizeValueForTy σ .bool (.bool true) = .ok (.bool true) from
    normalize_bool]
  simp only [mapEntries, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure, loadLoc, hlook]
  rw [mapEntryIndex?_bEntries_fresh σ hne]
  show storeLoc σ (.base a)
    (.mapData ((bEntries js).push (.int (i : Int) .int, .bool true))) = _
  rw [show (bEntries js).push
      ((.int (i : Int) .int : GoValue), (.bool true : GoValue))
      = bEntries (js ++ [i]) from by
    simp [bEntries, List.map_append]]
  simp only [storeLoc, hlook, coerceStoredValue, Bind.bind, Except.bind,
    pure, Except.pure]

/-- `deref` at a base-address value: the cell load. -/
theorem applyStrictOp_deref {σ : ExecState} {ty : Ty} {a : Addr}
    {c : HeapCell}
    (hlook : Heap.lookup σ.heap (.base a) = some c) :
    applyStrictOp σ (.deref ty) [.addr (.base a)] = .ok (c.value, σ) := by
  simp only [applyStrictOp, valueAsLoc, loadLoc, hlook, Bind.bind,
    Except.bind, pure, Except.pure]

/-- `fieldGet` at a matching mint tag. -/
theorem applyStrictOp_fieldGet {σ : ExecState} {tid : TypeId}
    {fname : String} {fs : Array (String × GoValue)} {v : GoValue}
    (hfield : StructFields.lookup fs fname = some v) :
    applyStrictOp σ (.fieldGet tid fname) [.struct tid fs]
      = .ok (v, σ) := by
  simp only [applyStrictOp]
  rw [show (tid != tid) = false from by simp]
  simp only [Bool.false_and, if_neg (by simp : ¬(false = true)), hfield,
    pure, Except.pure, Bind.bind, Except.bind]

/-! ## 5. The guarded-body segments

The guarded body shape both instances share:
`block [] [if t.live[uV] { thn } else {}]`. -/

/-- The guarded body's statement former. -/
def guardedBody (uV : String) (thn : Stmt) : Stmt :=
  .block #[] #[.ifThenElse (guardExpr uV) thn (.seqn #[])]

section GuardSeg

variable {rF rI rL uV : String} {thn : Stmt} {envW : LocalEnv} {k : Cont}
  {σ : ExecState} {ch : Choices} {na : Nat}

/-- The guard walk: 13 steps from the body configuration to the
branch dispatch, state untouched. `b` is the read liveness bit. -/
theorem guard_seg
    (hUT : uV ≠ "t")
    (henvT : LocalEnv.lookup envW "t" = some (.base ⟨lt⟩))
    {tw lb : Nat} {dtyT dtyTw dtyB : Option Ty}
    {fs : Array (String × GoValue)} {n cap : Nat} {vs : Array GoValue}
    {i : Nat} {b : Bool}
    (hT : Heap.lookup σ.heap (.base ⟨lt⟩)
      = some ⟨dtyT, .addr (.base ⟨tw⟩)⟩)
    (hTw : Heap.lookup σ.heap (.base ⟨tw⟩)
      = some ⟨dtyTw, .struct tidTwin fs⟩)
    (hLive : StructFields.lookup fs "live"
      = some (.slice ⟨some (.base ⟨lb⟩), 0, n, cap⟩))
    (hB : Heap.lookup σ.heap (.base ⟨lb⟩) = some ⟨dtyB, .array vs⟩)
    (hcap : n ≤ cap) (hin : i < n)
    (hvs : vs[i]? = some (.bool b))
    (hU : Heap.lookup σ.heap (.base ⟨na⟩) = some (idxCell i))
    (hi63 : (i : Int) < 2 ^ 63) :
    stepFnIter 13 σ
      (bodyCfg rF rI rL uV (guardedBody uV thn) envW k na) ch
      = .ok (.exec (if b then thn else (.seqn #[]))
          ([] :: envU envW uV na)
          (.seq [] ([] :: envU envW uV na)
            (.seq [] (envU envW uV na)
              (wloopK rF rI rL uV (guardedBody uV thn) envW k))),
        σ, ch) := by
  -- 3 pure steps: block push/pop + if entry
  have hA : stepFnIter 3 σ
      (bodyCfg rF rI rL uV (guardedBody uV thn) envW k na) ch
      = .ok (.evalE (guardExpr uV) ([] :: envU envW uV na)
          (.ifK thn (.seqn #[]) ([] :: envU envW uV na)
            (.seq [] ([] :: envU envW uV na)
              (.seq [] (envU envW uV na)
                (wloopK rF rI rL uV (guardedBody uV thn) envW k)))),
        σ, ch) := by
    with_unfolding_all rfl
  -- 3 pure dispatch steps down to the `t` read
  have hB1 : stepFnIter 3 σ
      (.evalE (guardExpr uV) ([] :: envU envW uV na)
        (.ifK thn (.seqn #[]) ([] :: envU envW uV na)
          (.seq [] ([] :: envU envW uV na)
            (.seq [] (envU envW uV na)
              (wloopK rF rI rL uV (guardedBody uV thn) envW k))))) ch
      = .ok (.evalE (.var "t") ([] :: envU envW uV na)
          (.strictK (.deref tyTwin) [] [] ([] :: envU envW uV na)
            (.strictK (.fieldGet tidTwin "live") [] []
              ([] :: envU envW uV na)
              (.strictK .indexGet [] [.var uV] ([] :: envU envW uV na)
                (.ifK thn (.seqn #[]) ([] :: envU envW uV na)
                  (.seq [] ([] :: envU envW uV na)
                    (.seq [] (envU envW uV na)
                      (wloopK rF rI rL uV (guardedBody uV thn)
                        envW k))))))),
        σ, ch) := by
    with_unfolding_all rfl
  have henvT3 : LocalEnv.lookup ([] :: envU envW uV na) "t"
      = some (.base ⟨lt⟩) := by
    rw [lookup_pushScope, lookup_envU_ne hUT]
    exact henvT
  have h7 := stepFnIter_one (stepFn_var (σ := σ) (henv := henvT3)
    (hlook := hT)
    (k := (.strictK (.deref tyTwin) [] [] ([] :: envU envW uV na)
      (.strictK (.fieldGet tidTwin "live") [] [] ([] :: envU envW uV na)
        (.strictK .indexGet [] [.var uV] ([] :: envU envW uV na)
          (.ifK thn (.seqn #[]) ([] :: envU envW uV na)
            (.seq [] ([] :: envU envW uV na)
              (.seq [] (envU envW uV na)
                (wloopK rF rI rL uV (guardedBody uV thn) envW k))))))))
    (ch := ch))
  have h8 := stepFnIter_one (stepFn_strict_apply (σ := σ)
    (op := .deref tyTwin) (done := []) (v := .addr (.base ⟨tw⟩))
    (env := [] :: envU envW uV na)
    (k := (.strictK (.fieldGet tidTwin "live") [] []
      ([] :: envU envW uV na)
      (.strictK .indexGet [] [.var uV] ([] :: envU envW uV na)
        (.ifK thn (.seqn #[]) ([] :: envU envW uV na)
          (.seq [] ([] :: envU envW uV na)
            (.seq [] (envU envW uV na)
              (wloopK rF rI rL uV (guardedBody uV thn) envW k)))))))
    (ch := ch) (h := applyStrictOp_deref hTw))
  have h9 := stepFnIter_one (stepFn_strict_apply (σ := σ)
    (op := .fieldGet tidTwin "live") (done := [])
    (v := .struct tidTwin fs) (env := [] :: envU envW uV na)
    (k := (.strictK .indexGet [] [.var uV] ([] :: envU envW uV na)
      (.ifK thn (.seqn #[]) ([] :: envU envW uV na)
        (.seq [] ([] :: envU envW uV na)
          (.seq [] (envU envW uV na)
            (wloopK rF rI rL uV (guardedBody uV thn) envW k))))))
    (ch := ch) (h := applyStrictOp_fieldGet hLive))
  -- slice arrives at the indexGet collector; 1 pure step to the uV read
  have hC : stepFnIter 1 σ
      (.retV (.slice ⟨some (.base ⟨lb⟩), 0, n, cap⟩)
        (.strictK .indexGet [] [.var uV] ([] :: envU envW uV na)
          (.ifK thn (.seqn #[]) ([] :: envU envW uV na)
            (.seq [] ([] :: envU envW uV na)
              (.seq [] (envU envW uV na)
                (wloopK rF rI rL uV (guardedBody uV thn) envW k)))))) ch
      = .ok (.evalE (.var uV) ([] :: envU envW uV na)
          (.strictK .indexGet [.slice ⟨some (.base ⟨lb⟩), 0, n, cap⟩] []
            ([] :: envU envW uV na)
            (.ifK thn (.seqn #[]) ([] :: envU envW uV na)
              (.seq [] ([] :: envU envW uV na)
                (.seq [] (envU envW uV na)
                  (wloopK rF rI rL uV (guardedBody uV thn) envW k))))),
        σ, ch) := by
    with_unfolding_all rfl
  have henvU3 : LocalEnv.lookup ([] :: envU envW uV na) uV
      = some (.base ⟨na⟩) := by
    rw [lookup_pushScope]; exact lookup_envU_self
  have h11 := stepFnIter_one (stepFn_var (σ := σ) (henv := henvU3)
    (hlook := hU)
    (k := (.strictK .indexGet [.slice ⟨some (.base ⟨lb⟩), 0, n, cap⟩] []
      ([] :: envU envW uV na)
      (.ifK thn (.seqn #[]) ([] :: envU envW uV na)
        (.seq [] ([] :: envU envW uV na)
          (.seq [] (envU envW uV na)
            (wloopK rF rI rL uV (guardedBody uV thn) envW k))))))
    (ch := ch))
  have hidxget : applyStrictOp σ .indexGet
      [.slice ⟨some (.base ⟨lb⟩), 0, n, cap⟩, .int (i : Int) .int]
      = .ok (.bool b, σ) := by
    have := GoLean.SliceMem.applyStrictOp_indexGet_slice (σ := σ)
      (a := ⟨lb⟩) (dty := dtyB) (off := 0) (len := n) (cap := cap)
      (i := i) (ik := .int) (vs := vs) (w := .bool b)
      hB hcap hin (by simpa using hvs)
    simpa using this
  have h12 := stepFnIter_one (stepFn_strict_apply (σ := σ)
    (op := .indexGet)
    (done := [.slice ⟨some (.base ⟨lb⟩), 0, n, cap⟩])
    (v := .int (i : Int) .int) (env := [] :: envU envW uV na)
    (k := (.ifK thn (.seqn #[]) ([] :: envU envW uV na)
      (.seq [] ([] :: envU envW uV na)
        (.seq [] (envU envW uV na)
          (wloopK rF rI rL uV (guardedBody uV thn) envW k)))))
    (ch := ch) (h := by simpa using hidxget))
  have h13 : stepFnIter 1 σ
      (.retV (.bool b)
        (.ifK thn (.seqn #[]) ([] :: envU envW uV na)
          (.seq [] ([] :: envU envW uV na)
            (.seq [] (envU envW uV na)
              (wloopK rF rI rL uV (guardedBody uV thn) envW k))))) ch
      = .ok (.exec (if b then thn else (.seqn #[]))
          ([] :: envU envW uV na)
          (.seq [] ([] :: envU envW uV na)
            (.seq [] (envU envW uV na)
              (wloopK rF rI rL uV (guardedBody uV thn) envW k))),
        σ, ch) := by
    cases b <;> with_unfolding_all rfl
  exact stepFnIter_chain hA (stepFnIter_chain hB1 (stepFnIter_chain h7
    (stepFnIter_chain h8 (stepFnIter_chain h9 (stepFnIter_chain hC
      (stepFnIter_chain h11 (stepFnIter_chain h12 h13)))))))

end GuardSeg

/-! ## 6. The action segments -/

section ActSeg

variable {rF rI rL uV : String} {thn : Stmt} {envW : LocalEnv} {k : Cont}
  {σ : ExecState} {ch : Choices} {na : Nat}

/-- The skip action (guard false): 2 steps to the body-done
configuration, state untouched. -/
theorem act_skip {body : Stmt} :
    stepFnIter 2 σ (.exec (.seqn #[]) ([] :: envU envW uV na)
      (.seq [] ([] :: envU envW uV na)
        (.seq [] (envU envW uV na)
          (wloopK rF rI rL uV body envW k)))) ch
      = .ok (bodyDoneCfg rF rI rL uV body envW k na, σ, ch) := by
  have h1 := stepFnIter_one (stepFn_seqn_splice (σ := σ) (ss := #[])
    (env := [] :: envU envW uV na) (rest := [])
    (k := (.seq [] (envU envW uV na) (wloopK rF rI rL uV body envW k)))
    (ch := ch))
  rw [show (Array.toList (#[] : Array Stmt) ++ ([] : List Stmt)) = []
    from rfl] at h1
  refine stepFnIter_chain h1 (stepFnIter_one ?_)
  with_unfolding_all rfl

/-- The map-insert action (rebuild, guard true): 11 steps writing
`bMap ↦ entries ++ [i]`, conditioned on the map-local and data-cell
lookups and key freshness. -/
theorem act_rebuild {body : Stmt} {lm bMap : Nat} {dtyM : Option Ty}
    {js : List Nat} {i : Nat}
    (henvM : LocalEnv.lookup envW "live" = some (.base ⟨lm⟩))
    (hM : Heap.lookup σ.heap (.base ⟨lm⟩)
      = some ⟨dtyM, .map ⟨some (.base ⟨bMap⟩)⟩⟩)
    (hD : Heap.lookup σ.heap (.base ⟨bMap⟩)
      = some ⟨none, .mapData (bEntries js)⟩)
    (hU : Heap.lookup σ.heap (.base ⟨na⟩) = some (idxCell i))
    (hne : ∀ j ∈ js, j ≠ i) (hi63 : (i : Int) < 2 ^ 63) :
    stepFnIter 11 σ
      (.exec (.block #[] #[.mapAssign (.var "live") (.var "j")
          (.boolLit true) tI .bool])
        ([] :: envU envW "j" na)
        (.seq [] ([] :: envU envW "j" na)
          (.seq [] (envU envW "j" na)
            (wloopK rF rI rL "j" body envW k)))) ch
      = .ok (bodyDoneCfg rF rI rL "j" body envW k na,
        { σ with heap := (Heap.set σ.heap (.base ⟨bMap⟩)
            ⟨none, .mapData (bEntries (js ++ [i]))⟩) }, ch) := by
  -- 3 pure steps: block push, pop, mapAssign plan entry
  have hA : stepFnIter 3 σ
      (.exec (.block #[] #[.mapAssign (.var "live") (.var "j")
          (.boolLit true) tI .bool])
        ([] :: envU envW "j" na)
        (.seq [] ([] :: envU envW "j" na)
          (.seq [] (envU envW "j" na)
            (wloopK rF rI rL "j" body envW k)))) ch
      = .ok (.evalE (.var "live") ([] :: [] :: envU envW "j" na)
          (.stmtOpK (.mapAssign tI .bool) 0 []
            [.var "j", .boolLit true] ([] :: [] :: envU envW "j" na)
            (.seq [] ([] :: [] :: envU envW "j" na)
              (.seq [] ([] :: envU envW "j" na)
                (.seq [] (envU envW "j" na)
                  (wloopK rF rI rL "j" body envW k))))),
        σ, ch) := by
    with_unfolding_all rfl
  have henvM4 : LocalEnv.lookup ([] :: [] :: envU envW "j" na) "live"
      = some (.base ⟨lm⟩) := by
    rw [lookup_pushScope, lookup_pushScope,
      lookup_envU_ne (by decide : "j" ≠ "live")]
    exact henvM
  have h4 := stepFnIter_one (stepFn_var (σ := σ) (henv := henvM4)
    (hlook := hM)
    (k := (.stmtOpK (.mapAssign tI .bool) 0 []
      [.var "j", .boolLit true] ([] :: [] :: envU envW "j" na)
      (.seq [] ([] :: [] :: envU envW "j" na)
        (.seq [] ([] :: envU envW "j" na)
          (.seq [] (envU envW "j" na)
            (wloopK rF rI rL "j" body envW k))))))
    (ch := ch))
  have hB : stepFnIter 1 σ
      (.retV (.map ⟨some (.base ⟨bMap⟩)⟩)
        (.stmtOpK (.mapAssign tI .bool) 0 []
          [.var "j", .boolLit true] ([] :: [] :: envU envW "j" na)
          (.seq [] ([] :: [] :: envU envW "j" na)
            (.seq [] ([] :: envU envW "j" na)
              (.seq [] (envU envW "j" na)
                (wloopK rF rI rL "j" body envW k)))))) ch
      = .ok (.evalE (.var "j") ([] :: [] :: envU envW "j" na)
          (.stmtOpK (.mapAssign tI .bool) 0
            [.map ⟨some (.base ⟨bMap⟩)⟩] [.boolLit true]
            ([] :: [] :: envU envW "j" na)
            (.seq [] ([] :: [] :: envU envW "j" na)
              (.seq [] ([] :: envU envW "j" na)
                (.seq [] (envU envW "j" na)
                  (wloopK rF rI rL "j" body envW k))))),
        σ, ch) := by
    with_unfolding_all rfl
  have henvU4 : LocalEnv.lookup ([] :: [] :: envU envW "j" na) "j"
      = some (.base ⟨na⟩) := by
    rw [lookup_pushScope, lookup_pushScope]
    exact lookup_envU_self
  have h6 := stepFnIter_one (stepFn_var (σ := σ) (henv := henvU4)
    (hlook := hU)
    (k := (.stmtOpK (.mapAssign tI .bool) 0
      [.map ⟨some (.base ⟨bMap⟩)⟩] [.boolLit true]
      ([] :: [] :: envU envW "j" na)
      (.seq [] ([] :: [] :: envU envW "j" na)
        (.seq [] ([] :: envU envW "j" na)
          (.seq [] (envU envW "j" na)
            (wloopK rF rI rL "j" body envW k))))))
    (ch := ch))
  have hC : stepFnIter 2 σ
      (.retV (.int (i : Int) .int)
        (.stmtOpK (.mapAssign tI .bool) 0
          [.map ⟨some (.base ⟨bMap⟩)⟩] [.boolLit true]
          ([] :: [] :: envU envW "j" na)
          (.seq [] ([] :: [] :: envU envW "j" na)
            (.seq [] ([] :: envU envW "j" na)
              (.seq [] (envU envW "j" na)
                (wloopK rF rI rL "j" body envW k)))))) ch
      = .ok (.retV (.bool true)
          (.stmtOpK (.mapAssign tI .bool) 0
            [.int (i : Int) .int, .map ⟨some (.base ⟨bMap⟩)⟩] []
            ([] :: [] :: envU envW "j" na)
            (.seq [] ([] :: [] :: envU envW "j" na)
              (.seq [] ([] :: envU envW "j" na)
                (.seq [] (envU envW "j" na)
                  (wloopK rF rI rL "j" body envW k))))),
        σ, ch) := by
    with_unfolding_all rfl
  have happly : applyStmtOp σ ch (.mapAssign tI .bool) 0
      ((GoValue.bool true
        :: [.int (i : Int) .int, .map ⟨some (.base ⟨bMap⟩)⟩]).reverse)
      = .ok ({ σ with heap := (Heap.set σ.heap (.base ⟨bMap⟩)
          ⟨none, .mapData (bEntries (js ++ [i]))⟩) }, ch) := by
    show applyStmtOp σ ch (.mapAssign tI .bool) 0
      [.map ⟨some (.base ⟨bMap⟩)⟩, .int (i : Int) .int, .bool true] = _
    simp only [applyStmtOp, applyStmtOpCore,
      mapAssignValue_bEntries_fresh hD hne hi63, Bind.bind, Except.bind,
      pure, Except.pure]
  have h9 := stepFnIter_one (stepFn_stmtOp_apply (σ := σ)
    (op := .mapAssign tI .bool) (nt := 0)
    (done := [.int (i : Int) .int, .map ⟨some (.base ⟨bMap⟩)⟩])
    (v := .bool true) (env := [] :: [] :: envU envW "j" na)
    (k := (.seq [] ([] :: [] :: envU envW "j" na)
      (.seq [] ([] :: envU envW "j" na)
        (.seq [] (envU envW "j" na)
          (wloopK rF rI rL "j" body envW k)))))
    (ch := ch) (ch' := ch) (h := happly))
  have hD2 : stepFnIter 2
      { σ with heap := (Heap.set σ.heap (.base ⟨bMap⟩)
          ⟨none, .mapData (bEntries (js ++ [i]))⟩) }
      (.next (.seq [] ([] :: [] :: envU envW "j" na)
        (.seq [] ([] :: envU envW "j" na)
          (.seq [] (envU envW "j" na)
            (wloopK rF rI rL "j" body envW k))))) ch
      = .ok (bodyDoneCfg rF rI rL "j" body envW k na,
        { σ with heap := (Heap.set σ.heap (.base ⟨bMap⟩)
            ⟨none, .mapData (bEntries (js ++ [i]))⟩) }, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain hA (stepFnIter_chain h4 (stepFnIter_chain hB
    (stepFnIter_chain h6 (stepFnIter_chain hC (stepFnIter_chain h9
      hD2)))))

/-- The counter-increment action (liveCount, guard true): 16 steps
writing `c := cv + 1`. -/
theorem act_inc {body : Stmt} {lc : Nat} {cv : Int}
    (henvC : LocalEnv.lookup envW "c" = some (.base ⟨lc⟩))
    (hC : Heap.lookup σ.heap (.base ⟨lc⟩) = some (idxCell cv))
    (h0 : 0 ≤ cv) (h1 : cv + 1 < 2 ^ 63) :
    stepFnIter 16 σ
      (.exec (.block #[] #[.assign (.var "c")
          (.add (.var "c") (.intLit 1 .int))])
        ([] :: envU envW "i" na)
        (.seq [] ([] :: envU envW "i" na)
          (.seq [] (envU envW "i" na)
            (wloopK rF rI rL "i" body envW k)))) ch
      = .ok (bodyDoneCfg rF rI rL "i" body envW k na,
        { σ with heap := Heap.set σ.heap (.base ⟨lc⟩) (idxCell (cv + 1)) },
        ch) := by
  have henvC4 : LocalEnv.lookup ([] :: [] :: envU envW "i" na) "c"
      = some (.base ⟨lc⟩) := by
    rw [lookup_pushScope, lookup_pushScope,
      lookup_envU_ne (by decide : "i" ≠ "c")]
    exact henvC
  -- 3 pure steps: block push, pop, assign plan entry
  have hA : stepFnIter 3 σ
      (.exec (.block #[] #[.assign (.var "c")
          (.add (.var "c") (.intLit 1 .int))])
        ([] :: envU envW "i" na)
        (.seq [] ([] :: envU envW "i" na)
          (.seq [] (envU envW "i" na)
            (wloopK rF rI rL "i" body envW k)))) ch
      = .ok (.evalE (.ref "c") ([] :: [] :: envU envW "i" na)
          (.tgtOpK (.chain []) [] [] [] [] .vals
            [.add (.var "c") (.intLit 1 .int)] [] (.seqn #[])
            ([] :: [] :: envU envW "i" na)
            (.seq [] ([] :: [] :: envU envW "i" na)
              (.seq [] ([] :: envU envW "i" na)
                (.seq [] (envU envW "i" na)
                  (wloopK rF rI rL "i" body envW k))))),
        σ, ch) := by
    with_unfolding_all rfl
  have h4 := stepFnIter_one (stepFn_ref (σ := σ) (henv := henvC4)
    (k := (.tgtOpK (.chain []) [] [] [] [] .vals
      [.add (.var "c") (.intLit 1 .int)] [] (.seqn #[])
      ([] :: [] :: envU envW "i" na)
      (.seq [] ([] :: [] :: envU envW "i" na)
        (.seq [] ([] :: envU envW "i" na)
          (.seq [] (envU envW "i" na)
            (wloopK rF rI rL "i" body envW k))))))
    (ch := ch))
  -- addr → evalE add → evalE (var c) (2 pure steps)
  have hB : stepFnIter 2 σ
      (.retV (.addr (.base ⟨lc⟩))
        (.tgtOpK (.chain []) [] [] [] [] .vals
          [.add (.var "c") (.intLit 1 .int)] [] (.seqn #[])
          ([] :: [] :: envU envW "i" na)
          (.seq [] ([] :: [] :: envU envW "i" na)
            (.seq [] ([] :: envU envW "i" na)
              (.seq [] (envU envW "i" na)
                (wloopK rF rI rL "i" body envW k)))))) ch
      = .ok (.evalE (.var "c") ([] :: [] :: envU envW "i" na)
          (.strictK .add [] [.intLit 1 .int]
            ([] :: [] :: envU envW "i" na)
            (.rhsK .vals [.chain (.addr (.base ⟨lc⟩)) [] []] [] []
              (.seqn #[]) ([] :: [] :: envU envW "i" na)
              (.seq [] ([] :: [] :: envU envW "i" na)
                (.seq [] ([] :: envU envW "i" na)
                  (.seq [] (envU envW "i" na)
                    (wloopK rF rI rL "i" body envW k)))))),
        σ, ch) := by
    with_unfolding_all rfl
  have h7 := stepFnIter_one (stepFn_var (σ := σ) (henv := henvC4)
    (hlook := hC)
    (k := (.strictK .add [] [.intLit 1 .int]
      ([] :: [] :: envU envW "i" na)
      (.rhsK .vals [.chain (.addr (.base ⟨lc⟩)) [] []] [] []
        (.seqn #[]) ([] :: [] :: envU envW "i" na)
        (.seq [] ([] :: [] :: envU envW "i" na)
          (.seq [] ([] :: envU envW "i" na)
            (.seq [] (envU envW "i" na)
              (wloopK rF rI rL "i" body envW k)))))))
    (ch := ch))
  -- retV cv → evalE lit → retV 1 (2 pure steps)
  have hCc : stepFnIter 2 σ
      (.retV (.int cv .int)
        (.strictK .add [] [.intLit 1 .int]
          ([] :: [] :: envU envW "i" na)
          (.rhsK .vals [.chain (.addr (.base ⟨lc⟩)) [] []] [] []
            (.seqn #[]) ([] :: [] :: envU envW "i" na)
            (.seq [] ([] :: [] :: envU envW "i" na)
              (.seq [] ([] :: envU envW "i" na)
                (.seq [] (envU envW "i" na)
                  (wloopK rF rI rL "i" body envW k))))))) ch
      = .ok (.retV (.int 1 .int)
          (.strictK .add [.int cv .int] []
            ([] :: [] :: envU envW "i" na)
            (.rhsK .vals [.chain (.addr (.base ⟨lc⟩)) [] []] [] []
              (.seqn #[]) ([] :: [] :: envU envW "i" na)
              (.seq [] ([] :: [] :: envU envW "i" na)
                (.seq [] ([] :: envU envW "i" na)
                  (.seq [] (envU envW "i" na)
                    (wloopK rF rI rL "i" body envW k)))))),
        σ, ch) := by
    with_unfolding_all rfl
  have h10 := stepFnIter_one (stepFn_strict_apply (σ := σ)
    (op := .add) (done := [.int cv .int]) (v := .int 1 .int)
    (env := [] :: [] :: envU envW "i" na)
    (k := (.rhsK .vals [.chain (.addr (.base ⟨lc⟩)) [] []] [] []
      (.seqn #[]) ([] :: [] :: envU envW "i" na)
      (.seq [] ([] :: [] :: envU envW "i" na)
        (.seq [] ([] :: envU envW "i" na)
          (.seq [] (envU envW "i" na)
            (wloopK rF rI rL "i" body envW k))))))
    (ch := ch) (h := applyStrictOp_add_int (by omega) h1))
  have hE : stepFnIter 1 σ
      (.retV (.int (cv + 1) .int)
        (.rhsK .vals [.chain (.addr (.base ⟨lc⟩)) [] []] [] []
          (.seqn #[]) ([] :: [] :: envU envW "i" na)
          (.seq [] ([] :: [] :: envU envW "i" na)
            (.seq [] ([] :: envU envW "i" na)
              (.seq [] (envU envW "i" na)
                (wloopK rF rI rL "i" body envW k)))))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨lc⟩)) [] []]
          [.int (cv + 1) .int] (.seqn #[])
          ([] :: [] :: envU envW "i" na)
          (.seq [] ([] :: [] :: envU envW "i" na)
            (.seq [] ([] :: envU envW "i" na)
              (.seq [] (envU envW "i" na)
                (wloopK rF rI rL "i" body envW k))))),
        σ, ch) := by
    with_unfolding_all rfl
  have h12 := stepFnIter_one (stepFn_store_step
    (rs := []) (vs := []) (body := .seqn #[])
    (env := [] :: [] :: envU envW "i" na)
    (k := (.seq [] ([] :: [] :: envU envW "i" na)
      (.seq [] ([] :: envU envW "i" na)
        (.seq [] (envU envW "i" na)
          (wloopK rF rI rL "i" body envW k)))))
    (ch := ch)
    (h := storeTarget_addr (ty := tI) (old := .int cv .int)
      (hlook := hC) (hnorm := normalize_int_signed (by omega) h1)))
  have hF : stepFnIter 4
      { σ with heap := Heap.set σ.heap (.base ⟨lc⟩) (idxCell (cv + 1)) }
      (.next (.storeK [] [] (.seqn #[]) ([] :: [] :: envU envW "i" na)
        (.seq [] ([] :: [] :: envU envW "i" na)
          (.seq [] ([] :: envU envW "i" na)
            (.seq [] (envU envW "i" na)
              (wloopK rF rI rL "i" body envW k)))))) ch
      = .ok (bodyDoneCfg rF rI rL "i" body envW k na,
        { σ with heap := Heap.set σ.heap (.base ⟨lc⟩) (idxCell (cv + 1)) },
        ch) := by
    have hx1 := stepFnIter_one (stepFn_storeK_nil
      (σ := { σ with heap := (Heap.set σ.heap (.base ⟨lc⟩)
        (idxCell (cv + 1))) })
      (body := .seqn #[]) (env := [] :: [] :: envU envW "i" na)
      (k := (.seq [] ([] :: [] :: envU envW "i" na)
        (.seq [] ([] :: envU envW "i" na)
          (.seq [] (envU envW "i" na)
            (wloopK rF rI rL "i" body envW k))))) (ch := ch))
    have hx2 := stepFnIter_one (stepFn_seqn_splice
      (σ := { σ with heap := (Heap.set σ.heap (.base ⟨lc⟩)
        (idxCell (cv + 1))) })
      (ss := #[]) (env := [] :: [] :: envU envW "i" na) (rest := [])
      (k := (.seq [] ([] :: envU envW "i" na)
        (.seq [] (envU envW "i" na)
          (wloopK rF rI rL "i" body envW k)))) (ch := ch))
    rw [show (Array.toList (#[] : Array Stmt) ++ ([] : List Stmt)) = []
      from rfl] at hx2
    have hx3 : stepFnIter 2
        { σ with heap := (Heap.set σ.heap (.base ⟨lc⟩)
          (idxCell (cv + 1))) }
        (.next (.seq [] ([] :: [] :: envU envW "i" na)
          (.seq [] ([] :: envU envW "i" na)
            (.seq [] (envU envW "i" na)
              (wloopK rF rI rL "i" body envW k))))) ch
        = .ok (bodyDoneCfg rF rI rL "i" body envW k na,
          { σ with heap := (Heap.set σ.heap (.base ⟨lc⟩)
            (idxCell (cv + 1))) }, ch) := by
      with_unfolding_all rfl
    exact stepFnIter_chain hx1 (stepFnIter_chain hx2 hx3)
  exact stepFnIter_chain hA (stepFnIter_chain h4 (stepFnIter_chain hB
    (stepFnIter_chain h7 (stepFnIter_chain hCc (stepFnIter_chain h10
      (stepFnIter_chain hE (stepFnIter_chain h12 hF)))))))

end ActSeg

/-! ## 7. Shared state plumbing -/

/-- A `FreshFrom` heap misses its frontier address. -/
theorem lookup_none_of_freshFrom {h : Heap} {na : Nat}
    (hf : FreshFrom h na) : Heap.lookup h (.base ⟨na⟩) = none := by
  cases hl : Heap.lookup h (.base ⟨na⟩) with
  | none => rfl
  | some c =>
      have := FreshFrom.lt_of_lookup hf hl
      omega

/-- The liveness backing array's element read. -/
theorem vs_map_bool {bs : List Bool} {i : Nat} (h : i < bs.length) :
    ((bs.map GoValue.bool).toArray)[i]? = some (.bool (bs.getD i false)) := by
  rw [List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem h]
  simp [List.getD, List.getElem?_eq_getElem h]

/-- `bindState`, double-set collapsed to the single index write. -/
theorem bindState_eq (σ : ExecState) (a : Int) :
    bindState σ a = { σ with
      heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) (idxCell a),
      nextAddr := σ.nextAddr + 1 } := by
  unfold bindState
  rw [set_set]

/-- `glueState` preserves the allocator. -/
theorem glueState_na (lf li i : Nat) (σ : ExecState) :
    (glueState lf li i σ).nextAddr = σ.nextAddr := by
  unfold glueState flagSet idxSet
  split <;> rfl

/-- A cell off both glue targets survives the glue write. -/
theorem glue_lookup_other {lf li i : Nat} {σ : ExecState} {x : Nat}
    (hxf : x ≠ lf) (hxi : x ≠ li) :
    Heap.lookup (glueState lf li i σ).heap (.base ⟨x⟩)
      = Heap.lookup σ.heap (.base ⟨x⟩) := by
  unfold glueState flagSet idxSet
  split <;> exact lookup_set_other (by omega)

/-- The glue write's freshness carry: targets are live cells, so the
frontier stays missing. -/
theorem glue_freshFrom {lf li i : Nat} {σ : ExecState} {na : Nat}
    (hf : FreshFrom σ.heap na) (hlf : lf < na) (hli : li < na) :
    FreshFrom (glueState lf li i σ).heap na := by
  unfold glueState flagSet idxSet
  split
  · exact FreshFrom.set hf hlf
  · exact FreshFrom.set hf hli

/-! ## 8. THE REBUILD INSTANCE -/

/-- The rebuild `then`-branch statement. -/
def rebThn : Stmt :=
  .block #[] #[.mapAssign (.var "live") (.var "j") (.boolLit true)
    tI .bool]

theorem rebuildBody_eq : rebuildBody = guardedBody "j" rebThn := rfl

/-- **The rebuild loop invariant** at iteration `i`: control cells at
their scheduled values, the twin route (`t`-cell → twin struct → live
backing) intact, the live map holding exactly `liveIdx bs i`, the
allocator at `na0 + i` with a fresh frontier. -/
def RebuildInv (lf li ll lt tw lb lm bMap : Nat)
    (dtyT dtyTw dtyB dtyM : Option Ty) (fs : Array (String × GoValue))
    (bs : List Bool) (na0 : Nat) (i : Nat) (σ : ExecState) : Prop :=
  Heap.lookup σ.heap (.base ⟨lf⟩) = some (flagCell (i == 0))
  ∧ Heap.lookup σ.heap (.base ⟨li⟩) = some (idxCell (idxAt i))
  ∧ Heap.lookup σ.heap (.base ⟨ll⟩) = some (idxCell (bs.length : Int))
  ∧ Heap.lookup σ.heap (.base ⟨lt⟩) = some ⟨dtyT, .addr (.base ⟨tw⟩)⟩
  ∧ Heap.lookup σ.heap (.base ⟨tw⟩) = some ⟨dtyTw, .struct tidTwin fs⟩
  ∧ Heap.lookup σ.heap (.base ⟨lb⟩)
      = some ⟨dtyB, .array (bs.map GoValue.bool).toArray⟩
  ∧ Heap.lookup σ.heap (.base ⟨lm⟩)
      = some ⟨dtyM, .map ⟨some (.base ⟨bMap⟩)⟩⟩
  ∧ Heap.lookup σ.heap (.base ⟨bMap⟩)
      = some ⟨none, .mapData (bEntries (liveIdx bs i))⟩
  ∧ σ.nextAddr = na0 + i
  ∧ FreshFrom σ.heap σ.nextAddr

section Rebuild

variable {envW : LocalEnv} {k : Cont} {ch : Choices}
  {lf li ll lt tw lb lm bMap : Nat}
  {dtyT dtyTw dtyB dtyM : Option Ty}
  {fs : Array (String × GoValue)} {bs : List Bool} {cap na0 : Nat}

/-- **The rebuild BODY fact** (the kit's `hbody` shape at `bB = 24`):
from the glue-written, index-bound state the guarded body completes
normally within 24 steps and re-establishes the invariant. -/
theorem rebuild_body_fact
    (hFI : lf ≠ li)
    (hOff : ∀ x ∈ [ll, lt, tw, lb, lm, bMap], x ≠ lf ∧ x ≠ li)
    (hbmOff : ∀ x ∈ [lf, li, ll, lt, tw, lb, lm], bMap ≠ x)
    (henvT : LocalEnv.lookup envW "t" = some (.base ⟨lt⟩))
    (henvM : LocalEnv.lookup envW "live" = some (.base ⟨lm⟩))
    (hLive : StructFields.lookup fs "live"
      = some (.slice ⟨some (.base ⟨lb⟩), 0, bs.length, cap⟩))
    (hcap : bs.length ≤ cap) (hn63 : (bs.length : Int) < 2 ^ 63) :
    ∀ i σ ch, i < bs.length →
      RebuildInv lf li ll lt tw lb lm bMap dtyT dtyTw dtyB dtyM fs bs
        na0 i σ →
      ∃ m ≤ 24, ∃ σ',
        stepFnIter m (bindState (glueState lf li i σ) i)
          (bodyCfg "$rfirst" "$ridx" "$rlen" "j" (guardedBody "j" rebThn)
            envW k σ.nextAddr) ch
          = .ok (bodyDoneCfg "$rfirst" "$ridx" "$rlen" "j"
              (guardedBody "j" rebThn) envW k σ.nextAddr, σ', ch)
        ∧ RebuildInv lf li ll lt tw lb lm bMap dtyT dtyTw dtyB dtyM fs
            bs na0 (i + 1) σ' := by
  intro i σ ch hin hInv
  obtain ⟨hflag, hidx, hlen, hT, hTw, hB, hM, hD, hna, hfresh⟩ := hInv
  have hlfna : lf < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hflag
  have hlina : li < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hidx
  have hllna : ll < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hlen
  have hltna : lt < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hT
  have htwna : tw < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hTw
  have hlbna : lb < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hB
  have hlmna : lm < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hM
  have hbmna : bMap < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hD
  have hgfresh : FreshFrom (glueState lf li i σ).heap σ.nextAddr :=
    glue_freshFrom hfresh hlfna hlina
  -- the mid state, collapsed to one bind write over the glue heap
  rw [bindState_glue]
  -- generic lookup transport into the mid heap
  have gl : ∀ {x : Nat} {c : HeapCell}, x ≠ lf → x ≠ li →
      Heap.lookup σ.heap (.base ⟨x⟩) = some c →
      Heap.lookup (Heap.set (glueState lf li i σ).heap
        (.base ⟨σ.nextAddr⟩) (idxCell (i : Int))) (.base ⟨x⟩)
        = some c := by
    intro x c hxf hxi hx
    have hxna : x < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hx
    rw [lookup_set_other (by omega : σ.nextAddr ≠ x),
      glue_lookup_other hxf hxi]
    exact hx
  have hmidT := gl (hOff lt (by simp)).1 (hOff lt (by simp)).2 hT
  have hmidTw := gl (hOff tw (by simp)).1 (hOff tw (by simp)).2 hTw
  have hmidB := gl (hOff lb (by simp)).1 (hOff lb (by simp)).2 hB
  have hmidM := gl (hOff lm (by simp)).1 (hOff lm (by simp)).2 hM
  have hmidD := gl (hOff bMap (by simp)).1 (hOff bMap (by simp)).2 hD
  have hmidU : Heap.lookup (Heap.set (glueState lf li i σ).heap
      (.base ⟨σ.nextAddr⟩) (idxCell (i : Int))) (.base ⟨σ.nextAddr⟩)
      = some (idxCell (i : Int)) := lookup_set_self
  -- the mid flag/idx cells (case on first-vs-later glue)
  have hmidlf : Heap.lookup (Heap.set (glueState lf li i σ).heap
      (.base ⟨σ.nextAddr⟩) (idxCell (i : Int))) (.base ⟨lf⟩)
      = some (flagCell false) := by
    rw [lookup_set_other (by omega : σ.nextAddr ≠ lf)]
    unfold glueState flagSet idxSet
    by_cases hi0 : i = 0
    · rw [if_pos hi0]
      exact lookup_set_self
    · rw [if_neg hi0]
      show Heap.lookup (Heap.set σ.heap (.base ⟨li⟩) _) (.base ⟨lf⟩) = _
      rw [lookup_set_other (Ne.symm hFI), hflag]
      have hb0 : (i == 0) = false := by
        cases i with
        | zero => exact absurd rfl hi0
        | succ _ => rfl
      rw [hb0]
  have hmidli : Heap.lookup (Heap.set (glueState lf li i σ).heap
      (.base ⟨σ.nextAddr⟩) (idxCell (i : Int))) (.base ⟨li⟩)
      = some (idxCell (i : Int)) := by
    rw [lookup_set_other (by omega : σ.nextAddr ≠ li)]
    unfold glueState flagSet idxSet
    by_cases hi0 : i = 0
    · rw [if_pos hi0]
      show Heap.lookup (Heap.set σ.heap (.base ⟨lf⟩) _) (.base ⟨li⟩) = _
      rw [lookup_set_other hFI, hidx, hi0]
      rfl
    · rw [if_neg hi0]
      exact lookup_set_self
  -- the guard walk (13 steps)
  have hguard := guard_seg (rF := "$rfirst") (rI := "$ridx")
    (rL := "$rlen") (uV := "j") (thn := rebThn) (envW := envW) (k := k)
    (σ := { σ with
      heap := Heap.set (glueState lf li i σ).heap
        (.base ⟨σ.nextAddr⟩) (idxCell (i : Int)),
      nextAddr := σ.nextAddr + 1 })
    (ch := ch) (na := σ.nextAddr)
    (by decide) henvT (tw := tw) (lb := lb)
    (fs := fs) (n := bs.length) (cap := cap)
    (vs := (bs.map GoValue.bool).toArray) (i := i)
    (b := bs.getD i false)
    hmidT hmidTw hLive hmidB hcap hin (vs_map_bool hin) hmidU
    (by omega)
  -- the invariant-recovery helpers
  have hb0succ : ((i + 1 : Nat) == 0) = false := by simp
  have hliveIdx_lt : ∀ j ∈ liveIdx bs i, j ≠ i :=
    fun j hj => Nat.ne_of_lt (liveIdx_lt hj)
  by_cases hbv : bs.getD i false
  · -- guard TRUE: map insert
    rw [hbv] at hguard
    have hact := act_rebuild (rF := "$rfirst") (rI := "$ridx")
      (rL := "$rlen") (body := guardedBody "j" rebThn) (envW := envW)
      (k := k)
      (σ := { σ with
        heap := Heap.set (glueState lf li i σ).heap
          (.base ⟨σ.nextAddr⟩) (idxCell (i : Int)),
        nextAddr := σ.nextAddr + 1 })
      (ch := ch) (na := σ.nextAddr) (lm := lm) (bMap := bMap)
      (dtyM := dtyM) (js := liveIdx bs i) (i := i)
      henvM hmidM hmidD hmidU hliveIdx_lt (by omega)
    have hrun := stepFnIter_chain hguard (by simpa [rebThn] using hact)
    refine ⟨24, by omega, _, hrun, ?_⟩
    · -- RebuildInv (i+1) at the map-written state
      have peel : ∀ {x : Nat} {c : HeapCell}, bMap ≠ x →
          Heap.lookup (Heap.set (glueState lf li i σ).heap
            (.base ⟨σ.nextAddr⟩) (idxCell (i : Int))) (.base ⟨x⟩)
            = some c →
          Heap.lookup (Heap.set (Heap.set (glueState lf li i σ).heap
            (.base ⟨σ.nextAddr⟩) (idxCell (i : Int))) (.base ⟨bMap⟩)
            ⟨none, .mapData (bEntries (liveIdx bs i ++ [i]))⟩)
            (.base ⟨x⟩) = some c := by
        intro x c hne h
        rw [lookup_set_other hne]
        exact h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hb0succ]
        exact peel (hbmOff lf (by simp)) hmidlf
      · rw [idxAt_succ]
        exact peel (hbmOff li (by simp)) hmidli
      · exact peel (hbmOff ll (by simp))
          (gl (hOff ll (by simp)).1 (hOff ll (by simp)).2 hlen)
      · exact peel (hbmOff lt (by simp)) hmidT
      · exact peel (hbmOff tw (by simp)) hmidTw
      · exact peel (hbmOff lb (by simp)) hmidB
      · exact peel (hbmOff lm (by simp)) hmidM
      · rw [show liveIdx bs (i + 1) = liveIdx bs i ++ [i] from by
          rw [liveIdx_succ, if_pos hbv]]
        exact lookup_set_self
      · show σ.nextAddr + 1 = na0 + (i + 1)
        omega
      · show FreshFrom _ (σ.nextAddr + 1)
        refine FreshFrom.set ?_ (by omega)
        rw [set_fresh (lookup_none_of_freshFrom hgfresh)]
        exact FreshFrom.push hgfresh
  · -- guard FALSE: skip
    rw [show bs.getD i false = false from by
      cases h : bs.getD i false
      · rfl
      · exact absurd h hbv] at hguard
    have hact := act_skip (rF := "$rfirst") (rI := "$ridx")
      (rL := "$rlen") (uV := "j") (body := guardedBody "j" rebThn)
      (envW := envW) (k := k)
      (σ := { σ with
        heap := Heap.set (glueState lf li i σ).heap
          (.base ⟨σ.nextAddr⟩) (idxCell (i : Int)),
        nextAddr := σ.nextAddr + 1 })
      (ch := ch) (na := σ.nextAddr)
    have hrun := stepFnIter_chain hguard hact
    refine ⟨15, by omega, _, hrun, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hb0succ]
        exact hmidlf
      · rw [idxAt_succ]
        exact hmidli
      · exact gl (hOff ll (by simp)).1 (hOff ll (by simp)).2 hlen
      · exact hmidT
      · exact hmidTw
      · exact hmidB
      · exact hmidM
      · rw [show liveIdx bs (i + 1) = liveIdx bs i from by
          rw [liveIdx_succ, if_neg hbv, List.append_nil]]
        exact hmidD
      · show σ.nextAddr + 1 = na0 + (i + 1)
        omega
      · show FreshFrom _ (σ.nextAddr + 1)
        rw [set_fresh (lookup_none_of_freshFrom hgfresh)]
        exact FreshFrom.push hgfresh

/-- **THE SYMBOLIC-NET REBUILD SPAN** (C2b headline 1): from ANY loop
head whose state satisfies the rebuild invariant at 0, the live-map
rebuild completes within `67 * n + 31` interpreter steps — `n` and
the liveness payload `bs` fully symbolic — delivering the loop's
continuation with the live map holding EXACTLY the live indices.
`67 = 43 + 24` reproduces the census's measured 67-step iteration. -/
theorem rebuildLoop_span
    (hFI : lf ≠ li)
    (hLFI : ll ≠ lf ∧ ll ≠ li)
    (hOff : ∀ x ∈ [ll, lt, tw, lb, lm, bMap], x ≠ lf ∧ x ≠ li)
    (hbmOff : ∀ x ∈ [lf, li, ll, lt, tw, lb, lm], bMap ≠ x)
    (henvF : LocalEnv.lookup envW "$rfirst" = some (.base ⟨lf⟩))
    (henvI : LocalEnv.lookup envW "$ridx" = some (.base ⟨li⟩))
    (henvL : LocalEnv.lookup envW "$rlen" = some (.base ⟨ll⟩))
    (henvT : LocalEnv.lookup envW "t" = some (.base ⟨lt⟩))
    (henvM : LocalEnv.lookup envW "live" = some (.base ⟨lm⟩))
    (hLive : StructFields.lookup fs "live"
      = some (.slice ⟨some (.base ⟨lb⟩), 0, bs.length, cap⟩))
    (hcap : bs.length ≤ cap) (hn63 : (bs.length : Int) < 2 ^ 63) :
    ∀ σ ch,
      RebuildInv lf li ll lt tw lb lm bMap dtyT dtyTw dtyB dtyM fs bs
        na0 0 σ →
      ∃ m ≤ 67 * bs.length + 31, ∃ σf,
        RebuildInv lf li ll lt tw lb lm bMap dtyT dtyTw dtyB dtyM fs
          bs na0 bs.length σf
        ∧ stepFnIter m σ
            (headCfg "$rfirst" "$ridx" "$rlen" "j"
              (guardedBody "j" rebThn) envW k) ch
            = .ok (.next k, glueState lf li bs.length σf, ch) := by
  intro σ ch hInv
  have h := sliceWalk_loop (rF := "$rfirst") (rI := "$ridx")
    (rL := "$rlen") (uV := "j") (body := guardedBody "j" rebThn)
    (envW := envW) (k := k)
    hFI hLFI.1 hLFI.2 (by decide) henvF henvI henvL
    (n := bs.length) (bB := 24) hn63
    (RebuildInv lf li ll lt tw lb lm bMap dtyT dtyTw dtyB dtyM fs bs na0)
    (fun i σ' _ hI => by
      obtain ⟨h1, h2, h3, _, _, _, _, _, _, h10⟩ := hI
      exact ⟨h1, h2, h3, lookup_none_of_freshFrom h10⟩)
    (fun i σ' ch' hilt hI =>
      rebuild_body_fact hFI hOff hbmOff henvT henvM hLive hcap hn63
        i σ' ch' hilt hI)
    0 σ ch (Nat.zero_le _) hInv
  obtain ⟨m, hm, σf, hSf, hrun⟩ := h
  exact ⟨m, by simpa using hm, σf, hSf, hrun⟩


end Rebuild

/-! ## 9. THE LIVECOUNT INSTANCE -/

/-- The liveCount `then`-branch statement. -/
def incThn : Stmt :=
  .block #[] #[.assign (.var "c") (.add (.var "c") (.intLit 1 .int))]

theorem lcBody_eq : lcBody = guardedBody "i" incThn := rfl

/-- `countTrue` is bounded by the index. -/
theorem countTrue_le {bs : List Bool} : ∀ i, countTrue bs i ≤ i := by
  intro i
  induction i with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
      rw [countTrue_succ]
      split <;> omega

/-- **The liveCount loop invariant** at iteration `i`. -/
def LiveCountInv (lf li ll lt tw lb lc : Nat)
    (dtyT dtyTw dtyB : Option Ty) (fs : Array (String × GoValue))
    (bs : List Bool) (na0 : Nat) (i : Nat) (σ : ExecState) : Prop :=
  Heap.lookup σ.heap (.base ⟨lf⟩) = some (flagCell (i == 0))
  ∧ Heap.lookup σ.heap (.base ⟨li⟩) = some (idxCell (idxAt i))
  ∧ Heap.lookup σ.heap (.base ⟨ll⟩) = some (idxCell (bs.length : Int))
  ∧ Heap.lookup σ.heap (.base ⟨lt⟩) = some ⟨dtyT, .addr (.base ⟨tw⟩)⟩
  ∧ Heap.lookup σ.heap (.base ⟨tw⟩) = some ⟨dtyTw, .struct tidTwin fs⟩
  ∧ Heap.lookup σ.heap (.base ⟨lb⟩)
      = some ⟨dtyB, .array (bs.map GoValue.bool).toArray⟩
  ∧ Heap.lookup σ.heap (.base ⟨lc⟩)
      = some (idxCell (countTrue bs i : Int))
  ∧ σ.nextAddr = na0 + i
  ∧ FreshFrom σ.heap σ.nextAddr

section LiveCount

variable {envW : LocalEnv} {k : Cont} {ch : Choices}
  {lf li ll lt tw lb lc : Nat}
  {dtyT dtyTw dtyB : Option Ty}
  {fs : Array (String × GoValue)} {bs : List Bool} {cap na0 : Nat}

/-- **The liveCount BODY fact** (the kit's `hbody` shape at
`bB = 29`). -/
theorem liveCount_body_fact
    (hFI : lf ≠ li)
    (hOff : ∀ x ∈ [ll, lt, tw, lb, lc], x ≠ lf ∧ x ≠ li)
    (hlcOff : ∀ x ∈ [lf, li, ll, lt, tw, lb], lc ≠ x)
    (henvT : LocalEnv.lookup envW "t" = some (.base ⟨lt⟩))
    (henvC : LocalEnv.lookup envW "c" = some (.base ⟨lc⟩))
    (hLive : StructFields.lookup fs "live"
      = some (.slice ⟨some (.base ⟨lb⟩), 0, bs.length, cap⟩))
    (hcap : bs.length ≤ cap) (hn63 : (bs.length : Int) < 2 ^ 63) :
    ∀ i σ ch, i < bs.length →
      LiveCountInv lf li ll lt tw lb lc dtyT dtyTw dtyB fs bs na0 i σ →
      ∃ m ≤ 29, ∃ σ',
        stepFnIter m (bindState (glueState lf li i σ) i)
          (bodyCfg "$rfirst" "$ridx" "$rlen" "i" (guardedBody "i" incThn)
            envW k σ.nextAddr) ch
          = .ok (bodyDoneCfg "$rfirst" "$ridx" "$rlen" "i"
              (guardedBody "i" incThn) envW k σ.nextAddr, σ', ch)
        ∧ LiveCountInv lf li ll lt tw lb lc dtyT dtyTw dtyB fs bs na0
            (i + 1) σ' := by
  intro i σ ch hin hInv
  obtain ⟨hflag, hidx, hlen, hT, hTw, hB, hC, hna, hfresh⟩ := hInv
  have hlfna : lf < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hflag
  have hlina : li < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hidx
  have hltna : lt < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hT
  have htwna : tw < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hTw
  have hlbna : lb < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hB
  have hlcna : lc < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hC
  have hgfresh : FreshFrom (glueState lf li i σ).heap σ.nextAddr :=
    glue_freshFrom hfresh hlfna hlina
  rw [bindState_glue]
  have gl : ∀ {x : Nat} {c : HeapCell}, x ≠ lf → x ≠ li →
      Heap.lookup σ.heap (.base ⟨x⟩) = some c →
      Heap.lookup (Heap.set (glueState lf li i σ).heap
        (.base ⟨σ.nextAddr⟩) (idxCell (i : Int))) (.base ⟨x⟩)
        = some c := by
    intro x c hxf hxi hx
    have hxna : x < σ.nextAddr := FreshFrom.lt_of_lookup hfresh hx
    rw [lookup_set_other (by omega : σ.nextAddr ≠ x),
      glue_lookup_other hxf hxi]
    exact hx
  have hmidT := gl (hOff lt (by simp)).1 (hOff lt (by simp)).2 hT
  have hmidTw := gl (hOff tw (by simp)).1 (hOff tw (by simp)).2 hTw
  have hmidB := gl (hOff lb (by simp)).1 (hOff lb (by simp)).2 hB
  have hmidC := gl (hOff lc (by simp)).1 (hOff lc (by simp)).2 hC
  have hmidU : Heap.lookup (Heap.set (glueState lf li i σ).heap
      (.base ⟨σ.nextAddr⟩) (idxCell (i : Int))) (.base ⟨σ.nextAddr⟩)
      = some (idxCell (i : Int)) := lookup_set_self
  have hmidlf : Heap.lookup (Heap.set (glueState lf li i σ).heap
      (.base ⟨σ.nextAddr⟩) (idxCell (i : Int))) (.base ⟨lf⟩)
      = some (flagCell false) := by
    rw [lookup_set_other (by omega : σ.nextAddr ≠ lf)]
    unfold glueState flagSet idxSet
    by_cases hi0 : i = 0
    · rw [if_pos hi0]
      exact lookup_set_self
    · rw [if_neg hi0]
      show Heap.lookup (Heap.set σ.heap (.base ⟨li⟩) _) (.base ⟨lf⟩) = _
      rw [lookup_set_other (Ne.symm hFI), hflag]
      have hb0 : (i == 0) = false := by
        cases i with
        | zero => exact absurd rfl hi0
        | succ _ => rfl
      rw [hb0]
  have hmidli : Heap.lookup (Heap.set (glueState lf li i σ).heap
      (.base ⟨σ.nextAddr⟩) (idxCell (i : Int))) (.base ⟨li⟩)
      = some (idxCell (i : Int)) := by
    rw [lookup_set_other (by omega : σ.nextAddr ≠ li)]
    unfold glueState flagSet idxSet
    by_cases hi0 : i = 0
    · rw [if_pos hi0]
      show Heap.lookup (Heap.set σ.heap (.base ⟨lf⟩) _) (.base ⟨li⟩) = _
      rw [lookup_set_other hFI, hidx, hi0]
      rfl
    · rw [if_neg hi0]
      exact lookup_set_self
  have hguard := guard_seg (rF := "$rfirst") (rI := "$ridx")
    (rL := "$rlen") (uV := "i") (thn := incThn) (envW := envW) (k := k)
    (σ := { σ with
      heap := Heap.set (glueState lf li i σ).heap
        (.base ⟨σ.nextAddr⟩) (idxCell (i : Int)),
      nextAddr := σ.nextAddr + 1 })
    (ch := ch) (na := σ.nextAddr)
    (by decide) henvT (tw := tw) (lb := lb)
    (fs := fs) (n := bs.length) (cap := cap)
    (vs := (bs.map GoValue.bool).toArray) (i := i)
    (b := bs.getD i false)
    hmidT hmidTw hLive hmidB hcap hin (vs_map_bool hin) hmidU
    (by omega)
  have hb0succ : ((i + 1 : Nat) == 0) = false := by simp
  have hcnt := countTrue_le (bs := bs) i
  by_cases hbv : bs.getD i false
  · -- guard TRUE: increment
    rw [hbv] at hguard
    have hact := act_inc (rF := "$rfirst") (rI := "$ridx")
      (rL := "$rlen") (body := guardedBody "i" incThn) (envW := envW)
      (k := k)
      (σ := { σ with
        heap := Heap.set (glueState lf li i σ).heap
          (.base ⟨σ.nextAddr⟩) (idxCell (i : Int)),
        nextAddr := σ.nextAddr + 1 })
      (ch := ch) (na := σ.nextAddr) (lc := lc)
      (cv := (countTrue bs i : Int))
      henvC hmidC (by omega) (by omega)
    have hrun := stepFnIter_chain hguard (by simpa [incThn] using hact)
    refine ⟨29, by omega, _, hrun, ?_⟩
    · have peel : ∀ {x : Nat} {c : HeapCell}, lc ≠ x →
          Heap.lookup (Heap.set (glueState lf li i σ).heap
            (.base ⟨σ.nextAddr⟩) (idxCell (i : Int))) (.base ⟨x⟩)
            = some c →
          Heap.lookup (Heap.set (Heap.set (glueState lf li i σ).heap
            (.base ⟨σ.nextAddr⟩) (idxCell (i : Int))) (.base ⟨lc⟩)
            (idxCell ((countTrue bs i : Int) + 1))) (.base ⟨x⟩)
            = some c := by
        intro x c hne h
        rw [lookup_set_other hne]
        exact h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hb0succ]
        exact peel (hlcOff lf (by simp)) hmidlf
      · rw [idxAt_succ]
        exact peel (hlcOff li (by simp)) hmidli
      · exact peel (hlcOff ll (by simp))
          (gl (hOff ll (by simp)).1 (hOff ll (by simp)).2 hlen)
      · exact peel (hlcOff lt (by simp)) hmidT
      · exact peel (hlcOff tw (by simp)) hmidTw
      · exact peel (hlcOff lb (by simp)) hmidB
      · rw [show ((countTrue bs (i + 1) : Nat) : Int)
            = (countTrue bs i : Int) + 1 from by
          rw [countTrue_succ, if_pos hbv]
          omega]
        exact lookup_set_self
      · show σ.nextAddr + 1 = na0 + (i + 1)
        omega
      · show FreshFrom _ (σ.nextAddr + 1)
        refine FreshFrom.set ?_ (by omega)
        rw [set_fresh (lookup_none_of_freshFrom hgfresh)]
        exact FreshFrom.push hgfresh
  · -- guard FALSE: skip
    rw [show bs.getD i false = false from by
      cases h : bs.getD i false
      · rfl
      · exact absurd h hbv] at hguard
    have hact := act_skip (rF := "$rfirst") (rI := "$ridx")
      (rL := "$rlen") (uV := "i") (body := guardedBody "i" incThn)
      (envW := envW) (k := k)
      (σ := { σ with
        heap := Heap.set (glueState lf li i σ).heap
          (.base ⟨σ.nextAddr⟩) (idxCell (i : Int)),
        nextAddr := σ.nextAddr + 1 })
      (ch := ch) (na := σ.nextAddr)
    have hrun := stepFnIter_chain hguard hact
    refine ⟨15, by omega, _, hrun, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hb0succ]
        exact hmidlf
      · rw [idxAt_succ]
        exact hmidli
      · exact gl (hOff ll (by simp)).1 (hOff ll (by simp)).2 hlen
      · exact hmidT
      · exact hmidTw
      · exact hmidB
      · rw [show ((countTrue bs (i + 1) : Nat) : Int)
            = (countTrue bs i : Int) from by
          rw [countTrue_succ, if_neg hbv]
          omega]
        exact hmidC
      · show σ.nextAddr + 1 = na0 + (i + 1)
        omega
      · show FreshFrom _ (σ.nextAddr + 1)
        rw [set_fresh (lookup_none_of_freshFrom hgfresh)]
        exact FreshFrom.push hgfresh

/-- **THE SYMBOLIC-NET LIVECOUNT SPAN** (C2b headline 2): the count
walk completes within `72 * n + 31` steps with the counter cell at
EXACTLY the live count. `72 = 43 + 29` reproduces the census. -/
theorem liveCountLoop_span
    (hFI : lf ≠ li)
    (hLFI : ll ≠ lf ∧ ll ≠ li)
    (hOff : ∀ x ∈ [ll, lt, tw, lb, lc], x ≠ lf ∧ x ≠ li)
    (hlcOff : ∀ x ∈ [lf, li, ll, lt, tw, lb], lc ≠ x)
    (henvF : LocalEnv.lookup envW "$rfirst" = some (.base ⟨lf⟩))
    (henvI : LocalEnv.lookup envW "$ridx" = some (.base ⟨li⟩))
    (henvL : LocalEnv.lookup envW "$rlen" = some (.base ⟨ll⟩))
    (henvT : LocalEnv.lookup envW "t" = some (.base ⟨lt⟩))
    (henvC : LocalEnv.lookup envW "c" = some (.base ⟨lc⟩))
    (hLive : StructFields.lookup fs "live"
      = some (.slice ⟨some (.base ⟨lb⟩), 0, bs.length, cap⟩))
    (hcap : bs.length ≤ cap) (hn63 : (bs.length : Int) < 2 ^ 63) :
    ∀ σ ch,
      LiveCountInv lf li ll lt tw lb lc dtyT dtyTw dtyB fs bs na0 0 σ →
      ∃ m ≤ 72 * bs.length + 31, ∃ σf,
        LiveCountInv lf li ll lt tw lb lc dtyT dtyTw dtyB fs bs na0
          bs.length σf
        ∧ stepFnIter m σ
            (headCfg "$rfirst" "$ridx" "$rlen" "i"
              (guardedBody "i" incThn) envW k) ch
            = .ok (.next k, glueState lf li bs.length σf, ch) := by
  intro σ ch hInv
  have h := sliceWalk_loop (rF := "$rfirst") (rI := "$ridx")
    (rL := "$rlen") (uV := "i") (body := guardedBody "i" incThn)
    (envW := envW) (k := k)
    hFI hLFI.1 hLFI.2 (by decide) henvF henvI henvL
    (n := bs.length) (bB := 29) hn63
    (LiveCountInv lf li ll lt tw lb lc dtyT dtyTw dtyB fs bs na0)
    (fun i σ' _ hI => by
      obtain ⟨h1, h2, h3, _, _, _, _, _, h9⟩ := hI
      exact ⟨h1, h2, h3, lookup_none_of_freshFrom h9⟩)
    (fun i σ' ch' hilt hI =>
      liveCount_body_fact hFI hOff hlcOff henvT henvC hLive hcap hn63
        i σ' ch' hilt hI)
    0 σ ch (Nat.zero_le _) hInv
  obtain ⟨m, hm, σf, hSf, hrun⟩ := h
  exact ⟨m, by simpa using hm, σf, hSf, hrun⟩

end LiveCount


end GoLean.RaftSeam.DriverNet
