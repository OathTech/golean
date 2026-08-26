import GoLeanProofs.Specs.Raft.SpanS23Walk1

/-!
# The apply walk, part 2 (A4d-SM2): the violation-branch engine

The four violation branches (S3-index, S3-term, anomaly, S2) all
share the shape: a run of `$c := utoa(arg)` units followed by a
`t.viol(<concat>)` call. This module carries the shared engine:

- **`BrCells`** — the cell pack a branch preserves and its argument
  reads consume (the two S3 branches and the anomaly branch read only
  through it).
- **`concat6_eval`** — the 6-part left-nested concat spine's
  evaluation (both S3 branches' viol argument; 21 steps).
- **`s3Branch_walk`** — ONE walk for BOTH S3 fire branches
  (parameterized by the three gensym names, argument expressions +
  delivery facts, and the three literals): three `utoaUnit_walk`
  rides + the concat + `viol_call_span`, ending `.next K` with
  `violations` incremented EXACTLY and the trace existential.

LINEAGE: conditioned-single composition (StepKit); P-H call spans.
-/

namespace GoLean.RaftSeam.SpanS23

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.RaftSeam.UtoaSpan
open GoLean.RaftSeam.SpanCells
open GoLean.RaftSeam.SpanS1 (tyTwinD tyNodeD tidT tidN idE)
open GoLean.Examples.RaftTwin (twinLowered)
open GoLean.StringMem (gs)

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-! ## 1. The branch cell pack -/

/-- The cells a violation branch preserves and its argument reads
consume: the `t`/`nd` parameter cells, the twin and node structs, and
the `idx`/`trm` locals. -/
def BrCells (na₀ tw nw : Nat) (twc ndc icell tcell : HeapCell)
    (σ' : ExecState) : Prop :=
  Heap.lookup σ'.heap (.base ⟨na₀⟩) = some (tParA tw)
    ∧ Heap.lookup σ'.heap (.base ⟨na₀ + 1⟩) = some (ndParA nw)
    ∧ Heap.lookup σ'.heap (.base ⟨tw⟩) = some twc
    ∧ Heap.lookup σ'.heap (.base ⟨nw⟩) = some ndc
    ∧ Heap.lookup σ'.heap (.base ⟨na₀ + 3⟩) = some icell
    ∧ Heap.lookup σ'.heap (.base ⟨na₀ + 6⟩) = some tcell

/-! ## 2. The 6-part concat spine -/

section Concat

variable {env' : LocalEnv} {K : Cont} {c1 c2 c3 : String}
  {l1 l2 l3 : Nat} {s1 s2 s3 : GoString} {L1 L2 L3 : GoString}

/-- The two S3 branches' viol argument, spelled. -/
def concat6 (L1 : GoString) (c1 : String) (L2 : GoString)
    (c2 : String) (L3 : GoString) (c3 : String) : Expr :=
  .add (.add (.add (.add (.add (.stringLit L1) (.var c1))
    (.stringLit L2)) (.var c2)) (.stringLit L3)) (.var c3)

/-- The 6-part concat spine's evaluation (21 steps): three string
cells read, five appends, state untouched. -/
theorem concat6_eval (σ : ExecState) (ch : Choices)
    (henv1 : LocalEnv.lookup env' c1 = some (.base ⟨l1⟩))
    (henv2 : LocalEnv.lookup env' c2 = some (.base ⟨l2⟩))
    (henv3 : LocalEnv.lookup env' c3 = some (.base ⟨l3⟩))
    (h1 : Heap.lookup σ.heap (.base ⟨l1⟩) = some (sCell s1))
    (h2 : Heap.lookup σ.heap (.base ⟨l2⟩) = some (sCell s2))
    (h3 : Heap.lookup σ.heap (.base ⟨l3⟩) = some (sCell s3)) :
    stepFnIter 21 σ
        (.evalE (concat6 L1 c1 L2 c2 L3 c3) env' K) ch
      = .ok (.retV (.string (GoString.append (GoString.append
          (GoString.append (GoString.append (GoString.append
            L1 s1) L2) s2) L3) s3)) K, σ, ch) := by
  -- descend the spine to L1 and deliver it (6 steps)
  have hA : stepFnIter 6 σ
      (.evalE (concat6 L1 c1 L2 c2 L3 c3) env' K) ch
      = .ok (.retV (.string L1)
          (.strictK .add [] [.var c1] env'
            (.strictK .add [] [.stringLit L2] env'
              (.strictK .add [] [.var c2] env'
                (.strictK .add [] [.stringLit L3] env'
                  (.strictK .add [] [.var c3] env' K))))), σ, ch) := by
    with_unfolding_all rfl
  -- c1 (2 steps: shift + var read)
  have hB : stepFnIter 1 σ (.retV (.string L1)
      (.strictK .add [] [.var c1] env'
        (.strictK .add [] [.stringLit L2] env'
          (.strictK .add [] [.var c2] env'
            (.strictK .add [] [.stringLit L3] env'
              (.strictK .add [] [.var c3] env' K)))))) ch
      = .ok (.evalE (.var c1)
          (env')
          (.strictK .add [.string L1] [] env'
            (.strictK .add [] [.stringLit L2] env'
              (.strictK .add [] [.var c2] env'
                (.strictK .add [] [.stringLit L3] env'
                  (.strictK .add [] [.var c3] env' K))))), σ, ch) := by
    with_unfolding_all rfl
  have hC : stepFnIter 1 σ (.evalE (.var c1) env'
      (.strictK .add [.string L1] [] env'
        (.strictK .add [] [.stringLit L2] env'
          (.strictK .add [] [.var c2] env'
            (.strictK .add [] [.stringLit L3] env'
              (.strictK .add [] [.var c3] env' K)))))) ch
      = .ok (.retV (.string s1)
          (.strictK .add [.string L1] [] env'
            (.strictK .add [] [.stringLit L2] env'
              (.strictK .add [] [.var c2] env'
                (.strictK .add [] [.stringLit L3] env'
                  (.strictK .add [] [.var c3] env' K))))), σ, ch) :=
    stepFnIter_one (stepFn_var (henv := henv1) (hlook := h1))
  have hD : stepFnIter 1 σ (.retV (.string s1)
      (.strictK .add [.string L1] [] env'
        (.strictK .add [] [.stringLit L2] env'
          (.strictK .add [] [.var c2] env'
            (.strictK .add [] [.stringLit L3] env'
              (.strictK .add [] [.var c3] env' K)))))) ch
      = .ok (.retV (.string (GoString.append L1 s1))
          (.strictK .add [] [.stringLit L2] env'
            (.strictK .add [] [.var c2] env'
              (.strictK .add [] [.stringLit L3] env'
                (.strictK .add [] [.var c3] env' K)))), σ, ch) := by
    refine stepFnIter_one (stepFn_strict_apply (h := ?_))
    rw [show (List.reverse [GoValue.string s1, GoValue.string L1])
      = [GoValue.string L1, GoValue.string s1] from rfl]
    exact applyStrictOp_add_string
  -- L2 (3 steps: shift + lit + apply)
  have hE : stepFnIter 3 σ
      (.retV (.string (GoString.append L1 s1))
        (.strictK .add [] [.stringLit L2] env'
          (.strictK .add [] [.var c2] env'
            (.strictK .add [] [.stringLit L3] env'
              (.strictK .add [] [.var c3] env' K))))) ch
      = .ok (.retV (.string (GoString.append (GoString.append L1 s1)
            L2))
          (.strictK .add [] [.var c2] env'
            (.strictK .add [] [.stringLit L3] env'
              (.strictK .add [] [.var c3] env' K))), σ, ch) := by
    have e1 : stepFnIter 2 σ
        (.retV (.string (GoString.append L1 s1))
          (.strictK .add [] [.stringLit L2] env'
            (.strictK .add [] [.var c2] env'
              (.strictK .add [] [.stringLit L3] env'
                (.strictK .add [] [.var c3] env' K))))) ch
        = .ok (.retV (.string L2)
            (.strictK .add [.string (GoString.append L1 s1)] [] env'
              (.strictK .add [] [.var c2] env'
                (.strictK .add [] [.stringLit L3] env'
                  (.strictK .add [] [.var c3] env' K)))), σ, ch) := by
      with_unfolding_all rfl
    have e2 : stepFnIter 1 σ (.retV (.string L2)
        (.strictK .add [.string (GoString.append L1 s1)] [] env'
          (.strictK .add [] [.var c2] env'
            (.strictK .add [] [.stringLit L3] env'
              (.strictK .add [] [.var c3] env' K))))) ch
        = .ok (.retV (.string (GoString.append (GoString.append L1 s1)
              L2))
            (.strictK .add [] [.var c2] env'
              (.strictK .add [] [.stringLit L3] env'
                (.strictK .add [] [.var c3] env' K))), σ, ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.string L2,
          GoValue.string (GoString.append L1 s1)])
        = [GoValue.string (GoString.append L1 s1),
            GoValue.string L2] from rfl]
      exact applyStrictOp_add_string
    exact stepFnIter_chain e1 e2
  -- c2 (3 steps: shift + var + apply)
  have hF : stepFnIter 3 σ
      (.retV (.string (GoString.append (GoString.append L1 s1) L2))
        (.strictK .add [] [.var c2] env'
          (.strictK .add [] [.stringLit L3] env'
            (.strictK .add [] [.var c3] env' K)))) ch
      = .ok (.retV (.string (GoString.append (GoString.append
            (GoString.append L1 s1) L2) s2))
          (.strictK .add [] [.stringLit L3] env'
            (.strictK .add [] [.var c3] env' K)), σ, ch) := by
    have f1 : stepFnIter 1 σ
        (.retV (.string (GoString.append (GoString.append L1 s1) L2))
          (.strictK .add [] [.var c2] env'
            (.strictK .add [] [.stringLit L3] env'
              (.strictK .add [] [.var c3] env' K)))) ch
        = .ok (.evalE (.var c2) env'
            (.strictK .add
              [.string (GoString.append (GoString.append L1 s1) L2)]
              [] env'
              (.strictK .add [] [.stringLit L3] env'
                (.strictK .add [] [.var c3] env' K))), σ, ch) := by
      with_unfolding_all rfl
    have f2 : stepFnIter 1 σ (.evalE (.var c2) env'
        (.strictK .add
          [.string (GoString.append (GoString.append L1 s1) L2)]
          [] env'
          (.strictK .add [] [.stringLit L3] env'
            (.strictK .add [] [.var c3] env' K)))) ch
        = .ok (.retV (.string s2)
            (.strictK .add
              [.string (GoString.append (GoString.append L1 s1) L2)]
              [] env'
              (.strictK .add [] [.stringLit L3] env'
                (.strictK .add [] [.var c3] env' K))), σ, ch) :=
      stepFnIter_one (stepFn_var (henv := henv2) (hlook := h2))
    have f3 : stepFnIter 1 σ (.retV (.string s2)
        (.strictK .add
          [.string (GoString.append (GoString.append L1 s1) L2)]
          [] env'
          (.strictK .add [] [.stringLit L3] env'
            (.strictK .add [] [.var c3] env' K)))) ch
        = .ok (.retV (.string (GoString.append (GoString.append
              (GoString.append L1 s1) L2) s2))
            (.strictK .add [] [.stringLit L3] env'
              (.strictK .add [] [.var c3] env' K)), σ, ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.string s2,
          GoValue.string (GoString.append (GoString.append L1 s1)
            L2)])
        = [GoValue.string (GoString.append (GoString.append L1 s1)
            L2), GoValue.string s2] from rfl]
      exact applyStrictOp_add_string
    exact stepFnIter_chain (stepFnIter_chain f1 f2) f3
  -- L3 (3) then c3 (3)
  have hG : stepFnIter 3 σ
      (.retV (.string (GoString.append (GoString.append
          (GoString.append L1 s1) L2) s2))
        (.strictK .add [] [.stringLit L3] env'
          (.strictK .add [] [.var c3] env' K))) ch
      = .ok (.retV (.string (GoString.append (GoString.append
            (GoString.append (GoString.append L1 s1) L2) s2) L3))
          (.strictK .add [] [.var c3] env' K), σ, ch) := by
    have g1 : stepFnIter 2 σ
        (.retV (.string (GoString.append (GoString.append
            (GoString.append L1 s1) L2) s2))
          (.strictK .add [] [.stringLit L3] env'
            (.strictK .add [] [.var c3] env' K))) ch
        = .ok (.retV (.string L3)
            (.strictK .add
              [.string (GoString.append (GoString.append
                (GoString.append L1 s1) L2) s2)] [] env'
              (.strictK .add [] [.var c3] env' K)), σ, ch) := by
      with_unfolding_all rfl
    have g2 : stepFnIter 1 σ (.retV (.string L3)
        (.strictK .add
          [.string (GoString.append (GoString.append
            (GoString.append L1 s1) L2) s2)] [] env'
          (.strictK .add [] [.var c3] env' K))) ch
        = .ok (.retV (.string (GoString.append (GoString.append
              (GoString.append (GoString.append L1 s1) L2) s2) L3))
            (.strictK .add [] [.var c3] env' K), σ, ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.string L3,
          GoValue.string (GoString.append (GoString.append
            (GoString.append L1 s1) L2) s2)])
        = [GoValue.string (GoString.append (GoString.append
            (GoString.append L1 s1) L2) s2),
            GoValue.string L3] from rfl]
      exact applyStrictOp_add_string
    exact stepFnIter_chain g1 g2
  have hH : stepFnIter 3 σ
      (.retV (.string (GoString.append (GoString.append
          (GoString.append (GoString.append L1 s1) L2) s2) L3))
        (.strictK .add [] [.var c3] env' K)) ch
      = .ok (.retV (.string (GoString.append (GoString.append
            (GoString.append (GoString.append (GoString.append
              L1 s1) L2) s2) L3) s3)) K, σ, ch) := by
    have i1 : stepFnIter 1 σ
        (.retV (.string (GoString.append (GoString.append
            (GoString.append (GoString.append L1 s1) L2) s2) L3))
          (.strictK .add [] [.var c3] env' K)) ch
        = .ok (.evalE (.var c3) env'
            (.strictK .add
              [.string (GoString.append (GoString.append
                (GoString.append (GoString.append L1 s1) L2) s2)
                L3)] [] env' K), σ, ch) := by
      with_unfolding_all rfl
    have i2 : stepFnIter 1 σ (.evalE (.var c3) env'
        (.strictK .add
          [.string (GoString.append (GoString.append
            (GoString.append (GoString.append L1 s1) L2) s2) L3)]
          [] env' K)) ch
        = .ok (.retV (.string s3)
            (.strictK .add
              [.string (GoString.append (GoString.append
                (GoString.append (GoString.append L1 s1) L2) s2)
                L3)] [] env' K), σ, ch) :=
      stepFnIter_one (stepFn_var (henv := henv3) (hlook := h3))
    have i3 : stepFnIter 1 σ (.retV (.string s3)
        (.strictK .add
          [.string (GoString.append (GoString.append
            (GoString.append (GoString.append L1 s1) L2) s2) L3)]
          [] env' K)) ch
        = .ok (.retV (.string (GoString.append (GoString.append
              (GoString.append (GoString.append (GoString.append
                L1 s1) L2) s2) L3) s3)) K, σ, ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.string s3,
          GoValue.string (GoString.append (GoString.append
            (GoString.append (GoString.append L1 s1) L2) s2) L3)])
        = [GoValue.string (GoString.append (GoString.append
            (GoString.append (GoString.append L1 s1) L2) s2) L3),
            GoValue.string s3] from rfl]
      exact applyStrictOp_add_string
    exact stepFnIter_chain (stepFnIter_chain i1 i2) i3
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      hA hB) hC) hD) hE) hF) (stepFnIter_chain hG hH)

end Concat

/-! ## 3. Env lookup helpers (symbolic gensym names) -/

theorem scope_lookup_head (c : String) (l : Loc) (sc : Scope) :
    Scope.lookup ((c, l) :: sc) c = some l := by
  simp [Scope.lookup]

theorem scope_lookup_ne {c x : String} (h : c ≠ x) (l : Loc)
    (sc : Scope) :
    Scope.lookup ((c, l) :: sc) x = Scope.lookup sc x := by
  simp [Scope.lookup, beq_eq_false_iff_ne.mpr h]

theorem env_lookup_head {sc : Scope} {env : LocalEnv} {x : String}
    {l : Loc} (h : Scope.lookup sc x = some l) :
    LocalEnv.lookup (sc :: env) x = some l := by
  simp [LocalEnv.lookup, h]

theorem env_lookup_skip {sc : Scope} {env : LocalEnv} {x : String}
    (h : Scope.lookup sc x = none) :
    LocalEnv.lookup (sc :: env) x = LocalEnv.lookup env x := by
  simp [LocalEnv.lookup, h]

/-! ## 4. The S3 fire-branch engine -/

section Branch

variable {env0 : LocalEnv} {K : Cont} {na₀ tw nw : Nat}
  {ndc icell tcell : HeapCell}
  {nodesV netV liveV byV pendV drvV hlV : GoValue} {lm : Nat}
  {cc cm w sq : Int} {tr : GoString}

/-- **The S3 fire-branch walk** (both S3 branches; the anomaly and S2
branches ride the same units with their own spines): three
`utoaUnit_walk` rides + the 6-part concat + `viol_call_span`,
ending `.next K` with `violations` incremented EXACTLY, the trace
existential, and every cell below the entry frontier except the twin
framed. -/
theorem s3Branch_walk
    (c1 c2 c3 : String) (argE1 argE2 argE3 : Expr)
    (L1 L2 L3 : GoString) {a1 a2 a3 : Nat} {k1 k2 k3 : Nat}
    (ha1 : a1 < 2 ^ 64) (ha2 : a2 < 2 ^ 64) (ha3 : a3 < 2 ^ 64)
    (hne21 : c2 ≠ c1) (hne31 : c3 ≠ c1) (hne32 : c3 ≠ c2)
    (hf1 : c1 ≠ "t" ∧ c1 ≠ "nd" ∧ c1 ≠ "idx" ∧ c1 ≠ "trm")
    (hf2 : c2 ≠ "t" ∧ c2 ≠ "nd" ∧ c2 ≠ "idx" ∧ c2 ≠ "trm")
    (hf3 : c3 ≠ "t" ∧ c3 ≠ "nd" ∧ c3 ≠ "idx" ∧ c3 ≠ "trm")
    (henvT0 : LocalEnv.lookup env0 "t" = some (.base ⟨na₀⟩))
    (henvN0 : LocalEnv.lookup env0 "nd" = some (.base ⟨na₀ + 1⟩))
    (henvI0 : LocalEnv.lookup env0 "idx" = some (.base ⟨na₀ + 3⟩))
    (henvR0 : LocalEnv.lookup env0 "trm" = some (.base ⟨na₀ + 6⟩))
    (σB : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σB)
    (hfr : ∀ x, σB.nextAddr ≤ x →
      Heap.lookup σB.heap (.base ⟨x⟩) = none)
    (hBr : BrCells na₀ tw nw
      (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr hlV)
      ndc icell tcell σB)
    (harg1 : ∀ (σ' : ExecState) (env' : LocalEnv) (K' : Cont),
      BrCells na₀ tw nw
        (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr hlV)
        ndc icell tcell σ' →
      LocalEnv.lookup env' "nd" = some (.base ⟨na₀ + 1⟩) →
      LocalEnv.lookup env' "idx" = some (.base ⟨na₀ + 3⟩) →
      LocalEnv.lookup env' "trm" = some (.base ⟨na₀ + 6⟩) →
      stepFnIter k1 σ' (.evalE argE1 env' K') ch
        = .ok (.retV (.int (a1 : Int) .uint64) K', σ', ch))
    (harg2 : ∀ (σ' : ExecState) (env' : LocalEnv) (K' : Cont),
      BrCells na₀ tw nw
        (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr hlV)
        ndc icell tcell σ' →
      LocalEnv.lookup env' "nd" = some (.base ⟨na₀ + 1⟩) →
      LocalEnv.lookup env' "idx" = some (.base ⟨na₀ + 3⟩) →
      LocalEnv.lookup env' "trm" = some (.base ⟨na₀ + 6⟩) →
      stepFnIter k2 σ' (.evalE argE2 env' K') ch
        = .ok (.retV (.int (a2 : Int) .uint64) K', σ', ch))
    (harg3 : ∀ (σ' : ExecState) (env' : LocalEnv) (K' : Cont),
      BrCells na₀ tw nw
        (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr hlV)
        ndc icell tcell σ' →
      LocalEnv.lookup env' "nd" = some (.base ⟨na₀ + 1⟩) →
      LocalEnv.lookup env' "idx" = some (.base ⟨na₀ + 3⟩) →
      LocalEnv.lookup env' "trm" = some (.base ⟨na₀ + 6⟩) →
      stepFnIter k3 σ' (.evalE argE3 env' K') ch
        = .ok (.retV (.int (a3 : Int) .uint64) K', σ', ch))
    (hc0 : -(2 ^ 63) ≤ cc) (hc1 : cc < 2 ^ 63)
    (hm0 : -(2 ^ 63) ≤ cm) (hm1 : cm < 2 ^ 63)
    (hw0 : -(2 ^ 63) ≤ w) (hw1 : w + 1 < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63) :
    ∃ m ≤ k1 + k2 + k3 + 4800, ∃ σ' : ExecState, ∃ tr' : GoString,
      stepFnIter m σB
          (.exec (.block #[] #[utoaUnit c1 argE1, utoaUnit c2 argE2,
            utoaUnit c3 argE3,
            .call #[] ⟨"main.twin.viol"⟩
              #[.var "t", concat6 L1 c1 L2 c2 L3 c3]]) env0 K) ch
        = .ok (.next K, σ', ch)
      ∧ Heap.lookup σ'.heap (.base ⟨tw⟩)
          = some (twCell nodesV netV liveV lm byV cc cm (w + 1)
              pendV drvV sq tr' hlV)
      ∧ (∀ x, x < σB.nextAddr → x ≠ tw →
          Heap.lookup σ'.heap (.base ⟨x⟩)
            = Heap.lookup σB.heap (.base ⟨x⟩))
      ∧ σB.nextAddr + 11 ≤ σ'.nextAddr
      ∧ σ'.nextAddr ≤ σB.nextAddr + 17
      ∧ (∀ x, σ'.nextAddr ≤ x →
          Heap.lookup σ'.heap (.base ⟨x⟩) = none)
      ∧ bfTB.Agrees σ' := by
  obtain ⟨htP, hnP, hTw, hNd, hIc, hTc⟩ := hBr
  -- address bounds
  have htPna : na₀ < σB.nextAddr := by
    rcases Nat.lt_or_ge na₀ σB.nextAddr with h | h
    · exact h
    · rw [hfr na₀ h] at htP; cases htP
  have hnPna : na₀ + 1 < σB.nextAddr := by
    rcases Nat.lt_or_ge (na₀ + 1) σB.nextAddr with h | h
    · exact h
    · rw [hfr (na₀ + 1) h] at hnP; cases hnP
  have htwna : tw < σB.nextAddr := by
    rcases Nat.lt_or_ge tw σB.nextAddr with h | h
    · exact h
    · rw [hfr tw h] at hTw; cases hTw
  have hnwna : nw < σB.nextAddr := by
    rcases Nat.lt_or_ge nw σB.nextAddr with h | h
    · exact h
    · rw [hfr nw h] at hNd; cases hNd
  have hicna : na₀ + 3 < σB.nextAddr := by
    rcases Nat.lt_or_ge (na₀ + 3) σB.nextAddr with h | h
    · exact h
    · rw [hfr (na₀ + 3) h] at hIc; cases hIc
  have htcna : na₀ + 6 < σB.nextAddr := by
    rcases Nat.lt_or_ge (na₀ + 6) σB.nextAddr with h | h
    · exact h
    · rw [hfr (na₀ + 6) h] at hTc; cases hTc
  -- B0: block + pop (2)
  let env2 : LocalEnv := [] :: env0
  have hB0 : stepFnIter 2 σB
      (.exec (.block #[] #[utoaUnit c1 argE1, utoaUnit c2 argE2,
        utoaUnit c3 argE3,
        .call #[] ⟨"main.twin.viol"⟩
          #[.var "t", concat6 L1 c1 L2 c2 L3 c3]]) env0 K) ch
      = .ok (.exec (utoaUnit c1 argE1) env2
          (.seq [utoaUnit c2 argE2, utoaUnit c3 argE3,
            .call #[] ⟨"main.twin.viol"⟩
              #[.var "t", concat6 L1 c1 L2 c2 L3 c3]] env2 K),
        σB, ch) :=
    stepFnIter_chain (stepFnIter_one stepFn_block)
      (stepFnIter_one stepFn_seq_pop)
  -- ===== UNIT 1 =====
  let env2a : LocalEnv := [(c1, Loc.base ⟨σB.nextAddr⟩)] :: env0
  have henvc1 : LocalEnv.lookup (env2.declare c1
      (.base ⟨σB.nextAddr⟩)) c1 = some (.base ⟨σB.nextAddr⟩) :=
    env_lookup_head (scope_lookup_head ..)
  have henvN2a : LocalEnv.lookup env2a "nd" = some (.base ⟨na₀ + 1⟩) := by
    rw [env_lookup_skip (by
      rw [scope_lookup_ne hf1.2.1]
      rfl)]
    exact henvN0
  have henvI2a : LocalEnv.lookup env2a "idx"
      = some (.base ⟨na₀ + 3⟩) := by
    rw [env_lookup_skip (by
      rw [scope_lookup_ne hf1.2.2.1]
      rfl)]
    exact henvI0
  have henvR2a : LocalEnv.lookup env2a "trm"
      = some (.base ⟨na₀ + 6⟩) := by
    rw [env_lookup_skip (by
      rw [scope_lookup_ne hf1.2.2.2]
      rfl)]
    exact henvR0
  have hBrF1 : BrCells na₀ tw nw
      (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr hlV)
      ndc icell tcell
      { σB with heap := Heap.set σB.heap (.base ⟨σB.nextAddr⟩) (sCell (gs [])), nextAddr := σB.nextAddr + 1 } := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · show Heap.lookup (Heap.set σB.heap (.base ⟨σB.nextAddr⟩) _)
          _ = _
        rw [lookup_set_other (by omega)]
        first
          | exact htP | exact hnP | exact hTw | exact hNd
          | exact hIc | exact hTc
  have hU1 := utoaUnit_walk (envQ := env2)
    (rest := [utoaUnit c2 argE2, utoaUnit c3 argE3,
      .call #[] ⟨"main.twin.viol"⟩
        #[.var "t", concat6 L1 c1 L2 c2 L3 c3]])
    (K := K) (c := c1) (argE := argE1) (ka := k1) (av := a1)
    σB ch hag hfr ha1 henvc1
    (harg1 _ _ _ hBrF1 henvN2a henvI2a henvR2a)
  obtain ⟨m1, hb1, s1, σU1, hrun1, hcell1, hna1lo, hna1hi, hfrm1,
    hfrs1, hag1⟩ := hU1
  have hBrU1 : BrCells na₀ tw nw
      (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr hlV)
      ndc icell tcell σU1 :=
    ⟨by rw [hfrm1 na₀ (by omega)]; exact htP,
     by rw [hfrm1 (na₀ + 1) (by omega)]; exact hnP,
     by rw [hfrm1 tw (by omega)]; exact hTw,
     by rw [hfrm1 nw (by omega)]; exact hNd,
     by rw [hfrm1 (na₀ + 3) (by omega)]; exact hIc,
     by rw [hfrm1 (na₀ + 6) (by omega)]; exact hTc⟩
  -- drain to unit 2 (2)
  have hD1 : stepFnIter 2 σU1
      (.exec (.seqn #[]) env2a
        (.seq [utoaUnit c2 argE2, utoaUnit c3 argE3,
          .call #[] ⟨"main.twin.viol"⟩
            #[.var "t", concat6 L1 c1 L2 c2 L3 c3]] env2a K)) ch
      = .ok (.exec (utoaUnit c2 argE2) env2a
          (.seq [utoaUnit c3 argE3,
            .call #[] ⟨"main.twin.viol"⟩
              #[.var "t", concat6 L1 c1 L2 c2 L3 c3]] env2a K),
        σU1, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  -- ===== UNIT 2 =====
  let env2b : LocalEnv :=
    [(c2, Loc.base ⟨σU1.nextAddr⟩), (c1, Loc.base ⟨σB.nextAddr⟩)]
      :: env0
  have henvc2 : LocalEnv.lookup (env2a.declare c2
      (.base ⟨σU1.nextAddr⟩)) c2 = some (.base ⟨σU1.nextAddr⟩) :=
    env_lookup_head (scope_lookup_head ..)
  have henvN2b : LocalEnv.lookup env2b "nd"
      = some (.base ⟨na₀ + 1⟩) := by
    rw [env_lookup_skip (by
      rw [scope_lookup_ne hf2.2.1, scope_lookup_ne hf1.2.1]
      rfl)]
    exact henvN0
  have henvI2b : LocalEnv.lookup env2b "idx"
      = some (.base ⟨na₀ + 3⟩) := by
    rw [env_lookup_skip (by
      rw [scope_lookup_ne hf2.2.2.1, scope_lookup_ne hf1.2.2.1]
      rfl)]
    exact henvI0
  have henvR2b : LocalEnv.lookup env2b "trm"
      = some (.base ⟨na₀ + 6⟩) := by
    rw [env_lookup_skip (by
      rw [scope_lookup_ne hf2.2.2.2, scope_lookup_ne hf1.2.2.2]
      rfl)]
    exact henvR0
  have hBrF2 : BrCells na₀ tw nw
      (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr hlV)
      ndc icell tcell
      { σU1 with heap := Heap.set σU1.heap (.base ⟨σU1.nextAddr⟩) (sCell (gs [])), nextAddr := σU1.nextAddr + 1 } := by
    obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hBrU1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · show Heap.lookup (Heap.set σU1.heap (.base ⟨σU1.nextAddr⟩) _)
          _ = _
        rw [lookup_set_other (by omega)]
        first
          | exact j1 | exact j2 | exact j3 | exact j4
          | exact j5 | exact j6
  have hU2 := utoaUnit_walk (envQ := env2a)
    (rest := [utoaUnit c3 argE3,
      .call #[] ⟨"main.twin.viol"⟩
        #[.var "t", concat6 L1 c1 L2 c2 L3 c3]])
    (K := K) (c := c2) (argE := argE2) (ka := k2) (av := a2)
    σU1 ch hag1 hfrs1 ha2 henvc2
    (harg2 _ _ _ hBrF2 henvN2b henvI2b henvR2b)
  obtain ⟨m2, hb2, s2, σU2, hrun2, hcell2, hna2lo, hna2hi, hfrm2,
    hfrs2, hag2⟩ := hU2
  have hBrU2 : BrCells na₀ tw nw
      (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr hlV)
      ndc icell tcell σU2 := by
    obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hBrU1
    exact ⟨by rw [hfrm2 na₀ (by omega)]; exact j1,
      by rw [hfrm2 (na₀ + 1) (by omega)]; exact j2,
      by rw [hfrm2 tw (by omega)]; exact j3,
      by rw [hfrm2 nw (by omega)]; exact j4,
      by rw [hfrm2 (na₀ + 3) (by omega)]; exact j5,
      by rw [hfrm2 (na₀ + 6) (by omega)]; exact j6⟩
  have hcell1U2 : Heap.lookup σU2.heap (.base ⟨σB.nextAddr⟩)
      = some (sCell s1) := by
    rw [hfrm2 σB.nextAddr (by omega)]
    exact hcell1
  -- drain to unit 3 (2)
  have hD2 : stepFnIter 2 σU2
      (.exec (.seqn #[]) env2b
        (.seq [utoaUnit c3 argE3,
          .call #[] ⟨"main.twin.viol"⟩
            #[.var "t", concat6 L1 c1 L2 c2 L3 c3]] env2b K)) ch
      = .ok (.exec (utoaUnit c3 argE3) env2b
          (.seq [.call #[] ⟨"main.twin.viol"⟩
            #[.var "t", concat6 L1 c1 L2 c2 L3 c3]] env2b K),
        σU2, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  -- ===== UNIT 3 =====
  let env2c : LocalEnv :=
    [(c3, Loc.base ⟨σU2.nextAddr⟩), (c2, Loc.base ⟨σU1.nextAddr⟩),
      (c1, Loc.base ⟨σB.nextAddr⟩)] :: env0
  have henvc3 : LocalEnv.lookup (env2b.declare c3
      (.base ⟨σU2.nextAddr⟩)) c3 = some (.base ⟨σU2.nextAddr⟩) :=
    env_lookup_head (scope_lookup_head ..)
  have henvN2c : LocalEnv.lookup env2c "nd"
      = some (.base ⟨na₀ + 1⟩) := by
    rw [env_lookup_skip (by
      rw [scope_lookup_ne hf3.2.1, scope_lookup_ne hf2.2.1,
        scope_lookup_ne hf1.2.1]
      rfl)]
    exact henvN0
  have henvI2c : LocalEnv.lookup env2c "idx"
      = some (.base ⟨na₀ + 3⟩) := by
    rw [env_lookup_skip (by
      rw [scope_lookup_ne hf3.2.2.1, scope_lookup_ne hf2.2.2.1,
        scope_lookup_ne hf1.2.2.1]
      rfl)]
    exact henvI0
  have henvR2c : LocalEnv.lookup env2c "trm"
      = some (.base ⟨na₀ + 6⟩) := by
    rw [env_lookup_skip (by
      rw [scope_lookup_ne hf3.2.2.2, scope_lookup_ne hf2.2.2.2,
        scope_lookup_ne hf1.2.2.2]
      rfl)]
    exact henvR0
  have hBrF3 : BrCells na₀ tw nw
      (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr hlV)
      ndc icell tcell
      { σU2 with heap := Heap.set σU2.heap (.base ⟨σU2.nextAddr⟩) (sCell (gs [])), nextAddr := σU2.nextAddr + 1 } := by
    obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hBrU2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · show Heap.lookup (Heap.set σU2.heap (.base ⟨σU2.nextAddr⟩) _)
          _ = _
        rw [lookup_set_other (by omega)]
        first
          | exact j1 | exact j2 | exact j3 | exact j4
          | exact j5 | exact j6
  have hU3 := utoaUnit_walk (envQ := env2b)
    (rest := [.call #[] ⟨"main.twin.viol"⟩
      #[.var "t", concat6 L1 c1 L2 c2 L3 c3]])
    (K := K) (c := c3) (argE := argE3) (ka := k3) (av := a3)
    σU2 ch hag2 hfrs2 ha3 henvc3
    (harg3 _ _ _ hBrF3 henvN2c henvI2c henvR2c)
  obtain ⟨m3, hb3, s3, σU3, hrun3, hcell3, hna3lo, hna3hi, hfrm3,
    hfrs3, hag3⟩ := hU3
  have hBrU3 : BrCells na₀ tw nw
      (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr hlV)
      ndc icell tcell σU3 := by
    obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hBrU2
    exact ⟨by rw [hfrm3 na₀ (by omega)]; exact j1,
      by rw [hfrm3 (na₀ + 1) (by omega)]; exact j2,
      by rw [hfrm3 tw (by omega)]; exact j3,
      by rw [hfrm3 nw (by omega)]; exact j4,
      by rw [hfrm3 (na₀ + 3) (by omega)]; exact j5,
      by rw [hfrm3 (na₀ + 6) (by omega)]; exact j6⟩
  have hcell1U3 : Heap.lookup σU3.heap (.base ⟨σB.nextAddr⟩)
      = some (sCell s1) := by
    rw [hfrm3 σB.nextAddr (by omega)]
    exact hcell1U2
  have hcell2U3 : Heap.lookup σU3.heap (.base ⟨σU1.nextAddr⟩)
      = some (sCell s2) := by
    rw [hfrm3 σU1.nextAddr (by omega)]
    exact hcell2
  -- drain to the viol call (2)
  have hD3 : stepFnIter 2 σU3
      (.exec (.seqn #[]) env2c
        (.seq [.call #[] ⟨"main.twin.viol"⟩
          #[.var "t", concat6 L1 c1 L2 c2 L3 c3]] env2c K)) ch
      = .ok (.exec (.call #[] ⟨"main.twin.viol"⟩
          #[.var "t", concat6 L1 c1 L2 c2 L3 c3]) env2c
          (.seq [] env2c K), σU3, ch) :=
    stepFnIter_splice_pop (ss := #[]) rfl
  -- ===== THE VIOL CALL =====
  -- V1: the plan step (1)
  have hV1 : stepFnIter 1 σU3
      (.exec (.call #[] ⟨"main.twin.viol"⟩
        #[.var "t", concat6 L1 c1 L2 c2 L3 c3]) env2c
        (.seq [] env2c K)) ch
      = .ok (.evalE (.var "t") env2c
          (.callArgsK ⟨"main.twin.viol"⟩ [] []
            [concat6 L1 c1 L2 c2 L3 c3] env2c (.seq [] env2c K)),
        σU3, ch) := by
    with_unfolding_all rfl
  -- V2: the t read (1)
  have henvT2c : LocalEnv.lookup env2c "t" = some (.base ⟨na₀⟩) := by
    rw [env_lookup_skip (by
      rw [scope_lookup_ne hf3.1, scope_lookup_ne hf2.1,
        scope_lookup_ne hf1.1]
      rfl)]
    exact henvT0
  have hV2 : stepFnIter 1 σU3 (.evalE (.var "t") env2c
      (.callArgsK ⟨"main.twin.viol"⟩ [] []
        [concat6 L1 c1 L2 c2 L3 c3] env2c (.seq [] env2c K))) ch
      = .ok (.retV (.addr (.base ⟨tw⟩))
          (.callArgsK ⟨"main.twin.viol"⟩ [] []
            [concat6 L1 c1 L2 c2 L3 c3] env2c (.seq [] env2c K)),
        σU3, ch) :=
    stepFnIter_one (stepFn_var (henv := henvT2c)
      (hlook := hBrU3.1))
  -- V3: the arg advance (1)
  have hV3 : stepFnIter 1 σU3 (.retV (.addr (.base ⟨tw⟩))
      (.callArgsK ⟨"main.twin.viol"⟩ [] []
        [concat6 L1 c1 L2 c2 L3 c3] env2c (.seq [] env2c K))) ch
      = .ok (.evalE (concat6 L1 c1 L2 c2 L3 c3) env2c
          (.callArgsK ⟨"main.twin.viol"⟩ [] [.addr (.base ⟨tw⟩)]
            [] env2c (.seq [] env2c K)), σU3, ch) := by
    with_unfolding_all rfl
  -- V4: the concat spine (21)
  have henvC1 : LocalEnv.lookup env2c c1
      = some (.base ⟨σB.nextAddr⟩) :=
    env_lookup_head (by
      rw [scope_lookup_ne hne31, scope_lookup_ne hne21]
      exact scope_lookup_head ..)
  have henvC2 : LocalEnv.lookup env2c c2
      = some (.base ⟨σU1.nextAddr⟩) :=
    env_lookup_head (by
      rw [scope_lookup_ne hne32]
      exact scope_lookup_head ..)
  have henvC3 : LocalEnv.lookup env2c c3
      = some (.base ⟨σU2.nextAddr⟩) :=
    env_lookup_head (scope_lookup_head ..)
  have hV4 := concat6_eval (env' := env2c)
    (K := .callArgsK ⟨"main.twin.viol"⟩ [] [.addr (.base ⟨tw⟩)]
      [] env2c (.seq [] env2c K))
    (L1 := L1) (L2 := L2) (L3 := L3)
    σU3 ch henvC1 henvC2 henvC3 hcell1U3 hcell2U3 hcell3
  -- V5: the viol span (42)
  have hV5 := viol_call_span (envC := env2c)
    (Kc := .seq [] env2c K) (tw := tw)
    (nodesV := nodesV) (netV := netV) (liveV := liveV) (lm := lm)
    (byV := byV) (c := cc) (cm := cm) (w := w) (pendV := pendV)
    (drvV := drvV) (sq := sq) (tr := tr) (hlV := hlV)
    σU3 ch
    (GoString.append (GoString.append (GoString.append
      (GoString.append (GoString.append L1 s1) L2) s2) L3) s3)
    hag3 hBrU3.2.2.1 hfrs3 hc0 hc1 hm0 hm1 hw0 hw1 hq0 hq1
  -- V6: the seq-nil pop (1)
  let σV : ExecState := twinSt (Heap.set (Heap.set (Heap.set σU3.heap
    (.base ⟨σU3.nextAddr⟩) (tParCell tw))
    (.base ⟨σU3.nextAddr + 1⟩) (sCell (GoString.append
      (GoString.append (GoString.append (GoString.append
        (GoString.append L1 s1) L2) s2) L3) s3)))
    (.base ⟨tw⟩)
    (twCell nodesV netV liveV lm byV cc cm (w + 1) pendV drvV
      sq (GoString.append tr (GoString.append (gs [32, 33])
        (GoString.append (GoString.append (GoString.append
          (GoString.append (GoString.append L1 s1) L2) s2) L3) s3)))
      hlV))
    (σU3.nextAddr + 2)
  have hV6 : stepFnIter 1 σV (.next (.seq [] env2c K)) ch
      = .ok (.next K, σV, ch) := by
    with_unfolding_all rfl
  -- assemble
  refine ⟨2 + m1 + 2 + m2 + 2 + m3 + 2 + 1 + 1 + 1 + 21 + 42 + 1,
    by omega, σV,
    GoString.append tr (GoString.append (gs [32, 33])
      (GoString.append (GoString.append (GoString.append
        (GoString.append (GoString.append L1 s1) L2) s2) L3) s3)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
            hB0 hrun1) hD1) hrun2) hD2) hrun3) hD3) hV1) hV2) hV3)
        hV4) hV5) hV6
  · show Heap.lookup σV.heap (.base ⟨tw⟩) = _
    exact lookup_set_self
  · intro x hx hxtw
    show Heap.lookup (Heap.set (Heap.set (Heap.set σU3.heap
      (.base ⟨σU3.nextAddr⟩) _) (.base ⟨σU3.nextAddr + 1⟩) _)
      (.base ⟨tw⟩) _) (.base ⟨x⟩) = _
    rw [lookup_set_other (fun he => hxtw he.symm),
      lookup_set_other (by omega : σU3.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σU3.nextAddr ≠ x),
      hfrm3 x (by omega), hfrm2 x (by omega), hfrm1 x (by omega)]
  · show σB.nextAddr + 11 ≤ σU3.nextAddr + 2
    omega
  · show σU3.nextAddr + 2 ≤ σB.nextAddr + 17
    omega
  · intro x hx
    have hx2 : σU3.nextAddr + 2 ≤ x := hx
    show Heap.lookup (Heap.set (Heap.set (Heap.set σU3.heap
      (.base ⟨σU3.nextAddr⟩) _) (.base ⟨σU3.nextAddr + 1⟩) _)
      (.base ⟨tw⟩) _) (.base ⟨x⟩) = none
    rw [lookup_set_other (by omega : tw ≠ x),
      lookup_set_other (by omega : σU3.nextAddr + 1 ≠ x),
      lookup_set_other (by omega : σU3.nextAddr ≠ x)]
    exact hfrs3 x (by omega)
  · exact ⟨rfl, rfl, rfl, rfl⟩

end Branch

/-! ## 5. The two S3 guard segments -/

section Guards

variable {env0 : LocalEnv} {KK : Cont} {nxt : Stmt}
  {rest2 : List Stmt} {na₀ tw nw : Nat}
  {nodesV netV liveV byV pendV drvV hlV rnV stV : GoValue} {lm gm : Nat}
  {cc cm w sq : Int} {tr : GoString}
  {idvN tmvN cmvN stvN apl ltm ixN tmN : Nat}

/-- The node cell at Nat payloads (the walk's working form). -/
abbrev ndCellN (idvN : Nat) (rnV stV : GoValue)
    (tmvN cmvN stvN apl ltm : Nat) (gm : Nat) : HeapCell :=
  ndCell (idvN : Int) rnV stV (tmvN : Int) (cmvN : Int) (stvN : Int)
    (apl : Int) (ltm : Int) gm

/-- **The S3-index guard segment**: evaluate `idx <= nd.applied`; on
fire run the violation branch; either way land on the next statement
with `violations` carrying the guard readout EXACTLY. -/
theorem s3idx_seg
    (henvT0 : LocalEnv.lookup env0 "t" = some (.base ⟨na₀⟩))
    (henvN0 : LocalEnv.lookup env0 "nd" = some (.base ⟨na₀ + 1⟩))
    (henvI0 : LocalEnv.lookup env0 "idx" = some (.base ⟨na₀ + 3⟩))
    (henvR0 : LocalEnv.lookup env0 "trm" = some (.base ⟨na₀ + 6⟩))
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (hBr : BrCells na₀ tw nw
      (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr hlV)
      (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm)
      ⟨some (.int .uint64), .int (ixN : Int) .uint64⟩
      ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩ σ)
    (hidv : idvN < 2 ^ 64) (hixr : ixN < 2 ^ 64)
    (hapl : apl < 2 ^ 64)
    (hc0 : -(2 ^ 63) ≤ cc) (hc1 : cc < 2 ^ 63)
    (hm0 : -(2 ^ 63) ≤ cm) (hm1 : cm < 2 ^ 63)
    (hw0 : -(2 ^ 63) ≤ w) (hw1 : w + 1 < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63) :
    ∃ m ≤ 4900, ∃ σ' : ExecState, ∃ tr' : GoString,
      stepFnIter m σ
          (.exec s3IdxIfS env0 (.seq (nxt :: rest2) env0 KK)) ch
        = .ok (.exec nxt env0 (.seq rest2 env0 KK), σ', ch)
      ∧ Heap.lookup σ'.heap (.base ⟨tw⟩)
          = some (twCell nodesV netV liveV lm byV cc cm
              (w + (if ixN ≤ apl then 1 else 0)) pendV drvV sq
              tr' hlV)
      ∧ (∀ x, x < σ.nextAddr → x ≠ tw →
          Heap.lookup σ'.heap (.base ⟨x⟩)
            = Heap.lookup σ.heap (.base ⟨x⟩))
      ∧ σ.nextAddr ≤ σ'.nextAddr ∧ σ'.nextAddr ≤ σ.nextAddr + 17
      ∧ (∀ x, σ'.nextAddr ≤ x →
          Heap.lookup σ'.heap (.base ⟨x⟩) = none)
      ∧ bfTB.Agrees σ' := by
  obtain ⟨htP, hnP, hTw, hNd, hIc, hTc⟩ := hBr
  -- the guard evaluation (10 steps to the delivered Bool)
  have hguard : stepFnIter 10 σ
      (.exec s3IdxIfS env0 (.seq (nxt :: rest2) env0 KK)) ch
      = .ok (.retV (.bool (decide ((ixN : Int) ≤ (apl : Int))))
          (.ifK s3IdxBranch (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK)), σ, ch) := by
    have q1 : stepFnIter 2 σ
        (.exec s3IdxIfS env0 (.seq (nxt :: rest2) env0 KK)) ch
        = .ok (.evalE (.var "idx") env0
            (.strictK .atMostCmp [] [appliedE] env0
              (.ifK s3IdxBranch (.seqn #[]) env0
                (.seq (nxt :: rest2) env0 KK))), σ, ch) := by
      with_unfolding_all rfl
    have q2 : stepFnIter 1 σ (.evalE (.var "idx") env0
        (.strictK .atMostCmp [] [appliedE] env0
          (.ifK s3IdxBranch (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK)))) ch
        = .ok (.retV (.int (ixN : Int) .uint64)
            (.strictK .atMostCmp [] [appliedE] env0
              (.ifK s3IdxBranch (.seqn #[]) env0
                (.seq (nxt :: rest2) env0 KK))), σ, ch) :=
      stepFnIter_one (stepFn_var (henv := henvI0) (hlook := hIc))
    have q3 : stepFnIter 1 σ (.retV (.int (ixN : Int) .uint64)
        (.strictK .atMostCmp [] [appliedE] env0
          (.ifK s3IdxBranch (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK)))) ch
        = .ok (.evalE appliedE env0
            (.strictK .atMostCmp [.int (ixN : Int) .uint64] [] env0
              (.ifK s3IdxBranch (.seqn #[]) env0
                (.seq (nxt :: rest2) env0 KK))), σ, ch) := by
      with_unfolding_all rfl
    have q4 : stepFnIter 5 σ (.evalE appliedE env0
        (.strictK .atMostCmp [.int (ixN : Int) .uint64] [] env0
          (.ifK s3IdxBranch (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK)))) ch
        = .ok (.retV (.int (apl : Int) .uint64)
            (.strictK .atMostCmp [.int (ixN : Int) .uint64] [] env0
              (.ifK s3IdxBranch (.seqn #[]) env0
                (.seq (nxt :: rest2) env0 KK))), σ, ch) :=
      read_field_seg (henv := henvN0) (hp := hnP) (hw := hNd)
        (hf := nodeFs_applied)
    have q5 : stepFnIter 1 σ (.retV (.int (apl : Int) .uint64)
        (.strictK .atMostCmp [.int (ixN : Int) .uint64] [] env0
          (.ifK s3IdxBranch (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK)))) ch
        = .ok (.retV (.bool (decide ((ixN : Int) ≤ (apl : Int))))
            (.ifK s3IdxBranch (.seqn #[]) env0
              (.seq (nxt :: rest2) env0 KK)), σ, ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.int (apl : Int) .uint64,
          GoValue.int (ixN : Int) .uint64])
        = [GoValue.int (ixN : Int) .uint64,
            GoValue.int (apl : Int) .uint64] from rfl]
      exact applyStrictOp_atMostCmp_int
    exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain q1 q2) q3) q4) q5
  by_cases hfire : ixN ≤ apl
  · -- FIRE
    have hbool : (decide ((ixN : Int) ≤ (apl : Int))) = true := by
      simp only [decide_eq_true_iff]
      omega
    have hdisp : stepFnIter 1 σ
        (.retV (.bool (decide ((ixN : Int) ≤ (apl : Int))))
          (.ifK s3IdxBranch (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK))) ch
        = .ok (.exec s3IdxBranch env0
            (.seq (nxt :: rest2) env0 KK), σ, ch) := by
      rw [hbool]
      with_unfolding_all rfl
    have hbr := s3Branch_walk (env0 := env0)
      (K := .seq (nxt :: rest2) env0 KK)
      "$c2298" "$c2299" "$c2300" idE (.var "idx") appliedE
      (gs [83, 51, 32, 109, 111, 110, 111, 116, 111, 110, 105, 99,
        105, 116, 121, 58, 32, 110, 111, 100, 101, 32])
      (gs [32, 97, 112, 112, 108, 105, 101, 100, 32, 105, 110, 100,
        101, 120, 32])
      (gs [32, 97, 102, 116, 101, 114, 32, 105, 110, 100, 101, 120,
        32])
      (a1 := idvN) (a2 := ixN) (a3 := apl) (k1 := 5) (k2 := 1)
      (k3 := 5)
      hidv hixr hapl (by decide) (by decide) (by decide)
      ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide⟩
      henvT0 henvN0 henvI0 henvR0 σ ch hag hfr
      ⟨htP, hnP, hTw, hNd, hIc, hTc⟩
      (fun σ' env' K' hbr hnd hidx htrm =>
        read_field_seg (henv := hnd) (hp := hbr.2.1)
          (hw := hbr.2.2.2.1) (hf := nodeFs_id))
      (fun σ' env' K' hbr hnd hidx htrm =>
        stepFnIter_one (stepFn_var (henv := hidx)
          (hlook := hbr.2.2.2.2.1)))
      (fun σ' env' K' hbr hnd hidx htrm =>
        read_field_seg (henv := hnd) (hp := hbr.2.1)
          (hw := hbr.2.2.2.1) (hf := nodeFs_applied))
      hc0 hc1 hm0 hm1 hw0 hw1 hq0 hq1
    obtain ⟨mB, hmB, σ', tr', hrunB, hTw', hfrm', hnalo, hnahi,
      hfrs', hag'⟩ := hbr
    have hpop : stepFnIter 1 σ'
        (.next (.seq (nxt :: rest2) env0 KK)) ch
        = .ok (.exec nxt env0 (.seq rest2 env0 KK), σ', ch) :=
      stepFnIter_one stepFn_seq_pop
    refine ⟨10 + 1 + mB + 1, by omega, σ', tr', ?_, ?_, ?_,
      by omega, by omega, hfrs', hag'⟩
    · exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        hguard hdisp) hrunB) hpop
    · rw [if_pos hfire]
      exact hTw'
    · exact hfrm'
  · -- SKIP
    have hbool : (decide ((ixN : Int) ≤ (apl : Int))) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    have hdisp : stepFnIter 1 σ
        (.retV (.bool (decide ((ixN : Int) ≤ (apl : Int))))
          (.ifK s3IdxBranch (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK))) ch
        = .ok (.exec (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK), σ, ch) := by
      rw [hbool]
      with_unfolding_all rfl
    have hdrain : stepFnIter 2 σ
        (.exec (.seqn #[]) env0 (.seq (nxt :: rest2) env0 KK)) ch
        = .ok (.exec nxt env0 (.seq rest2 env0 KK), σ, ch) :=
      stepFnIter_splice_pop (ss := #[]) rfl
    refine ⟨10 + 1 + 2, by omega, σ, tr, ?_, ?_,
      fun x _ _ => rfl, by omega, by omega, hfr, hag⟩
    · exact stepFnIter_chain (stepFnIter_chain hguard hdisp) hdrain
    · rw [if_neg hfire, Int.add_zero]
      exact hTw

/-- **The S3-term guard segment**: evaluate `trm < nd.lastTrm`;
the index guard's mirror. -/
theorem s3term_seg
    (henvT0 : LocalEnv.lookup env0 "t" = some (.base ⟨na₀⟩))
    (henvN0 : LocalEnv.lookup env0 "nd" = some (.base ⟨na₀ + 1⟩))
    (henvI0 : LocalEnv.lookup env0 "idx" = some (.base ⟨na₀ + 3⟩))
    (henvR0 : LocalEnv.lookup env0 "trm" = some (.base ⟨na₀ + 6⟩))
    (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ)
    (hfr : ∀ x, σ.nextAddr ≤ x →
      Heap.lookup σ.heap (.base ⟨x⟩) = none)
    (hBr : BrCells na₀ tw nw
      (twCell nodesV netV liveV lm byV cc cm w pendV drvV sq tr hlV)
      (ndCellN idvN rnV stV tmvN cmvN stvN apl ltm gm)
      ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩
      ⟨some (.int .uint64), .int (tmN : Int) .uint64⟩ σ)
    (hidv : idvN < 2 ^ 64) (htmr : tmN < 2 ^ 64)
    (hltm : ltm < 2 ^ 64)
    (hc0 : -(2 ^ 63) ≤ cc) (hc1 : cc < 2 ^ 63)
    (hm0 : -(2 ^ 63) ≤ cm) (hm1 : cm < 2 ^ 63)
    (hw0 : -(2 ^ 63) ≤ w) (hw1 : w + 1 < 2 ^ 63)
    (hq0 : -(2 ^ 63) ≤ sq) (hq1 : sq < 2 ^ 63) :
    ∃ m ≤ 4900, ∃ σ' : ExecState, ∃ tr' : GoString,
      stepFnIter m σ
          (.exec s3TermIfS env0 (.seq (nxt :: rest2) env0 KK)) ch
        = .ok (.exec nxt env0 (.seq rest2 env0 KK), σ', ch)
      ∧ Heap.lookup σ'.heap (.base ⟨tw⟩)
          = some (twCell nodesV netV liveV lm byV cc cm
              (w + (if tmN < ltm then 1 else 0)) pendV drvV sq
              tr' hlV)
      ∧ (∀ x, x < σ.nextAddr → x ≠ tw →
          Heap.lookup σ'.heap (.base ⟨x⟩)
            = Heap.lookup σ.heap (.base ⟨x⟩))
      ∧ σ.nextAddr ≤ σ'.nextAddr ∧ σ'.nextAddr ≤ σ.nextAddr + 17
      ∧ (∀ x, σ'.nextAddr ≤ x →
          Heap.lookup σ'.heap (.base ⟨x⟩) = none)
      ∧ bfTB.Agrees σ' := by
  obtain ⟨htP, hnP, hTw, hNd, hIc, hTc⟩ := hBr
  -- the guard evaluation (10 steps to the delivered Bool)
  have hguard : stepFnIter 10 σ
      (.exec s3TermIfS env0 (.seq (nxt :: rest2) env0 KK)) ch
      = .ok (.retV (.bool (decide ((tmN : Int) < (ltm : Int))))
          (.ifK s3TermBranch (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK)), σ, ch) := by
    have q1 : stepFnIter 2 σ
        (.exec s3TermIfS env0 (.seq (nxt :: rest2) env0 KK)) ch
        = .ok (.evalE (.var "trm") env0
            (.strictK .lessCmp [] [lastTrmE] env0
              (.ifK s3TermBranch (.seqn #[]) env0
                (.seq (nxt :: rest2) env0 KK))), σ, ch) := by
      with_unfolding_all rfl
    have q2 : stepFnIter 1 σ (.evalE (.var "trm") env0
        (.strictK .lessCmp [] [lastTrmE] env0
          (.ifK s3TermBranch (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK)))) ch
        = .ok (.retV (.int (tmN : Int) .uint64)
            (.strictK .lessCmp [] [lastTrmE] env0
              (.ifK s3TermBranch (.seqn #[]) env0
                (.seq (nxt :: rest2) env0 KK))), σ, ch) :=
      stepFnIter_one (stepFn_var (henv := henvR0) (hlook := hTc))
    have q3 : stepFnIter 1 σ (.retV (.int (tmN : Int) .uint64)
        (.strictK .lessCmp [] [lastTrmE] env0
          (.ifK s3TermBranch (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK)))) ch
        = .ok (.evalE lastTrmE env0
            (.strictK .lessCmp [.int (tmN : Int) .uint64] [] env0
              (.ifK s3TermBranch (.seqn #[]) env0
                (.seq (nxt :: rest2) env0 KK))), σ, ch) := by
      with_unfolding_all rfl
    have q4 : stepFnIter 5 σ (.evalE lastTrmE env0
        (.strictK .lessCmp [.int (tmN : Int) .uint64] [] env0
          (.ifK s3TermBranch (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK)))) ch
        = .ok (.retV (.int (ltm : Int) .uint64)
            (.strictK .lessCmp [.int (tmN : Int) .uint64] [] env0
              (.ifK s3TermBranch (.seqn #[]) env0
                (.seq (nxt :: rest2) env0 KK))), σ, ch) :=
      read_field_seg (henv := henvN0) (hp := hnP) (hw := hNd)
        (hf := nodeFs_lastTrm)
    have q5 : stepFnIter 1 σ (.retV (.int (ltm : Int) .uint64)
        (.strictK .lessCmp [.int (tmN : Int) .uint64] [] env0
          (.ifK s3TermBranch (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK)))) ch
        = .ok (.retV (.bool (decide ((tmN : Int) < (ltm : Int))))
            (.ifK s3TermBranch (.seqn #[]) env0
              (.seq (nxt :: rest2) env0 KK)), σ, ch) := by
      refine stepFnIter_one (stepFn_strict_apply (h := ?_))
      rw [show (List.reverse [GoValue.int (ltm : Int) .uint64,
          GoValue.int (tmN : Int) .uint64])
        = [GoValue.int (tmN : Int) .uint64,
            GoValue.int (ltm : Int) .uint64] from rfl]
      exact applyStrictOp_lessCmp_int'
    exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain q1 q2) q3) q4) q5
  by_cases hfire : tmN < ltm
  · -- FIRE
    have hbool : (decide ((tmN : Int) < (ltm : Int))) = true := by
      simp only [decide_eq_true_iff]
      omega
    have hdisp : stepFnIter 1 σ
        (.retV (.bool (decide ((tmN : Int) < (ltm : Int))))
          (.ifK s3TermBranch (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK))) ch
        = .ok (.exec s3TermBranch env0
            (.seq (nxt :: rest2) env0 KK), σ, ch) := by
      rw [hbool]
      with_unfolding_all rfl
    have hbr := s3Branch_walk (env0 := env0)
      (K := .seq (nxt :: rest2) env0 KK)
      "$c2301" "$c2302" "$c2303" idE (.var "trm") lastTrmE
      (gs [83, 51, 32, 109, 111, 110, 111, 116, 111, 110, 105, 99,
        105, 116, 121, 58, 32, 110, 111, 100, 101, 32])
      (gs [32, 97, 112, 112, 108, 105, 101, 100, 32, 116, 101, 114,
        109, 32])
      (gs [32, 97, 102, 116, 101, 114, 32, 116, 101, 114, 109, 32])
      (a1 := idvN) (a2 := tmN) (a3 := ltm) (k1 := 5) (k2 := 1)
      (k3 := 5)
      hidv htmr hltm (by decide) (by decide) (by decide)
      ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide⟩
      henvT0 henvN0 henvI0 henvR0 σ ch hag hfr
      ⟨htP, hnP, hTw, hNd, hIc, hTc⟩
      (fun σ' env' K' hbr hnd hidx htrm =>
        read_field_seg (henv := hnd) (hp := hbr.2.1)
          (hw := hbr.2.2.2.1) (hf := nodeFs_id))
      (fun σ' env' K' hbr hnd hidx htrm =>
        stepFnIter_one (stepFn_var (henv := htrm)
          (hlook := hbr.2.2.2.2.2)))
      (fun σ' env' K' hbr hnd hidx htrm =>
        read_field_seg (henv := hnd) (hp := hbr.2.1)
          (hw := hbr.2.2.2.1) (hf := nodeFs_lastTrm))
      hc0 hc1 hm0 hm1 hw0 hw1 hq0 hq1
    obtain ⟨mB, hmB, σ', tr', hrunB, hTw', hfrm', hnalo, hnahi,
      hfrs', hag'⟩ := hbr
    have hpop : stepFnIter 1 σ'
        (.next (.seq (nxt :: rest2) env0 KK)) ch
        = .ok (.exec nxt env0 (.seq rest2 env0 KK), σ', ch) :=
      stepFnIter_one stepFn_seq_pop
    refine ⟨10 + 1 + mB + 1, by omega, σ', tr', ?_, ?_, ?_,
      by omega, by omega, hfrs', hag'⟩
    · exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        hguard hdisp) hrunB) hpop
    · rw [if_pos hfire]
      exact hTw'
    · exact hfrm'
  · -- SKIP
    have hbool : (decide ((tmN : Int) < (ltm : Int))) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    have hdisp : stepFnIter 1 σ
        (.retV (.bool (decide ((tmN : Int) < (ltm : Int))))
          (.ifK s3TermBranch (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK))) ch
        = .ok (.exec (.seqn #[]) env0
            (.seq (nxt :: rest2) env0 KK), σ, ch) := by
      rw [hbool]
      with_unfolding_all rfl
    have hdrain : stepFnIter 2 σ
        (.exec (.seqn #[]) env0 (.seq (nxt :: rest2) env0 KK)) ch
        = .ok (.exec nxt env0 (.seq rest2 env0 KK), σ, ch) :=
      stepFnIter_splice_pop (ss := #[]) rfl
    refine ⟨10 + 1 + 2, by omega, σ, tr, ?_, ?_,
      fun x _ _ => rfl, by omega, by omega, hfr, hag⟩
    · exact stepFnIter_chain (stepFnIter_chain hguard hdisp) hdrain
    · rw [if_neg hfire, Int.add_zero]
      exact hTw


end Guards

end GoLean.RaftSeam.SpanS23
