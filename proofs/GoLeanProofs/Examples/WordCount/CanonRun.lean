import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.WordCount.Return

/-!
# WordCount — CanonRun

Per-phase shard of `GoLeanProofs.Examples.WordCount` (examples phase-2
slice 0, lever 2, 2026-08-14). Every statement and proof here is
BYTE-IDENTICAL to the pre-split module; only file placement changed, so
Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.WordCount`; the module docstring there records
the example's design.
-/

namespace GoLean.Examples.WordCount

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The canonical run, end to end -/

theorem countsList_length_le (ws : List Int) :
    (countsList ws).length ≤ ws.length := by
  have hbump : ∀ (kvs : List (Int × Nat)) (w : Int),
      (bump kvs w).length ≤ kvs.length + 1 := by
    intro kvs w
    induction kvs with
    | nil => simp [bump]
    | cons kv rest ih =>
        obtain ⟨k, c⟩ := kv
        by_cases hk : k = w
        · simp [bump, hk]
        · simp only [bump, if_neg hk, List.length_cons]
          omega
  have hfold : ∀ (l : List Int) (kvs : List (Int × Nat)),
      (List.foldl bump kvs l).length ≤ kvs.length + l.length := by
    intro l
    induction l with
    | nil => intro kvs; simp
    | cons w rest ih =>
        intro kvs
        simp only [List.foldl_cons, List.length_cons]
        have h1 := ih (bump kvs w)
        have h2 := hbump kvs w
        omega
  simpa [countsList] using hfold ws []

private theorem maxMult_le_len (ws : List Int) :
    maxMultiplicity ws ≤ ws.length := by
  refine maxMult_le (fun v _ => ?_)
  simp only [multiplicity]
  exact List.length_filter_le _ _

/-- **The canonical run, end to end**: from the canonical seed the
driver completes at the `.normal` terminal within `132 + 108·len`
steps, at EVERY choice stream, with `maxMultiplicity ws` in the
result cell and the input backing untouched. -/
private theorem wc_runs (ws : List Int)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63)
    (ch : Choices) :
    ∃ (k : Nat) (ch' : Choices) (tail : Heap) (na : Nat),
      k ≤ 132 + 108 * ws.length ∧
      stepFnIter k (wcSeed ws 1 [] 2) (.exec (wcCall ws 1) wcEnv .stop) ch
        = .ok (.next .stop,
            σX ws.length ws (countsList ws)
              ((maxMultiplicity ws : Nat) : Int)
              ((maxMultiplicity ws : Nat) : Int) tail na, ch') := by
  have hM : maxMultiplicity ws ≤ ws.length := maxMult_le_len ws
  have hMnorm : IntKind.normalize .uint64 ((maxMultiplicity ws : Nat) : Int)
      = ((maxMultiplicity ws : Nat) : Int) := by
    refine unorm_of_range (by omega) ?_
    have : maxMultiplicity ws < 2 ^ 64 := by omega
    exact_mod_cast this
  -- entry
  have hE1 := wc_entryA_raw ws ch
  rw [inorm_nat_of_lt hlen] at hE1
  have happ : applyStrictOp (wcSeed ws 1 [] 2) (.sliceExpr false)
      [.addr (.base ⟨1⟩), .int 0 .int, .int ((ws.length : Nat) : Int) .int]
      = .ok (sliceH ws.length, wcSeed ws 1 [] 2) :=
    applyStrictOp_sliceExpr_array
      (show Heap.lookup (wcSeed ws 1 [] 2).heap (.base ⟨1⟩)
          = some ⟨some (.array ws.length tU64),
              .array ⟨ws.map (fun v => .int v .uint64)⟩⟩ from rfl)
      (by simp)
  have hE := stepFnIter_chain
    (stepFnIter_chain hE1
      (stepFnIter_one (stepFn_strict_apply
        (done := [.int 0 .int, .addr (.base ⟨1⟩)]) happ)))
    (wc_entryB_raw ws ch)
  -- first dispatch
  have hA0 := wc_segA0_raw ws.length ws [] 0 [] 9 ch
  have hlen_apply : applyStrictOp (σC ws.length ws [] 0 false [] 9)
      (.lengthOf (some (.slice tU64))) [sliceH ws.length]
      = .ok (.int (ws.length : Nat) .int, σC ws.length ws [] 0 false [] 9) :=
    applyStrictOp_len_slice (Nat.le_refl _)
  have hCmp := wc_cmp_raw ws.length ws [] 0 0 [] 9 ch
  have hD := stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hE hA0)
      (stepFnIter_one (stepFn_strict_apply (done := []) hlen_apply)))
    hCmp
  -- the counting loop to the range head
  obtain ⟨k₁, tail₁, hk₁, htail₁, hbest₁, hrun₁⟩ :=
    wc_count_loop ws hws hlen (ws.length - 0) 0 rfl (by omega) [] 9
      (by omega) (fun _ _ => rfl) ch
  have hC := stepFnIter_chain hD hrun₁
  -- the range loop
  obtain ⟨k₂, ch₂, tail₂, na₂, hk₂, hna₂, hbest₂, htail₂, hrun₂⟩ :=
    wc_range_loop ws (countsList ws) (countsList ws).length (countsList ws)
      rfl 0 (9 + 2 * (ws.length - 0)) (9 + 2 * (ws.length - 0) + 1) tail₁
      ch (fun p hp => countsList_val_le ws hp) hlen (by omega) (by omega)
      (by omega) hbest₁ htail₁
  have hR := stepFnIter_chain hC hrun₂
  rw [show max 0 (maxOf ((countsList ws).map Prod.snd))
      = maxMultiplicity ws from by
    rw [Nat.zero_max]
    exact maxOf_countsList ws] at hbest₂
  -- the return path
  have hX1 := wc_segX1_raw ws.length ws (countsList ws) 0 0 tail₂
    (9 + 2 * (ws.length - 0)) na₂ ch₂
  have hX := stepFnIter_chain hR hX1
  have hlkB : Heap.lookup
      (σX ws.length ws (countsList ws) 0 0 tail₂ na₂).heap
      (.base ⟨9 + 2 * (ws.length - 0)⟩)
      = some (u64cell ((maxMultiplicity ws : Nat) : Int)) := by
    show Heap.lookup (frontX ws.length ws (countsList ws) 0 0 ++ tail₂)
      (.base ⟨9 + 2 * (ws.length - 0)⟩)
      = some (u64cell ((maxMultiplicity ws : Nat) : Int))
    rw [lookup_append_right
      (lookup_frontX_none ws.length ws (countsList ws) 0 0 (by omega))]
    exact hbest₂
  have hX2 := stepFnIter_chain hX (stepFnIter_one
    (stepFn_var (x := "best") (env := envRB (9 + 2 * (ws.length - 0)))
      (a := ⟨9 + 2 * (ws.length - 0)⟩) (ch := ch₂) rfl hlkB))
  have hX2a := wc_segX2a_raw ws.length ws (countsList ws) 0 0
    ((maxMultiplicity ws : Nat) : Int) tail₂
    (9 + 2 * (ws.length - 0)) na₂ ch₂
  rw [hMnorm] at hX2a
  have hX3 := stepFnIter_chain hX2 hX2a
  have hX4 := stepFnIter_chain hX3
    (wc_segX2b_raw ws.length ws (countsList ws) 0
      ((maxMultiplicity ws : Nat) : Int) tail₂
      (9 + 2 * (ws.length - 0)) na₂ ch₂)
  have hX2c := wc_segX2c_raw ws.length ws (countsList ws) 0
    ((maxMultiplicity ws : Nat) : Int) tail₂ na₂
    (9 + 2 * (ws.length - 0)) ch₂
  rw [hMnorm] at hX2c
  have hX5 := stepFnIter_chain hX4 hX2c
  refine ⟨_, ch₂, tail₂, na₂, ?_, hX5⟩
  have hm := countsList_length_le ws
  omega

/-- **Total correctness of the `maxCount` run at the canonical
placement** — the SUPPORTING inner-run theorem beneath the harness-form
headline (statement-form ruling 2026-08-13: user-facing headlines
quantify over `GoValue` arguments at the `runFunctionWithContextM`
boundary; this canonical-driver form carries the semantic content — the
∀-choices total run with the order-independent readout — and is what
the shared harness entry-glue consumes). Past fuel `132 + 108·len`,
at EVERY choice stream (every map-iteration order), execution completes
normally with EXACTLY `maxMultiplicity ws` in the result cell and the
input backing untouched. -/
theorem maxCount_total_canonical (ws : List Int)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63) :
    ∀ fuel : Nat, 132 + 108 * ws.length ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel wcEnv (wcSeed ws 1 [] 2) ch (wcCall ws 1)
          = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩)
            = .ok (.int ((maxMultiplicity ws : Nat) : Int) .uint64)
        ∧ Heap.lookup σf.heap (.base ⟨1⟩)
            = some ⟨some (.array ws.length tU64),
                .array ⟨ws.map (fun v => .int v .uint64)⟩⟩ := by
  intro fuel hfuel ch
  obtain ⟨k, ch', tail, na, hk, hrun⟩ := wc_runs ws hws hlen ch
  refine ⟨σX ws.length ws (countsList ws)
    ((maxMultiplicity ws : Nat) : Int) ((maxMultiplicity ws : Nat) : Int)
    tail na, ch', ?_, rfl, rfl⟩
  show execStmtLoop fuel (wcSeed ws 1 [] 2)
    (.exec (wcCall ws 1) wcEnv .stop) ch = _
  have hfold := execStmtLoop_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hfold, execStmtLoop_next_stop]


end GoLean.Examples.WordCount
