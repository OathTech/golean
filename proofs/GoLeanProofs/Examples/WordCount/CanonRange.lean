import GoLeanProofs.MapMem
import GoLeanProofs.StepKit
import GoLeanProofs.Examples.WordCount.RangeGeneric

/-!
# WordCount — CanonRange

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

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false



/-! ### The canonical placement's range-loop discharges + wrapper -/

private theorem wcC_pick (ws : List Int) :
    ∀ (kvs rem : List (Int × Nat)) (idx : Nat) (ch ch₂ : Choices)
      (p : Int × Nat) (tail : Heap) (B na : Nat),
      Choices.consume ch rem.length = (idx, ch₂) → idx < rem.length →
      rem[idx]? = some p →
      IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) →
      9 ≤ na → DeadFrom tail na →
      stepFn (σC ws.length ws kvs (ws.length : Int) false tail na)
          (rangeHeadR envRB kR B rem) ch
        = .ok (.exec wcRangeBody (envIterR envRB B na)
              (iterKR envRB kR B (rem.eraseIdx idx)),
            σC ws.length ws kvs (ws.length : Int) false
              (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
              (na + 1), ch₂) := by
  intro kvs rem idx ch ch₂ p tail B na hcons hidx hp hvnorm hna htail
  have hmiss : Heap.lookup
      (frontC ws.length ws kvs (ws.length : Int) false ++ tail)
      (.base ⟨na⟩) = none := by
    rw [lookup_append_right (lookup_frontC_none ws.length ws kvs
      (ws.length : Int) false hna)]
    exact htail na (Nat.le_refl na)
  have hPick := GoLean.MapMem.stepFn_pick_value (v := "c")
    (σ := σC ws.length ws kvs (ws.length : Int) false tail na)
    (body := wcRangeBody) (env := envRB B) (k := kR B)
    hcons hidx hp hvnorm
  rw [show (σC ws.length ws kvs (ws.length : Int) false tail
        na).nextAddr = na from rfl,
    show (σC ws.length ws kvs (ws.length : Int) false tail na).heap
      = frontC ws.length ws kvs (ws.length : Int) false ++ tail
      from rfl,
    set_fresh hmiss, List.append_assoc] at hPick
  exact hPick

private theorem wcC_R4b (ws : List Int) :
    ∀ (kvs rem : List (Int × Nat)) (tail : Heap) (B na₀ na : Nat)
      (ch : Choices),
      stepFnIter 4 (σC ws.length ws kvs (ws.length : Int) false tail na)
          (.next (.seq [.assign (.var "best") (.var "c")]
            (env4R envRB B na₀)
            (.seq [] (envIfR envRB B na₀) (iterKR envRB kR B rem)))) ch
        = .ok (.evalE (.var "c") (env4R envRB B na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
                (.seqn #[]) (env4R envRB B na₀)
                (storeBestKR envRB kR B na₀ rem)),
            σC ws.length ws kvs (ws.length : Int) false tail na, ch) := by
  intro kvs rem tail B na₀ na ch
  with_unfolding_all rfl

private theorem wcC_varC (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (tail : Heap) (na₀ na : Nat)
      (v : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "c" = some (.base ⟨na₀⟩) →
      9 ≤ na₀ → DeadFrom tail na₀ →
      stepFn (σC ws.length ws kvs (ws.length : Int) false
          (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]) na)
          (.evalE (.var "c") env k) ch
        = .ok (.retV (.int v .uint64) k,
            σC ws.length ws kvs (ws.length : Int) false
              (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]) na,
            ch) := by
  intro kvs tail na₀ na v env k ch henv hna hdead
  refine stepFn_var (c := ⟨some tU64, .int v .uint64⟩) henv ?_
  show Heap.lookup
    (frontC ws.length ws kvs (ws.length : Int) false
      ++ (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]))
    (.base ⟨na₀⟩) = some ⟨some tU64, .int v .uint64⟩
  rw [lookup_append_right (lookup_frontC_none ws.length ws kvs
      (ws.length : Int) false hna),
    lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
  exact lookup_singleton_self

private theorem wcC_varBest (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (tail : Heap) (B na : Nat)
      (bv : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "best" = some (.base ⟨B⟩) → 9 ≤ B →
      Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      stepFn (σC ws.length ws kvs (ws.length : Int) false tail na)
          (.evalE (.var "best") env k) ch
        = .ok (.retV (.int bv .uint64) k,
            σC ws.length ws kvs (ws.length : Int) false tail na, ch) := by
  intro kvs tail B na bv env k ch henv hB hlkB
  refine stepFn_var (c := u64cell bv) henv ?_
  show Heap.lookup
    (frontC ws.length ws kvs (ws.length : Int) false ++ tail)
    (.base ⟨B⟩) = some (u64cell bv)
  rw [lookup_append_right (lookup_frontC_none ws.length ws kvs
      (ws.length : Int) false hB)]
  exact hlkB

private theorem wcC_stB (ws : List Int) :
    ∀ (kvs rem : List (Int × Nat)) (tail : Heap) (B na₀ na : Nat)
      (bv v : Int) (ch : Choices),
      9 ≤ B → Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      IntKind.normalize .uint64 v = v →
      stepFn (σC ws.length ws kvs (ws.length : Int) false tail na)
          (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int v .uint64] (.seqn #[]) (env4R envRB B na₀)
            (storeBestKR envRB kR B na₀ rem))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (env4R envRB B na₀)
              (storeBestKR envRB kR B na₀ rem)),
            σC ws.length ws kvs (ws.length : Int) false
              (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int v .uint64⟩) na,
            ch) := by
  intro kvs rem tail B na₀ na bv v ch hB hlkB hvn
  have hlook : Heap.lookup
      (σC ws.length ws kvs (ws.length : Int) false tail na).heap
      (.base ⟨B⟩) = some ⟨some tU64, .int bv .uint64⟩ := by
    show Heap.lookup
      (frontC ws.length ws kvs (ws.length : Int) false ++ tail)
      (.base ⟨B⟩) = some ⟨some tU64, .int bv .uint64⟩
    rw [lookup_append_right (lookup_frontC_none ws.length ws kvs
        (ws.length : Int) false hB)]
    exact hlkB
  have h := storeTarget_addr (v := .int v .uint64) (v' := .int v .uint64)
    hlook
    (by
      simp only [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel]
      rw [hvn]
      rfl)
  rw [show (σC ws.length ws kvs (ws.length : Int) false tail na).heap
      = frontC ws.length ws kvs (ws.length : Int) false ++ tail from rfl,
    set_append_right (lookup_frontC_none ws.length ws kvs
      (ws.length : Int) false hB)] at h
  exact stepFn_store_step h

/-- **The range loop, at every choice stream** — INSTANTIATED from the
placement-generic `wcRange_generic` (§10b; consolidation slice
2026-08-13). -/
theorem wc_range_loop (ws : List Int) (kvs : List (Int × Nat)) :
    ∀ (m : Nat) (rem : List (Int × Nat)), rem.length = m →
    ∀ (bv : Nat) (B na : Nat) (tail : Heap) (ch : Choices),
    (∀ p ∈ rem, p.2 ≤ ws.length) → ws.length < 2 ^ 63 → bv ≤ ws.length →
    9 ≤ B → B < na →
    Heap.lookup tail (.base ⟨B⟩) = some (u64cell (bv : Int)) →
    (∀ x : Nat, na ≤ x → Heap.lookup tail (.base ⟨x⟩) = none) →
    ∃ (k : Nat) (ch' : Choices) (tail' : Heap) (na' : Nat),
      k ≤ 24 * m + 1 ∧ na ≤ na'
      ∧ Heap.lookup tail' (.base ⟨B⟩)
          = some (u64cell ((max bv (maxOf (rem.map Prod.snd)) : Nat) : Int))
      ∧ (∀ x : Nat, na' ≤ x → Heap.lookup tail' (.base ⟨x⟩) = none)
      ∧ stepFnIter k (σC ws.length ws kvs (ws.length : Int) false tail na)
          (rangeHead B rem) ch
        = .ok (.next (kR B),
            σC ws.length ws kvs (ws.length : Int) false tail' na', ch') := by
  intro m rem hm bv B na tail ch hrem hlen hbv hB hBna hbest htail
  obtain ⟨k, ch', tail', na', hk, hna', hbest', htail', hrun⟩ :=
    wcRange_generic envRB kR (σC ws.length ws) (ws.length : Int) 9
      ws.length hlen
      (fun B na₀ => rfl)
      (wcC_pick ws) (wcC_R4b ws) (wcC_varC ws) (wcC_varBest ws)
      (wcC_stB ws)
      m kvs rem hm bv B na tail ch hrem hbv hB hBna hbest htail
  exact ⟨k, ch', tail', na', hk, hna', hbest', htail', hrun⟩



end GoLean.Examples.WordCount
