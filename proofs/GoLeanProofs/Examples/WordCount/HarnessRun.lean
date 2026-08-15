import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.MapMem
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.MapLoops
import GoLeanProofs.Examples.WordCount.CanonCount
import GoLeanProofs.Examples.WordCount.CanonRun
import GoLeanProofs.Examples.WordCount.Family
import GoLeanProofs.Examples.WordCount.HarnessSetup
import GoLeanProofs.Examples.WordCount.HarnessSubject
import GoLeanProofs.Examples.WordCount.Machine
import GoLeanProofs.Examples.WordCount.Pure
import GoLeanProofs.Examples.WordCount.RangeGeneric
import GoLeanProofs.Examples.Targets

/-!
# WordCount — HarnessRun

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
open GoLean.MapMem
open GoLean.MapLoops

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The harness counting tower — the generic layer's SECOND consumer
(the former storm site closes by instantiation; consolidation slice
2026-08-13) -/

/-! ## The HARNESS placement's discharge lemmas (gap G1's former storm site) (the generic layer's
hypotheses at `S := σH ws.length sv siv ws`; every statement pins the full
transition — the E-form made structural) -/

/- GAP-C1 CLOSED (kit-gap closure, 2026-08-15): the harness
placement's conditioned discharges (`wcH_init1`/`wcH_st1`/`wcH_init2`/
`wcH_st2`/`wcH_lk1`/`wcH_lk2`/`wcH_var1`/`wcH_var2`/`wcH_read`/
`wcH_mapGet`/`wcH_mapAsgn`, ~270 lines) are DELETED — the kit's
`MapLoops.mapCountIter_at` constructs them from nine placement facts,
every one a `rfl` here except `lookup_frontH_none`
(`HarnessSubject`). -/

/-- **One counting iteration** (exit test true at word `i`): the map
data cell advances from the counts of `ws.take i` to those of
`ws.take (i+1)`; two fresh dead cells land at `na`, `na + 1`. 53
steps — via the kit's bundled `MapLoops.mapCountIter_at` (GAP-C1
closure, 2026-08-15). -/
private theorem wcH_count_iter (ws : List Int) (sv siv : Int) (i : Nat)
    (dead : Heap)
    (na : Nat) (ch : Choices)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63)
    (hi : i < ws.length) (hna : 16 ≤ na)
    (hdead : ∀ x : Nat, na ≤ x → Heap.lookup dead (.base ⟨x⟩) = none) :
    stepFnIter 53
      (σH ws.length sv siv ws (countsFold (ws.take i)) (i : Int) false dead na)
      (.retV (.bool true) cmpContCH) ch
      = .ok (headCH,
          σH ws.length sv siv ws (countsFold (ws.take (i + 1))) (i : Int) false
            (dead ++ [(.base ⟨na⟩, mhCellW),
              (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2), ch) := by
  have hw := hws (ws.getD i 0) (getD_mem hi)
  have hcnt : cnt (countsFold (ws.take i)) (ws.getD i 0) + 1 < 2 ^ 64 := by
    have := cnt_take_le (ws := ws) (i := i) (ws.getD i 0)
    omega
  have h := mapCountIter_at "words" (σH ws.length sv siv ws)
    (wcSeed ws 1 [] 2)
    (fun kvs iv => frontH ws.length sv siv ws kvs iv false) ws 4 12 16
    headCH cmpContCH postBodyKH env3H u1EnvH uEnvH
    (fun _ _ _ _ => rfl)
    (fun kvs iv x hx =>
      lookup_frontH_none ws.length sv siv ws kvs iv false hx)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun kvs iv dead na ch => wcH_segC1_raw ws.length sv siv ws kvs iv dead na ch)
    (fun kvs iv dead na₀ na ch =>
      wcH_segC2_raw ws.length sv siv ws kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na ch =>
      wcH_segC3_raw ws.length sv siv ws kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na ch =>
      wcH_segC4_raw ws.length sv siv ws kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na w ch =>
      wcH_segC5_raw ws.length sv siv ws kvs iv dead na₀ na w ch)
    (fun kvs iv dead na₀ na ch =>
      wcH_segC6_raw ws.length sv siv ws kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na ch =>
      wcH_segC7_raw ws.length sv siv ws kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na w ch =>
      wcH_segC8_raw ws.length sv siv ws kvs iv dead na₀ na w ch)
    (fun kvs iv dead na₀ na w ch =>
      wcH_segC9_raw ws.length sv siv ws kvs iv dead na₀ na w ch)
    (fun kvs iv dead na₀ na w cv ch =>
      wcH_segC10_raw ws.length sv siv ws kvs iv dead na₀ na w cv ch)
    (fun kvs iv dead na₀ na ch =>
      wcH_segC11_raw ws.length sv siv ws kvs iv dead na₀ na ch)
    (countsFold (ws.take i)) i dead na ch hi hw.1 hw.2 hcnt hna hdead
  rw [show setk (countsFold (ws.take i)) (ws.getD i 0)
      (cnt (countsFold (ws.take i)) (ws.getD i 0) + 1)
      = countsFold (ws.take (i + 1)) from by
    rw [setk_cnt_succ, ← countsFold_append, ← take_succ_getD hi]] at h
  exact h

private theorem wcH_initBest (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (ch : Choices), 16 ≤ na → DeadFrom dead na →
    stepFn (σH ws.length sv siv ws kvs iv false dead na)
        (.exec (.initialization { id := "best", typ := tU64 }) envR0H
          (.seq [.assign (.var "best") (.intLit 0 .uint64),
            wcMapRangeStmt, retSeqn] envR0H frameKH)) ch
      = .ok (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
            wcMapRangeStmt, retSeqn] (envRBH na) frameKH),
          σH ws.length sv siv ws kvs iv false (dead ++ [(.base ⟨na⟩, u64cell 0)])
            (na + 1), ch) := by
  intro kvs iv dead na ch hna hdead
  have hmiss : Heap.lookup
      (frontH ws.length sv siv ws kvs iv false ++ dead) (.base ⟨na⟩) = none := by
    rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs iv false
      hna)]
    exact hdead na (Nat.le_refl na)
  have h := stepFn_init_seq (σ := σH ws.length sv siv ws kvs iv false dead na)
    (p := { id := "best", typ := tU64 })
    (rest := [.assign (.var "best") (.intLit 0 .uint64),
      wcMapRangeStmt, retSeqn])
    (env := envR0H) (k := frameKH) (ch := ch) (v := .int 0 .uint64)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σH ws.length sv siv ws kvs iv false dead na).nextAddr = na from rfl,
    show (σH ws.length sv siv ws kvs iv false dead na).heap
      = frontH ws.length sv siv ws kvs iv false ++ dead from rfl,
    set_fresh hmiss, List.append_assoc] at h
  exact h

private theorem wcH_stBest (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (ch : Choices), 16 ≤ B → DeadFrom dead B →
    stepFn (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
          [.int 0 .uint64] (.seqn #[]) (envRBH B)
          (.seq [wcMapRangeStmt, retSeqn] (envRBH B) frameKH))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envRBH B)
            (.seq [wcMapRangeStmt, retSeqn] (envRBH B) frameKH)),
          σH ws.length sv siv ws kvs iv false (dead ++ [(.base ⟨B⟩, u64cell 0)]) na,
          ch) := by
  intro kvs iv dead B na ch hB hdead
  have hlook : Heap.lookup
      (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na).heap
      (.base ⟨B⟩) = some ⟨some tU64, .int 0 .uint64⟩ := by
    show Heap.lookup
      (frontH ws.length sv siv ws kvs iv false ++ (dead ++ [(.base ⟨B⟩, u64cell 0)]))
      (.base ⟨B⟩) = some ⟨some tU64, .int 0 .uint64⟩
    rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs iv false hB),
      lookup_append_right (hdead B (Nat.le_refl B))]
    exact lookup_singleton_self
  have h := storeTarget_addr (v := .int 0 .uint64) (v' := .int 0 .uint64)
    hlook
    (by simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel, IntKind.normalize, IntKind.bits?, IntKind.signed])
  rw [show (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na).heap
      = frontH ws.length sv siv ws kvs iv false ++ (dead ++ [(.base ⟨B⟩, u64cell 0)])
      from rfl,
    set_append_right (lookup_frontH_none ws.length sv siv ws kvs iv false hB),
    set_append_right (hdead B (Nat.le_refl B)),
    set_singleton_self] at h
  exact stepFn_store_step h

private theorem wcH_snap (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (ch : Choices),
      (∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
        ∧ IntKind.normalize .uint64 ((p.2 : Nat) : Int)
            = ((p.2 : Nat) : Int)) →
    stepFn (σH ws.length sv siv ws kvs iv false dead na)
        (.retV (.map ⟨some (.base ⟨12⟩)⟩)
          (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRBH B)
            (kRH B))) ch
      = .ok (.next (.mapIterK none (some "c") tU64 tU64 wcRangeBody
            (toEntries kvs) (envRBH B) (kRH B)),
          σH ws.length sv siv ws kvs iv false dead na, ch) := by
  intro kvs iv dead B na ch hkv
  exact stepFn_snapshot (snapshot_toEntries (a := ⟨12⟩) (dty := none) rfl hkv)

/-- **The counting loop**, by strong induction on the remaining word
count: from the exit-test delivery at word `i`, the run reaches the
RANGE HEAD over the snapshot of the full counts, with `best` zeroed at
address `na + 2·(L - i)`, within `84·(L-i) + 23` steps — the kit's
`MapLoops.mapCountLoop_generic` plus this placement's own 23-step exit
tower (GAP-C1 closure, 2026-08-15). -/
private theorem wcH_count_loop (ws : List Int) (sv siv : Int)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63) :
    ∀ (n i : Nat), n = ws.length - i → i ≤ ws.length →
    ∀ (dead : Heap) (na : Nat), 16 ≤ na →
    (∀ x : Nat, na ≤ x → Heap.lookup dead (.base ⟨x⟩) = none) →
    ∀ ch : Choices,
    ∃ (k : Nat) (tail : Heap),
      k ≤ 84 * n + 23
      ∧ (∀ x : Nat, na + 2 * n + 1 ≤ x →
          Heap.lookup tail (.base ⟨x⟩) = none)
      ∧ Heap.lookup tail (.base ⟨na + 2 * n⟩) = some (u64cell 0)
      ∧ stepFnIter k
          (σH ws.length sv siv ws (countsFold (ws.take i)) (i : Int) false dead na)
          (.retV (.bool (decide ((i : Int) < (ws.length : Int)))) cmpContCH)
          ch
        = .ok (rangeHeadH (na + 2 * n) (countsFold ws),
            σH ws.length sv siv ws (countsFold ws) (ws.length : Int) false tail
              (na + 2 * n + 1), ch) := by
  intro n i hn hi dead na hna hdead ch
  obtain ⟨tail₀, htail₀, hrun₀⟩ :=
    mapCountLoop_generic (σH ws.length sv siv ws) ws 4 12 16 headCH
      cmpContCH env2H hlen
      (fun i dead na ch hi hna hdead =>
        wcH_count_iter ws sv siv i dead na ch hws hlen hi hna hdead)
      (fun kvs iv dead na ch =>
        wcH_segA1_raw ws.length sv siv ws kvs iv dead na ch)
      n i hn hi dead na hna hdead ch
  -- the exit tower: 23 steps, `best` allocated at `na + 2·n`
  have hX := wcH_segX0_raw ws.length sv siv ws (countsFold ws)
    ((ws.length : Nat) : Int) tail₀ (na + 2 * n) ch
  have hIB := wcH_initBest ws sv siv (countsFold ws)
    ((ws.length : Nat) : Int) tail₀ (na + 2 * n) ch (by omega) htail₀
  have h1 := stepFnIter_chain hX (stepFnIter_one hIB)
  have hXb := wcH_segX0b_raw ws.length sv siv ws (countsFold ws)
    ((ws.length : Nat) : Int) (tail₀ ++ [(.base ⟨na + 2 * n⟩, u64cell 0)])
    (na + 2 * n) (na + 2 * n + 1) ch
  have h2 := stepFnIter_chain h1 hXb
  have hSB := wcH_stBest ws sv siv (countsFold ws) ((ws.length : Nat) : Int)
    tail₀ (na + 2 * n) (na + 2 * n + 1) ch (by omega) htail₀
  have h3 := stepFnIter_chain h2 (stepFnIter_one hSB)
  have hXc := wcH_segX0c_raw ws.length sv siv ws (countsFold ws)
    ((ws.length : Nat) : Int) (tail₀ ++ [(.base ⟨na + 2 * n⟩, u64cell 0)])
    (na + 2 * n) (na + 2 * n + 1) ch
  have h4 := stepFnIter_chain h3 hXc
  have hSn := wcH_snap ws sv siv (countsFold ws) ((ws.length : Nat) : Int)
    (tail₀ ++ [(.base ⟨na + 2 * n⟩, u64cell 0)]) (na + 2 * n)
    (na + 2 * n + 1) ch (countsFold_norm ws hws hlen)
  have h5 := stepFnIter_chain h4 (stepFnIter_one hSn)
  refine ⟨84 * n + 23, tail₀ ++ [(.base ⟨na + 2 * n⟩, u64cell 0)],
    Nat.le_refl _, ?_, ?_, ?_⟩
  · intro x hx
    exact DeadFrom.push (c := u64cell 0) htail₀ x (by omega)
  · rw [lookup_append_right (htail₀ (na + 2 * n) (Nat.le_refl _))]
    exact lookup_singleton_self
  · exact stepFnIter_chain hrun₀ h5

/-! ### The HARNESS placement's range-loop discharges + wrapper -/

private theorem wcH_pick (ws : List Int) (sv siv : Int) :
    ∀ (kvs rem : List (Int × Nat)) (idx : Nat) (ch ch₂ : Choices)
      (p : Int × Nat) (tail : Heap) (B na : Nat),
      Choices.consume ch rem.length = (idx, ch₂) → idx < rem.length →
      rem[idx]? = some p →
      IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) →
      16 ≤ na → DeadFrom tail na →
      stepFn (σH ws.length sv siv ws kvs (ws.length : Int) false tail na)
          (rangeHeadR envRBH kRH B rem) ch
        = .ok (.exec wcRangeBody (envIterR envRBH B na)
              (iterKR envRBH kRH B (rem.eraseIdx idx)),
            σH ws.length sv siv ws kvs (ws.length : Int) false
              (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
              (na + 1), ch₂) := by
  intro kvs rem idx ch ch₂ p tail B na hcons hidx hp hvnorm hna htail
  have hmiss : Heap.lookup
      (frontH ws.length sv siv ws kvs (ws.length : Int) false ++ tail)
      (.base ⟨na⟩) = none := by
    rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs
      (ws.length : Int) false hna)]
    exact htail na (Nat.le_refl na)
  have hPick := GoLean.MapMem.stepFn_pick_value (v := "c")
    (σ := σH ws.length sv siv ws kvs (ws.length : Int) false tail na)
    (body := wcRangeBody) (env := envRBH B) (k := kRH B)
    hcons hidx hp hvnorm
  rw [show (σH ws.length sv siv ws kvs (ws.length : Int) false tail
        na).nextAddr = na from rfl,
    show (σH ws.length sv siv ws kvs (ws.length : Int) false tail na).heap
      = frontH ws.length sv siv ws kvs (ws.length : Int) false ++ tail
      from rfl,
    set_fresh hmiss, List.append_assoc] at hPick
  exact hPick

private theorem wcH_R4b (ws : List Int) (sv siv : Int) :
    ∀ (kvs rem : List (Int × Nat)) (tail : Heap) (B na₀ na : Nat)
      (ch : Choices),
      stepFnIter 4 (σH ws.length sv siv ws kvs (ws.length : Int) false tail na)
          (.next (.seq [.assign (.var "best") (.var "c")]
            (env4R envRBH B na₀)
            (.seq [] (envIfR envRBH B na₀) (iterKR envRBH kRH B rem)))) ch
        = .ok (.evalE (.var "c") (env4R envRBH B na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
                (.seqn #[]) (env4R envRBH B na₀)
                (storeBestKR envRBH kRH B na₀ rem)),
            σH ws.length sv siv ws kvs (ws.length : Int) false tail na, ch) := by
  intro kvs rem tail B na₀ na ch
  with_unfolding_all rfl

private theorem wcH_varC (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (tail : Heap) (na₀ na : Nat)
      (v : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "c" = some (.base ⟨na₀⟩) →
      16 ≤ na₀ → DeadFrom tail na₀ →
      stepFn (σH ws.length sv siv ws kvs (ws.length : Int) false
          (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]) na)
          (.evalE (.var "c") env k) ch
        = .ok (.retV (.int v .uint64) k,
            σH ws.length sv siv ws kvs (ws.length : Int) false
              (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]) na,
            ch) := by
  intro kvs tail na₀ na v env k ch henv hna hdead
  refine stepFn_var (c := ⟨some tU64, .int v .uint64⟩) henv ?_
  show Heap.lookup
    (frontH ws.length sv siv ws kvs (ws.length : Int) false
      ++ (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]))
    (.base ⟨na₀⟩) = some ⟨some tU64, .int v .uint64⟩
  rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs
      (ws.length : Int) false hna),
    lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
  exact lookup_singleton_self

private theorem wcH_varBest (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (tail : Heap) (B na : Nat)
      (bv : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "best" = some (.base ⟨B⟩) → 16 ≤ B →
      Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      stepFn (σH ws.length sv siv ws kvs (ws.length : Int) false tail na)
          (.evalE (.var "best") env k) ch
        = .ok (.retV (.int bv .uint64) k,
            σH ws.length sv siv ws kvs (ws.length : Int) false tail na, ch) := by
  intro kvs tail B na bv env k ch henv hB hlkB
  refine stepFn_var (c := u64cell bv) henv ?_
  show Heap.lookup
    (frontH ws.length sv siv ws kvs (ws.length : Int) false ++ tail)
    (.base ⟨B⟩) = some (u64cell bv)
  rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs
      (ws.length : Int) false hB)]
  exact hlkB

private theorem wcH_stB (ws : List Int) (sv siv : Int) :
    ∀ (kvs rem : List (Int × Nat)) (tail : Heap) (B na₀ na : Nat)
      (bv v : Int) (ch : Choices),
      16 ≤ B → Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      IntKind.normalize .uint64 v = v →
      stepFn (σH ws.length sv siv ws kvs (ws.length : Int) false tail na)
          (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int v .uint64] (.seqn #[]) (env4R envRBH B na₀)
            (storeBestKR envRBH kRH B na₀ rem))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (env4R envRBH B na₀)
              (storeBestKR envRBH kRH B na₀ rem)),
            σH ws.length sv siv ws kvs (ws.length : Int) false
              (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int v .uint64⟩) na,
            ch) := by
  intro kvs rem tail B na₀ na bv v ch hB hlkB hvn
  have hlook : Heap.lookup
      (σH ws.length sv siv ws kvs (ws.length : Int) false tail na).heap
      (.base ⟨B⟩) = some ⟨some tU64, .int bv .uint64⟩ := by
    show Heap.lookup
      (frontH ws.length sv siv ws kvs (ws.length : Int) false ++ tail)
      (.base ⟨B⟩) = some ⟨some tU64, .int bv .uint64⟩
    rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs
        (ws.length : Int) false hB)]
    exact hlkB
  have h := storeTarget_addr (v := .int v .uint64) (v' := .int v .uint64)
    hlook
    (by
      simp only [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel]
      rw [hvn]
      rfl)
  rw [show (σH ws.length sv siv ws kvs (ws.length : Int) false tail na).heap
      = frontH ws.length sv siv ws kvs (ws.length : Int) false ++ tail from rfl,
    set_append_right (lookup_frontH_none ws.length sv siv ws kvs
      (ws.length : Int) false hB)] at h
  exact stepFn_store_step h

/-- **The range loop, at every choice stream** — INSTANTIATED from the
placement-generic `wcRange_generic` (§10b; consolidation slice
2026-08-13). -/
private theorem wcH_range_loop (ws : List Int) (sv siv : Int)
    (kvs : List (Int × Nat)) :
    ∀ (m : Nat) (rem : List (Int × Nat)), rem.length = m →
    ∀ (bv : Nat) (B na : Nat) (tail : Heap) (ch : Choices),
    (∀ p ∈ rem, p.2 ≤ ws.length) → ws.length < 2 ^ 63 → bv ≤ ws.length →
    16 ≤ B → B < na →
    Heap.lookup tail (.base ⟨B⟩) = some (u64cell (bv : Int)) →
    (∀ x : Nat, na ≤ x → Heap.lookup tail (.base ⟨x⟩) = none) →
    ∃ (k : Nat) (ch' : Choices) (tail' : Heap) (na' : Nat),
      k ≤ 24 * m + 1 ∧ na ≤ na'
      ∧ Heap.lookup tail' (.base ⟨B⟩)
          = some (u64cell ((max bv (maxOf (rem.map Prod.snd)) : Nat) : Int))
      ∧ (∀ x : Nat, na' ≤ x → Heap.lookup tail' (.base ⟨x⟩) = none)
      ∧ stepFnIter k (σH ws.length sv siv ws kvs (ws.length : Int) false tail na)
          (rangeHeadH B rem) ch
        = .ok (.next (kRH B),
            σH ws.length sv siv ws kvs (ws.length : Int) false tail' na', ch') := by
  intro m rem hm bv B na tail ch hrem hlen hbv hB hBna hbest htail
  obtain ⟨k, ch', tail', na', hk, hna', hbest', htail', hrun⟩ :=
    wcRange_generic envRBH kRH (σH ws.length sv siv ws) (ws.length : Int)
      16 ws.length hlen
      (fun B na₀ => rfl)
      (wcH_pick ws sv siv) (wcH_R4b ws sv siv) (wcH_varC ws sv siv) (wcH_varBest ws sv siv)
      (wcH_stB ws sv siv)
      m kvs rem hm bv B na tail ch hrem hbv hB hBna hbest htail
  exact ⟨k, ch', tail', na', hk, hna', hbest', htail', hrun⟩



/-- The harness exit-phase front: harness `$res0` (2), `$c10` (8), the
subject's `$res0` (10) generalized. -/
private def frontXH (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (r2 r8 r10 : Int) : Heap :=
  [(.base ⟨0⟩, u64cell (L : Int)), (.base ⟨1⟩, u64cell sv),
   (.base ⟨2⟩, u64cell r2), (.base ⟨3⟩, wHandleCell L),
   (.base ⟨4⟩, arrCell L ws), (.base ⟨5⟩, wHandleCell L),
   (.base ⟨6⟩, u64cell siv), (.base ⟨7⟩, bcell false),
   (.base ⟨8⟩, u64cell r8), (.base ⟨9⟩, wHandleCell L),
   (.base ⟨10⟩, u64cell r10), (.base ⟨11⟩, mhCellW),
   (.base ⟨12⟩, mdCell kvs), (.base ⟨13⟩, mhCellW),
   (.base ⟨14⟩, intcell ((L : Nat) : Int)), (.base ⟨15⟩, bcell false)]

def σXH (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (r2 r8 r10 : Int) (tail : Heap)
    (na : Nat) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := frontXH L sv siv ws kvs r2 r8 r10 ++ tail, nextAddr := na }

/-- X1H: loop exit → the `best` read of `$res0 := best`. 6 steps. -/
private theorem wcH_segX1_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (r2 r8 r10 : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 6 (σXH L sv siv ws kvs r2 r8 r10 tail na) (.next (kRH B)) ch
      = .ok (.evalE (.var "best") (envRBH B)
            (.rhsK .vals [.chain (.addr (.base ⟨10⟩)) [] []] [] []
              (.seqn #[]) (envRBH B)
              (.seq [.returnStmt] (envRBH B) frameKH)),
          σXH L sv siv ws kvs r2 r8 r10 tail na, ch) := by
  have h1 : stepFnIter 1 (σXH L sv siv ws kvs r2 r8 r10 tail na)
      (.next (kRH B)) ch
      = .ok (.exec retSeqn (envRBH B) (.seq [] (envRBH B) frameKH),
          σXH L sv siv ws kvs r2 r8 r10 tail na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σXH L sv siv ws kvs r2 r8 r10 tail na)
    (ss := #[.assign (.var "$res0") (.var "best"), .returnStmt])
    (env := envRBH B) (rest := []) (k := frameKH) (ch := ch))
  have h3 : stepFnIter 4 (σXH L sv siv ws kvs r2 r8 r10 tail na)
      (.next (.seq
        ((#[.assign (.var "$res0") (.var "best"),
          .returnStmt] : Array Stmt).toList ++ [])
        (envRBH B) frameKH)) ch
      = .ok (.evalE (.var "best") (envRBH B)
            (.rhsK .vals [.chain (.addr (.base ⟨10⟩)) [] []] [] []
              (.seqn #[]) (envRBH B)
              (.seq [.returnStmt] (envRBH B) frameKH)),
          σXH L sv siv ws kvs r2 r8 r10 tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- X2aH: the `best` value delivered → stored into the subject's
`$res0` (cell 10). 2 steps. -/
private theorem wcH_segX2a_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (r2 r8 r10 bvv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 2 (σXH L sv siv ws kvs r2 r8 r10 tail na)
      (.retV (.int bvv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨10⟩)) [] []] [] [] (.seqn #[])
          (envRBH B) (.seq [.returnStmt] (envRBH B) frameKH))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envRBH B)
            (.seq [.returnStmt] (envRBH B) frameKH)),
          σXH L sv siv ws kvs r2 r8 (IntKind.normalize .uint64 bvv) tail na,
          ch) := by
  with_unfolding_all rfl

/-- X2bH: → the `returnStmt` dispatch point. 2 steps. -/
private theorem wcH_segX2b_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (r2 r8 r10 : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 2 (σXH L sv siv ws kvs r2 r8 r10 tail na)
      (.next (.storeK [] [] (.seqn #[]) (envRBH B)
        (.seq [.returnStmt] (envRBH B) frameKH))) ch
      = .ok (.next (.seq
            (((#[] : Array Stmt).toList) ++ [.returnStmt]) (envRBH B)
            frameKH),
          σXH L sv siv ws kvs r2 r8 r10 tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σXH L sv siv ws kvs r2 r8 r10 tail na) (body := .seqn #[])
    (env := envRBH B)
    (k := .seq [.returnStmt] (envRBH B) frameKH) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σXH L sv siv ws kvs r2 r8 r10 tail na) (ss := #[])
    (env := envRBH B)
    (rest := [.returnStmt]) (k := frameKH) (ch := ch))
  exact stepFnIter_chain h1 h2

/-- X2cH: `return`, the subject frame's result read + `$c10`
write-back, the harness tail `$res0 := $c10; return`, the harness
frame exit → the driver terminal. 24 steps. -/
private theorem wcH_segX2c_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (r2 r8 r10 : Int) (tail : Heap) (na : Nat)
    (B : Nat) (ch : Choices) :
    stepFnIter 24 (σXH L sv siv ws kvs r2 r8 r10 tail na)
      (.next (.seq (((#[] : Array Stmt).toList) ++ [.returnStmt])
        (envRBH B) frameKH)) ch
      = .ok (.next .stop,
          σXH L sv siv ws kvs
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 r10))
            (IntKind.normalize .uint64 r10) r10 tail na, ch) := by
  with_unfolding_all rfl

private theorem lookup_frontXH_none (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (r2 r8 r10 : Int) {x : Nat} (hx : 16 ≤ x) :
    Heap.lookup (frontXH L sv siv ws kvs r2 r8 r10) (.base ⟨x⟩) = none := by
  simp only [frontXH, Heap.lookup,
    base_beq_false (by omega : (0 : Nat) ≠ x),
    base_beq_false (by omega : (1 : Nat) ≠ x),
    base_beq_false (by omega : (2 : Nat) ≠ x),
    base_beq_false (by omega : (3 : Nat) ≠ x),
    base_beq_false (by omega : (4 : Nat) ≠ x),
    base_beq_false (by omega : (5 : Nat) ≠ x),
    base_beq_false (by omega : (6 : Nat) ≠ x),
    base_beq_false (by omega : (7 : Nat) ≠ x),
    base_beq_false (by omega : (8 : Nat) ≠ x),
    base_beq_false (by omega : (9 : Nat) ≠ x),
    base_beq_false (by omega : (10 : Nat) ≠ x),
    base_beq_false (by omega : (11 : Nat) ≠ x),
    base_beq_false (by omega : (12 : Nat) ≠ x),
    base_beq_false (by omega : (13 : Nat) ≠ x),
    base_beq_false (by omega : (14 : Nat) ≠ x),
    base_beq_false (by omega : (15 : Nat) ≠ x),
    Bool.false_eq_true, if_false]

/-- **The harness run, end to end** (gap G1's composition): from the
machine entry's post-prelude state, through setup, the subject's
counting and range phases, and the harness return path, to the driver
terminal — with `⌈n/3⌉` in the harness result cell. -/
theorem wcH_runs (n seed : Nat) (hn : n < 2 ^ 63) (ch : Choices) :
    ∃ (k : Nat) (ch' : Choices) (tail : Heap) (na : Nat),
      k ≤ 229 + 165 * n ∧
      stepFnIter k (σWH0 ((n : Nat) : Int) ((seed : Nat) : Int))
          (.exec wordcountHarnessFunc.body [hWScope0] hWFrame0) ch
        = .ok (.next .stop,
            σXH n ((seed : Nat) : Int) ((n : Nat) : Int)
              (wcFamily n seed) (countsFold (wcFamily n seed))
              (((n + 2) / 3 : Nat) : Int) (((n + 2) / 3 : Nat) : Int)
              (((n + 2) / 3 : Nat) : Int) tail na, ch') := by
  have hws := wcFamily_range n seed
  have hLen : (wcFamily n seed).length = n := wcFamily_length n seed
  have hlen : (wcFamily n seed).length < 2 ^ 63 := by omega
  have hM : maxMultiplicity (wcFamily n seed) = (n + 2) / 3 :=
    wcFamily_maxMult n seed
  have hMle : (n + 2) / 3 ≤ n ∨ n = 0 := by omega
  have hMlt : (n + 2) / 3 < 2 ^ 64 := by omega
  have hMnorm : IntKind.normalize .uint64 (((n + 2) / 3 : Nat) : Int)
      = (((n + 2) / 3 : Nat) : Int) := by
    refine unorm_of_range (by omega) ?_
    exact_mod_cast hMlt
  -- entry: E1 → makeSlice → E2
  have hE := stepFnIter_chain
    (stepFnIter_chain (wcH_E1_raw n seed ch)
      (stepFnIter_one (wcH_makeSlice n seed ch)))
    (wcH_E2_raw n seed ch)
  -- setup: first dispatch, the fill loop, the exit
  have hA0 := wcH_suA0_raw n ((seed : Nat) : Int) 0
    (List.replicate n 0) ch
  have hSU := wcH_setup_loop n seed hn (n - 0) 0 rfl (by omega) ch
  have hS1 := stepFnIter_chain (stepFnIter_chain hE hA0) hSU
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hS1
  have hX := wcH_X_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
    (wcFamily n seed) ch
  have hS2 := stepFnIter_chain hS1 hX
  have hES := wcH_entryS_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
    (wcFamily n seed) ch
  have hS3 := stepFnIter_chain hS2 hES
  -- the subject's first dispatch to the exit-test delivery
  have hA0c := wcH_segA0_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
    (wcFamily n seed) [] 0 [] 16 ch
  have hlenap := stepFnIter_one
    (stepFn_strict_apply (done := []) (env := env2H)
      (k := .strictK .lessCmp [.int (0 : Int) .int] [] env2H cmpContCH)
      (ch := ch)
      (applyStrictOp_len_slice
        (σ := σH n ((seed : Nat) : Int) ((n : Nat) : Int)
          (wcFamily n seed) [] 0 false [] 16)
        (b := .base ⟨4⟩) (off := 0) (len := n) (cap := n) (elem := tU64)
        (Nat.le_refl n)))
  have hCmp := wcH_cmp_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
    (wcFamily n seed) [] 0 0 [] 16 ch
  have hS4 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hS3 hA0c)
    hlenap) hCmp
  -- the counting loop (instantiated at ws := wcFamily n seed, then the
  -- length rewritten to n)
  obtain ⟨k₁, tail₁, hk₁, htail₁, hbest₁, hrun₁⟩ :=
    wcH_count_loop (wcFamily n seed) ((seed : Nat) : Int) ((n : Nat) : Int)
      hws hlen ((wcFamily n seed).length - 0) 0 rfl (by omega) [] 16
      (by omega) (fun _ _ => rfl) ch
  rw [hLen] at hrun₁ hbest₁ htail₁ hk₁
  have hS5 := stepFnIter_chain hS4 hrun₁
  -- the range loop
  obtain ⟨k₂, ch₂, tail₂, na₂, hk₂, hna₂, hbest₂, htail₂, hrun₂⟩ :=
    wcH_range_loop (wcFamily n seed) ((seed : Nat) : Int) ((n : Nat) : Int)
      (countsFold (wcFamily n seed)) (countsFold (wcFamily n seed)).length
      (countsFold (wcFamily n seed)) rfl 0 (16 + 2 * (n - 0))
      (16 + 2 * (n - 0) + 1) tail₁ ch
      (fun p hp => by
        have := countsFold_val_le (wcFamily n seed) hp
        omega)
      hlen (by omega) (by omega) (by omega) hbest₁ htail₁
  rw [hLen] at hrun₂
  have hS6 := stepFnIter_chain hS5 hrun₂
  rw [show max 0 (maxOf ((countsFold (wcFamily n seed)).map Prod.snd))
      = (n + 2) / 3 from by
    rw [Nat.zero_max, maxOf_countsFold (wcFamily n seed), hM]] at hbest₂
  -- the return path
  have hX1 := wcH_segX1_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
    (wcFamily n seed) (countsFold (wcFamily n seed)) 0 0 0 tail₂
    (16 + 2 * (n - 0)) na₂ ch₂
  have hS7 := stepFnIter_chain hS6 hX1
  have hlkB : Heap.lookup
      (σXH n ((seed : Nat) : Int) ((n : Nat) : Int) (wcFamily n seed)
        (countsFold (wcFamily n seed)) 0 0 0 tail₂ na₂).heap
      (.base ⟨16 + 2 * (n - 0)⟩)
      = some (u64cell (((n + 2) / 3 : Nat) : Int)) := by
    show Heap.lookup
      (frontXH n ((seed : Nat) : Int) ((n : Nat) : Int) (wcFamily n seed)
        (countsFold (wcFamily n seed)) 0 0 0 ++ tail₂)
      (.base ⟨16 + 2 * (n - 0)⟩)
      = some (u64cell (((n + 2) / 3 : Nat) : Int))
    rw [lookup_append_right
      (lookup_frontXH_none n ((seed : Nat) : Int) ((n : Nat) : Int)
        (wcFamily n seed) (countsFold (wcFamily n seed)) 0 0 0 (by omega))]
    exact hbest₂
  have hS8 := stepFnIter_chain hS7 (stepFnIter_one
    (stepFn_var (x := "best") (env := envRBH (16 + 2 * (n - 0)))
      (a := ⟨16 + 2 * (n - 0)⟩) (ch := ch₂) rfl hlkB))
  have hX2a := wcH_segX2a_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
    (wcFamily n seed) (countsFold (wcFamily n seed)) 0 0 0
    (((n + 2) / 3 : Nat) : Int) tail₂ (16 + 2 * (n - 0)) na₂ ch₂
  rw [hMnorm] at hX2a
  have hS9 := stepFnIter_chain hS8 hX2a
  have hS10 := stepFnIter_chain hS9
    (wcH_segX2b_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
      (wcFamily n seed) (countsFold (wcFamily n seed)) 0 0
      (((n + 2) / 3 : Nat) : Int) tail₂ (16 + 2 * (n - 0)) na₂ ch₂)
  have hX2c := wcH_segX2c_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
    (wcFamily n seed) (countsFold (wcFamily n seed)) 0 0
    (((n + 2) / 3 : Nat) : Int) tail₂ na₂ (16 + 2 * (n - 0)) ch₂
  rw [hMnorm, hMnorm] at hX2c
  have hS11 := stepFnIter_chain hS10 hX2c
  refine ⟨_, ch₂, tail₂, na₂, ?_, hS11⟩
  have hm : (countsFold (wcFamily n seed)).length ≤ n := by
    have := countsFold_length_le (wcFamily n seed)
    omega
  omega

end GoLean.Examples.WordCount
