import GoLeanProofs.Examples.WordFreq.Count

/-!
# WordFreq — Range

The `for _, c := range counts` phase: the `best := 0` head, the map
snapshot, the §10b choice-pick loop with the max-fold carried as the
CONSERVATION invariant (`max best (maxOf remaining) = const`), ending
at the result-store seam `.next (rKRes a nb)`.

-- GAP-WITNESS: key-generic MapMem (string keys; promotion
-- candidate) — the pick step is `stepFn_pickW_value` (Count.lean's
-- string-key re-derivation of `MapMem.stepFn_pick_value`), and the
-- loop induction is `mapPickLoopW` (the kit's `mapPickLoop_generic`
-- one key type over). The body segments mirror
-- `WordCount.RangeGeneric`'s at `(.string, uint64)` range types.
-/

namespace GoLean.Examples.WordFreq

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.MapMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

/-! ## The range vocabulary -/

/-- The subject scope once `best` is declared (cell `nb`). -/
def rScope (a nb : Nat) : Scope := ("best", .base ⟨nb⟩) :: cScopeC a
def rEnv (a nb : Nat) : LocalEnv := [rScope a nb, wfFrameScope]
/-- The result-store seam: everything after the range statement. -/
def rKRes (a nb : Nat) : Cont := .seq [wfResSeqn] (rEnv a nb) wfFrameK
/-- The pick point at snapshot remainder `rem`. -/
def rIterK (a nb : Nat) (rem : List (List UInt8 × Nat)) : Cont :=
  .mapIterK none (some "c") tStr tU64 wordFreqFunc.wfRangeBody
    (toEntriesW rem) (rEnv a nb) (rKRes a nb)
/-- The range head configuration. -/
def rHead (a nb : Nat) (rem : List (List UInt8 × Nat)) : Config :=
  .next (rIterK a nb rem)
/-- The iteration env: `c` at the pick cell. -/
def rEnvIter (a nb nc : Nat) : LocalEnv :=
  [("c", .base ⟨nc⟩)] :: rEnv a nb
def rEnvIf (a nb nc : Nat) : LocalEnv := [] :: rEnvIter a nb nc
/-- The body's then-arm. -/
abbrev rThenBlk : Stmt :=
  .block #[] #[.seqn #[.assign (.var "best") (.var "c")]]
def rIfK (a nb nc : Nat) (rem : List (List UInt8 × Nat)) : Cont :=
  .ifK rThenBlk (.seqn #[]) (rEnvIf a nb nc)
    (.seq [] (rEnvIf a nb nc) (rIterK a nb rem))
def rEnv4 (a nb nc : Nat) : LocalEnv := [] :: rEnvIf a nb nc
def rStoreBestK (a nb nc : Nat) (rem : List (List UInt8 × Nat)) :
    Cont :=
  .seq [] (rEnv4 a nb nc)
    (.seq [] (rEnvIf a nb nc) (rIterK a nb rem))

/-! ## The σ-abstract body segments (no heap touch — the state rides) -/

section RangeSegs

variable (σR : ExecState) (rem : List (List UInt8 × Nat))
  (a nb nc : Nat) (ch : Choices)

/-- R1: body entry → the `c` read of the comparison. 4 steps. -/
theorem rg_R1 :
    stepFnIter 4 σR
      (.exec wordFreqFunc.wfRangeBody (rEnvIter a nb nc)
        (rIterK a nb rem)) ch
      = .ok (.evalE (.var "c") (rEnvIf a nb nc)
            (.strictK .greaterCmp [] [.var "best"] (rEnvIf a nb nc)
              (rIfK a nb nc rem)),
          σR, ch) := by
  with_unfolding_all rfl

/-- R2: `c` delivered → the `best` read. 1 step. -/
theorem rg_R2 (cv : GoValue) :
    stepFnIter 1 σR
      (.retV cv
        (.strictK .greaterCmp [] [.var "best"] (rEnvIf a nb nc)
          (rIfK a nb nc rem))) ch
      = .ok (.evalE (.var "best") (rEnvIf a nb nc)
            (.strictK .greaterCmp [cv] [] (rEnvIf a nb nc)
              (rIfK a nb nc rem)),
          σR, ch) := by
  with_unfolding_all rfl

/-- R3: `best` delivered → the `>` apply. 1 step. -/
theorem rg_R3 (cv bv : Int) :
    stepFnIter 1 σR
      (.retV (.int bv .uint64)
        (.strictK .greaterCmp [.int cv .uint64] [] (rEnvIf a nb nc)
          (rIfK a nb nc rem))) ch
      = .ok (.retV (.bool (decide (bv < cv))) (rIfK a nb nc rem),
          σR, ch) := by
  with_unfolding_all rfl

/-- R4a (then): comparison true → the inner store seqn's exec point.
3 steps. -/
theorem rg_R4a :
    stepFnIter 3 σR (.retV (.bool true) (rIfK a nb nc rem)) ch
      = .ok (.exec (.seqn #[.assign (.var "best") (.var "c")])
            (rEnv4 a nb nc)
            (.seq [] (rEnv4 a nb nc)
              (.seq [] (rEnvIf a nb nc) (rIterK a nb rem))),
          σR, ch) := by
  with_unfolding_all rfl

/-- R4c: the store value banks. 1 step. -/
theorem rg_R4c (cv : GoValue) :
    stepFnIter 1 σR
      (.retV cv
        (.rhsK .vals [.chain (.addr (.base ⟨nb⟩)) [] []] [] []
          (.seqn #[]) (rEnv4 a nb nc) (rStoreBestK a nb nc rem))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨nb⟩)) [] []] [cv]
            (.seqn #[]) (rEnv4 a nb nc) (rStoreBestK a nb nc rem)),
          σR, ch) := by
  with_unfolding_all rfl

/-- R5: `best` stored → the next pick point. 4 steps. -/
theorem rg_R5 :
    stepFnIter 4 σR
      (.next (.storeK [] [] (.seqn #[]) (rEnv4 a nb nc)
        (rStoreBestK a nb nc rem))) ch
      = .ok (rHead a nb rem, σR, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil (σ := σR)
    (body := .seqn #[]) (env := rEnv4 a nb nc)
    (k := rStoreBestK a nb nc rem) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := σR)
    (ss := #[]) (env := rEnv4 a nb nc) (rest := [])
    (k := .seq [] (rEnvIf a nb nc) (rIterK a nb rem)) (ch := ch))
  have h3 : stepFnIter 2 σR
      (.next (.seq ((#[] : Array Stmt).toList ++ []) (rEnv4 a nb nc)
        (.seq [] (rEnvIf a nb nc) (rIterK a nb rem)))) ch
      = .ok (rHead a nb rem, σR, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- R4e (else): comparison false → the next pick point. 3 steps. -/
theorem rg_R4e :
    stepFnIter 3 σR (.retV (.bool false) (rIfK a nb nc rem)) ch
      = .ok (rHead a nb rem, σR, ch) := by
  have h1 : stepFnIter 1 σR
      (.retV (.bool false) (rIfK a nb nc rem)) ch
      = .ok (.exec (.seqn #[]) (rEnvIf a nb nc)
            (.seq [] (rEnvIf a nb nc) (rIterK a nb rem)),
          σR, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice (σ := σR)
    (ss := #[]) (env := rEnvIf a nb nc) (rest := [])
    (k := rIterK a nb rem) (ch := ch))
  have h3 : stepFnIter 1 σR
      (.next (.seq ((#[] : Array Stmt).toList ++ []) (rEnvIf a nb nc)
        (rIterK a nb rem))) ch
      = .ok (rHead a nb rem, σR, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- The empty-snapshot drain: the loop exits to the result seam. 1
step. -/
theorem rg_exit :
    stepFnIter 1 σR (rHead a nb []) ch
      = .ok (.next (rKRes a nb), σR, ch) := by
  with_unfolding_all rfl

end RangeSegs

/-! ## The pick, the iteration, the loop -/

section RangeLoop

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
  (biv : Int) (b k cap : Nat) (iv0 sv2 : Int) (D : Heap) (a : Nat)
  (kvs : List (List UInt8 × Nat)) (civ : Int)

/-- The choice-pick at this placement: one choice consumed, the picked
VALUE cell allocated at `na`, one snapshot entry erased. -/
theorem rg_pick (rem : List (List UInt8 × Nat)) (idx : Nat)
    (p : List UInt8 × Nat) (ch ch₂ : Choices) (nb : Nat) (tail : Heap)
    (na : Nat)
    (hcons : Choices.consume ch rem.length = (idx, ch₂))
    (hidx : idx < rem.length) (hp : rem[idx]? = some p)
    (hvnorm : IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int))
    (ha : 31 ≤ a) (hD : DeadFrom D a) (htail : DeadFrom tail na)
    (hna : a + 5 ≤ na) :
    stepFn
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false tail na)
      (rHead a nb rem) ch
      = .ok (.exec wordFreqFunc.wfRangeBody (rEnvIter a nb na)
            (rIterK a nb (rem.eraseIdx idx)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false (tail ++ [(Loc.base ⟨na⟩, su64 ((p.2 : Nat) : Int))])
            (na + 1), ch₂) := by
  have h := stepFn_pickW_value
    (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
      false tail na)
    (rem := rem) (idx := idx) (ch := ch) (ch' := ch₂) (v := "c")
    (body := wordFreqFunc.wfRangeBody) (env := rEnv a nb)
    (k := rKRes a nb) (p := p) hcons hidx hp hvnorm
  rw [show Heap.set
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false tail na).heap
      (.base ⟨(cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        civ false tail na).nextAddr⟩)
      ⟨some tU64, .int (p.2 : Int) .uint64⟩
      = (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
          false (tail ++ [(Loc.base ⟨na⟩, su64 ((p.2 : Nat) : Int))])
          (na + 1)).heap from by
    show Heap.set (_ ++ tail) (.base ⟨na⟩) _ = _ ++ (tail ++ _)
    rw [set_fresh (by
      rw [lookup_append_right
        (lookup_cnFront_none nv sv qv bnv bsv l q biv b k cap iv0 sv2
          kvs civ false ha hD (by omega))]
      exact htail na (Nat.le_refl _))]
    simp [List.append_assoc]] at h
  exact h

/-- **One range iteration, GIVEN the pick** (both branches): within 24
steps the state advances to the erased snapshot with `best` at
`max bv p.2` and one fresh dead value cell. -/
theorem rg_iter (rem : List (List UInt8 × Nat)) (idx : Nat)
    (p : List UInt8 × Nat) (ch ch₂ : Choices) (nb : Nat) (bv : Nat)
    (tail : Heap) (na : Nat)
    (hcons : Choices.consume ch rem.length = (idx, ch₂))
    (hidx : idx < rem.length) (hp : rem[idx]? = some p)
    (hvnorm : IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int))
    (ha : 31 ≤ a) (hD : DeadFrom D a) (htail : DeadFrom tail na)
    (hna : a + 5 ≤ na) (hnb : a + 5 ≤ nb) (hbna : nb < na)
    (hbest : Heap.lookup tail (.base ⟨nb⟩)
      = some (su64 ((bv : Nat) : Int))) :
    ∃ (kk : Nat) (tail' : Heap),
      kk ≤ 24
      ∧ Heap.lookup tail' (.base ⟨nb⟩)
          = some (su64 ((max bv p.2 : Nat) : Int))
      ∧ DeadFrom tail' (na + 1)
      ∧ stepFnIter kk
          (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false tail na)
          (rHead a nb rem) ch
        = .ok (rHead a nb (rem.eraseIdx idx),
            cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
              civ false tail' (na + 1), ch₂) := by
  have hpick := stepFnIter_one
    (rg_pick σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ rem
      idx p ch ch₂ nb tail na hcons hidx hp hvnorm ha hD htail hna)
  let σ₁ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
    false (tail ++ [(Loc.base ⟨na⟩, su64 ((p.2 : Nat) : Int))])
    (na + 1)
  have hR1 := rg_R1 σ₁ (rem.eraseIdx idx) a nb na ch₂
  -- the `c` read
  have hlkc : Heap.lookup σ₁.heap (.base ⟨na⟩)
      = some (su64 ((p.2 : Nat) : Int)) := by
    show Heap.lookup (_ ++ (tail ++ [(Loc.base ⟨na⟩,
      su64 ((p.2 : Nat) : Int))])) (.base ⟨na⟩) = _
    rw [lookup_append_right
      (lookup_cnFront_none nv sv qv bnv bsv l q biv b k cap iv0 sv2
        kvs civ false ha hD (by omega)),
      lookup_append_right (htail na (Nat.le_refl _))]
    exact lookup_singleton_self
  have hVc1 := stepFnIter_one (stepFn_var (σ := σ₁) (x := "c")
    (env := rEnvIf a nb na) (a := ⟨na⟩)
    (k := .strictK .greaterCmp [] [.var "best"] (rEnvIf a nb na)
      (rIfK a nb na (rem.eraseIdx idx)))
    (ch := ch₂) rfl hlkc)
  have hR2 := rg_R2 σ₁ (rem.eraseIdx idx) a nb na ch₂
    (.int ((p.2 : Nat) : Int) .uint64)
  -- the `best` read
  have hlkb : Heap.lookup σ₁.heap (.base ⟨nb⟩)
      = some (su64 ((bv : Nat) : Int)) := by
    show Heap.lookup (_ ++ (tail ++ [(Loc.base ⟨na⟩,
      su64 ((p.2 : Nat) : Int))])) (.base ⟨nb⟩) = _
    rw [lookup_append_right
      (lookup_cnFront_none nv sv qv bnv bsv l q biv b k cap iv0 sv2
        kvs civ false ha hD (by omega))]
    exact lookup_append_left hbest
  have hVb := stepFnIter_one (stepFn_var (σ := σ₁) (x := "best")
    (env := rEnvIf a nb na) (a := ⟨nb⟩)
    (k := .strictK .greaterCmp [.int ((p.2 : Nat) : Int) .uint64] []
      (rEnvIf a nb na) (rIfK a nb na (rem.eraseIdx idx)))
    (ch := ch₂) rfl hlkb)
  have hR3 := rg_R3 σ₁ (rem.eraseIdx idx) a nb na ch₂
    ((p.2 : Nat) : Int) ((bv : Nat) : Int)
  have hpre := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hpick hR1) hVc1) hR2) hVb) hR3
  by_cases hcmp : bv < p.2
  · rw [show (decide (((bv : Nat) : Int) < ((p.2 : Nat) : Int)))
        = true from decide_eq_true (by exact_mod_cast hcmp)] at hpre
    have hR4a := rg_R4a σ₁ (rem.eraseIdx idx) a nb na ch₂
    have hsplice := stepFnIter_one (stepFn_seqn_splice (σ := σ₁)
      (ss := #[.assign (.var "best") (.var "c")])
      (env := rEnv4 a nb na) (rest := [])
      (k := .seq [] (rEnvIf a nb na) (rIterK a nb (rem.eraseIdx idx)))
      (ch := ch₂))
    have hR4b : stepFnIter 4 σ₁
        (.next (.seq ((#[.assign (.var "best") (.var "c")]
          : Array Stmt).toList ++ []) (rEnv4 a nb na)
          (.seq [] (rEnvIf a nb na) (rIterK a nb (rem.eraseIdx idx)))))
        ch₂
        = .ok (.evalE (.var "c") (rEnv4 a nb na)
              (.rhsK .vals [.chain (.addr (.base ⟨nb⟩)) [] []] [] []
                (.seqn #[]) (rEnv4 a nb na)
                (rStoreBestK a nb na (rem.eraseIdx idx))),
            σ₁, ch₂) := by
      with_unfolding_all rfl
    have hVc2 := stepFnIter_one (stepFn_var (σ := σ₁) (x := "c")
      (env := rEnv4 a nb na) (a := ⟨na⟩)
      (k := .rhsK .vals [.chain (.addr (.base ⟨nb⟩)) [] []] [] []
        (.seqn #[]) (rEnv4 a nb na)
        (rStoreBestK a nb na (rem.eraseIdx idx)))
      (ch := ch₂) rfl hlkc)
    have hR4c := rg_R4c σ₁ (rem.eraseIdx idx) a nb na ch₂
      (.int ((p.2 : Nat) : Int) .uint64)
    -- the `best` store
    have hstore : stepFnIter 1 σ₁
        (.next (.storeK [.chain (.addr (.base ⟨nb⟩)) [] []]
          [.int ((p.2 : Nat) : Int) .uint64] (.seqn #[])
          (rEnv4 a nb na) (rStoreBestK a nb na (rem.eraseIdx idx))))
        ch₂
        = .ok (.next (.storeK [] [] (.seqn #[]) (rEnv4 a nb na)
              (rStoreBestK a nb na (rem.eraseIdx idx))),
            cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
              civ false
              (Heap.set tail (.base ⟨nb⟩) (su64 ((p.2 : Nat) : Int))
                ++ [(Loc.base ⟨na⟩, su64 ((p.2 : Nat) : Int))])
              (na + 1), ch₂) := by
      refine stepFnIter_one (stepFn_store_step (rs := []) (vs := [])
        ?_)
      have h := storeTarget_addr (σ := σ₁) (a := ⟨nb⟩) (ty := tU64)
        (old := .int ((bv : Nat) : Int) .uint64)
        (v := .int ((p.2 : Nat) : Int) .uint64)
        (v' := .int ((p.2 : Nat) : Int) .uint64)
        hlkb
        (by
          simp only [normalizeValueForTy, normalizeValueForTyFuel,
            typeResolutionFuel]
          rw [hvnorm]
          rfl)
      rw [show Heap.set σ₁.heap (.base ⟨nb⟩)
          ⟨some tU64, .int ((p.2 : Nat) : Int) .uint64⟩
          = (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
              civ false
              (Heap.set tail (.base ⟨nb⟩) (su64 ((p.2 : Nat) : Int))
                ++ [(Loc.base ⟨na⟩, su64 ((p.2 : Nat) : Int))])
              (na + 1)).heap from by
        show Heap.set (_ ++ (tail ++ [(Loc.base ⟨na⟩,
          su64 ((p.2 : Nat) : Int))])) (.base ⟨nb⟩) _ = _
        rw [set_append_right
          (lookup_cnFront_none nv sv qv bnv bsv l q biv b k cap iv0
            sv2 kvs civ false ha hD (by omega)),
          set_append_left hbest]] at h
      exact h
    have hR5 := rg_R5
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false
        (Heap.set tail (.base ⟨nb⟩) (su64 ((p.2 : Nat) : Int))
          ++ [(Loc.base ⟨na⟩, su64 ((p.2 : Nat) : Int))]) (na + 1))
      (rem.eraseIdx idx) a nb na ch₂
    refine ⟨1 + 4 + 1 + 1 + 1 + 1 + 3 + 1 + 4 + 1 + 1 + 1 + 4,
      Heap.set tail (.base ⟨nb⟩) (su64 ((p.2 : Nat) : Int))
        ++ [(Loc.base ⟨na⟩, su64 ((p.2 : Nat) : Int))],
      by omega, ?_, ?_, ?_⟩
    · rw [show ((max bv p.2 : Nat) : Int) = ((p.2 : Nat) : Int) from by
        rw [Nat.max_eq_right (Nat.le_of_lt hcmp)]]
      exact lookup_append_left (lookup_set_self tail (.base ⟨nb⟩) _)
    · intro x hx
      rw [lookup_append_right (by
        rw [Machine.Heap.lookup_set_ne
          (show (Loc.base ⟨nb⟩ : Loc) ≠ .base ⟨x⟩ from by
            simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]
            omega)]
        exact htail x (by omega)),
        lookup_cons_ne (base_beq_false (by omega : na ≠ x))]
      rfl
    · exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain hpre hR4a) hsplice) hR4b) hVc2) hR4c)
            hstore) hR5
  · rw [show (decide (((bv : Nat) : Int) < ((p.2 : Nat) : Int)))
        = false from decide_eq_false (by
          intro hc
          exact hcmp (by exact_mod_cast hc))] at hpre
    have hR4e := rg_R4e σ₁ (rem.eraseIdx idx) a nb na ch₂
    refine ⟨1 + 4 + 1 + 1 + 1 + 1 + 3,
      tail ++ [(Loc.base ⟨na⟩, su64 ((p.2 : Nat) : Int))],
      by omega, ?_, DeadFrom.push htail,
      stepFnIter_chain hpre hR4e⟩
    rw [show ((max bv p.2 : Nat) : Int) = ((bv : Nat) : Int) from by
      rw [Nat.max_eq_left (by omega)]]
    exact lookup_append_left hbest

/-- **The range loop, at EVERY choice stream** (`24·m + 1` steps): the
snapshot drains, `best` ends at `max bv (maxOf values)`, the machine
parks at the result seam. -/
theorem rg_loop (bound : Nat) (hbound : bound < 2 ^ 64)
    (ha : 31 ≤ a) (hD : DeadFrom D a) :
    ∀ (m : Nat) (rem : List (List UInt8 × Nat)), rem.length = m →
    ∀ (bv : Nat) (nb : Nat) (tail : Heap) (na : Nat) (ch : Choices),
    (∀ p ∈ rem, p.2 ≤ bound) → bv ≤ bound →
    a + 5 ≤ nb → nb < na → a + 5 ≤ na →
    Heap.lookup tail (.base ⟨nb⟩) = some (su64 ((bv : Nat) : Int)) →
    DeadFrom tail na →
    ∃ (kk : Nat) (ch' : Choices) (tail' : Heap) (na' : Nat),
      kk ≤ 24 * m + 1 ∧ na ≤ na'
      ∧ Heap.lookup tail' (.base ⟨nb⟩)
          = some (su64 ((max bv (maxOf (rem.map Prod.snd)) : Nat) : Int))
      ∧ DeadFrom tail' na'
      ∧ stepFnIter kk
          (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false tail na)
          (rHead a nb rem) ch
        = .ok (.next (rKRes a nb),
            cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
              civ false tail' na', ch') := by
  intro m rem hm bv nb tail na ch hrem hbv hnb hbna hna hbest htail
  obtain ⟨kk, d', ch', hk, hP', hrun⟩ :=
    mapPickLoopW
      (T := fun d : Heap × Nat × Nat =>
        cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
          false d.1 d.2.1)
      (cfg := fun r => rHead a nb r)
      (exitCfg := .next (rKRes a nb))
      (P := fun d r =>
        d.2.2 ≤ bound ∧ (∀ p ∈ r, p.2 ≤ bound) ∧ na ≤ d.2.1
        ∧ nb < d.2.1
        ∧ Heap.lookup d.1 (.base ⟨nb⟩)
            = some (su64 ((d.2.2 : Nat) : Int))
        ∧ DeadFrom d.1 d.2.1
        ∧ max d.2.2 (maxOf (r.map Prod.snd))
            = max bv (maxOf (rem.map Prod.snd)))
      (c := 24) (e := 1)
      (fun d r idx p ch₀ ch₂ hcons hidx hp hP => by
        obtain ⟨hbv', hr, hna', hbna', hbest', htl, hmax⟩ := hP
        have hpmem : p ∈ r := by
          obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp hp
          exact h2 ▸ List.getElem_mem h1
        have hpc : p.2 ≤ bound := hr p hpmem
        have hvnorm : IntKind.normalize .uint64 (p.2 : Int)
            = (p.2 : Int) :=
          unorm_nat_of_lt (by omega)
        obtain ⟨k₁, tl', hk₁, hb', htl', hrun₁⟩ :=
          rg_iter σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
            civ r idx p ch₀ ch₂ nb d.2.2 d.1 d.2.1 hcons hidx hp
            hvnorm ha hD htl (by omega) hnb hbna' hbest'
        have hgetbang : (r.map Prod.snd)[idx]! = p.2 := by
          have hmap : (r.map Prod.snd)[idx]? = some p.2 := by
            simp [List.getElem?_map, hp]
          simp [List.getElem!_eq_getElem?_getD, hmap]
        have hmaxsplit : maxOf (r.map Prod.snd)
            = max p.2 (maxOf ((r.eraseIdx idx).map Prod.snd)) := by
          rw [← maxOf_eraseIdx (r.map Prod.snd) idx
              (by simpa using hidx), hgetbang, map_eraseIdx]
        refine ⟨k₁, (tl', d.2.1 + 1, max d.2.2 p.2), hk₁,
          ⟨Nat.max_le.mpr ⟨hbv', hpc⟩,
            fun z hz => hr z (GoLean.MapLoops.mem_of_mem_eraseIdx hz),
            Nat.le_succ_of_le hna', Nat.lt_succ_of_lt hbna', hb',
            htl', ?_⟩, hrun₁⟩
        show max (max d.2.2 p.2) (maxOf ((r.eraseIdx idx).map Prod.snd))
          = max bv (maxOf (rem.map Prod.snd))
        rw [← hmax, hmaxsplit, Nat.max_assoc])
      (fun d ch₀ _ =>
        rg_exit
          (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false d.1 d.2.1) a nb ch₀)
      m rem hm (tail, na, bv) ch
      ⟨hbv, hrem, Nat.le_refl na, hbna, hbest, htail, rfl⟩
  obtain ⟨hbv', -, hna', hbna', hbest', htl', hmax⟩ := hP'
  refine ⟨kk, ch', d'.1, d'.2.1, by omega, hna', ?_, htl', hrun⟩
  rw [show max bv (maxOf (rem.map Prod.snd)) = d'.2.2 from by
    rw [← hmax]
    simp [maxOf_nil]]
  exact hbest'

end RangeLoop

/-! ## The range head and the assembled range phase -/

section RangeHead

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
  (biv : Int) (b k cap : Nat) (iv0 sv2 : Int) (D : Heap) (a : Nat)
  (kvs : List (List UInt8 × Nat)) (civ : Int) (tail : Heap) (na : Nat)
  (ch : Choices)

theorem defaultValue_tU64W (σ' : ExecState) :
    defaultValue σ' tU64 = .ok (.int 0 .uint64) := by
  simp [defaultValue, defaultValueFuel, typeResolutionFuel]

theorem normalize_u64_0 (σ' : ExecState) :
    normalizeValueForTy σ' tU64 (.int 0 .uint64)
      = .ok (.int 0 .uint64) := by
  simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel]
  rfl

/-- **The range head** (16 steps): `best := 0` allocated at `na`, the
map snapshotted, the pick loop entered. -/
theorem rg_head (ha : 31 ≤ a) (hD : DeadFrom D a)
    (htail : DeadFrom tail na) (hna : a + 5 ≤ na)
    (hkv : ∀ p ∈ kvs,
      IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int)) :
    stepFnIter 16
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false tail na)
      (.exec wfBestSeqn (cEnvC a)
        (.seq [wfRangeStmt, wfResSeqn] (cEnvC a) wfFrameK)) ch
      = .ok (rHead a na kvs,
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1), ch) := by
  have hWD' : DeadFrom
      (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D) a :=
    fun x hx => by
      rw [lookup_append_right
        (lookup_wHeapCount_none nv sv qv bnv bsv l q biv b k cap iv0 sv2
          (by omega))]
      exact hD x hx
  have hfront : ∀ (x : Nat), na ≤ x →
      Heap.lookup
        (cnFront nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
          false) (.base ⟨x⟩) = none :=
    fun x hx =>
      lookup_cnFront_none nv sv qv bnv bsv l q biv b k cap iv0 sv2 kvs
        civ false ha hD (by omega)
  -- g1: the best-seqn splice
  have h1 := stepFnIter_one (stepFn_seqn_splice
    (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
      false tail na)
    (ss := #[.initialization { id := "best", typ := tU64 },
      .assign (.var "best") (.intLit 0 .uint64)])
    (env := cEnvC a) (rest := [wfRangeStmt, wfResSeqn])
    (k := wfFrameK) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seq_pop
    (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
      false tail na)
    (t := .initialization { id := "best", typ := tU64 })
    (rest := [.assign (.var "best") (.intLit 0 .uint64), wfRangeStmt,
      wfResSeqn])
    (env := cEnvC a) (k := wfFrameK) (ch := ch))
  -- g3: `best` allocated at `na`
  have h3 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false tail na)
      (.exec (.initialization { id := "best", typ := tU64 }) (cEnvC a)
        (.seq [.assign (.var "best") (.intLit 0 .uint64), wfRangeStmt,
          wfResSeqn] (cEnvC a) wfFrameK)) ch
      = .ok (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
              wfRangeStmt, wfResSeqn] (rEnv a na) wfFrameK),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1), ch) := by
    refine stepFnIter_one ?_
    have h := stepFn_init_seq
      (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false tail na)
      (p := { id := "best", typ := tU64 })
      (rest := [.assign (.var "best") (.intLit 0 .uint64), wfRangeStmt,
        wfResSeqn])
      (env := cEnvC a) (k := wfFrameK) (ch := ch)
      (v := .int 0 .uint64) (defaultValue_tU64W _)
    rw [show Heap.set
        (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
          false tail na).heap (.base ⟨na⟩)
        ⟨some tU64, .int 0 .uint64⟩
        = (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1)).heap
        from by
      show Heap.set (_ ++ tail) _ _ = _ ++ (tail ++ _)
      rw [set_fresh (by
        rw [lookup_append_right (hfront na (Nat.le_refl _))]
        exact htail na (Nat.le_refl _))]
      simp [List.append_assoc]] at h
    exact h
  -- g4 (6 steps, rfl): `best = 0` to the banked store
  have h4 : stepFnIter 6
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1))
      (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
        wfRangeStmt, wfResSeqn] (rEnv a na) wfFrameK)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
            [.int 0 .uint64] (.seqn #[]) (rEnv a na)
            (.seq [wfRangeStmt, wfResSeqn] (rEnv a na) wfFrameK)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1), ch) := by
    with_unfolding_all rfl
  -- g5: the `best = 0` store
  have h5 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1))
      (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
        [.int 0 .uint64] (.seqn #[]) (rEnv a na)
        (.seq [wfRangeStmt, wfResSeqn] (rEnv a na) wfFrameK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (rEnv a na)
            (.seq [wfRangeStmt, wfResSeqn] (rEnv a na) wfFrameK)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1), ch) := by
    refine stepFnIter_one (stepFn_store_step (rs := []) (vs := []) ?_)
    have h := storeTarget_addr
      (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1))
      (a := ⟨na⟩) (ty := tU64) (old := .int 0 .uint64)
      (v := .int 0 .uint64) (v' := .int 0 .uint64)
      (by
        show Heap.lookup (_ ++ (tail ++ [(Loc.base ⟨na⟩, su64 0)]))
          (.base ⟨na⟩) = some ⟨some tU64, .int 0 .uint64⟩
        rw [lookup_append_right (hfront na (Nat.le_refl _)),
          lookup_append_right (htail na (Nat.le_refl _))]
        exact lookup_singleton_self)
      (normalize_u64_0 _)
    rw [show Heap.set
        (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
          false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1)).heap
        (.base ⟨na⟩) ⟨some tU64, .int 0 .uint64⟩
        = (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1)).heap
        from by
      show Heap.set (_ ++ (tail ++ [(Loc.base ⟨na⟩, su64 0)])) _ _ = _
      rw [set_append_right (hfront na (Nat.le_refl _)),
        set_append_right (htail na (Nat.le_refl _)),
        set_singleton_self]] at h
    exact h
  -- g6…g8: drain, splice, the mapRange head
  have h6 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1))
      (.next (.storeK [] [] (.seqn #[]) (rEnv a na)
        (.seq [wfRangeStmt, wfResSeqn] (rEnv a na) wfFrameK))) ch
      = .ok (.exec (.seqn #[]) (rEnv a na)
            (.seq [wfRangeStmt, wfResSeqn] (rEnv a na) wfFrameK),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1), ch) := by
    with_unfolding_all rfl
  have h7 := stepFnIter_one (stepFn_seqn_splice
    (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
      false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1))
    (ss := #[]) (env := rEnv a na) (rest := [wfRangeStmt, wfResSeqn])
    (k := wfFrameK) (ch := ch))
  have h8 : stepFnIter 2
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1))
      (.next (.seq ((#[] : Array Stmt).toList
        ++ [wfRangeStmt, wfResSeqn]) (rEnv a na) wfFrameK)) ch
      = .ok (.evalE (.var "counts") (rEnv a na)
            (.mapRangeK none (some "c") tStr tU64
              wordFreqFunc.wfRangeBody (rEnv a na) (rKRes a na)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1), ch) := by
    with_unfolding_all rfl
  -- g9: the `counts` read
  have h9 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1))
      (.evalE (.var "counts") (rEnv a na)
        (.mapRangeK none (some "c") tStr tU64
          wordFreqFunc.wfRangeBody (rEnv a na) (rKRes a na))) ch
      = .ok (.retV (.map ⟨some (Loc.base ⟨a + 1⟩)⟩)
            (.mapRangeK none (some "c") tStr tU64
              wordFreqFunc.wfRangeBody (rEnv a na) (rKRes a na)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1), ch) := by
    refine stepFnIter_one (stepFn_var (a := ⟨a + 2⟩)
      (c := mhW (a + 1)) rfl ?_)
    exact lookup_five hWD' (by omega : (2 : Nat) < 5)
  -- g10: the snapshot
  have h10 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1))
      (.retV (.map ⟨some (Loc.base ⟨a + 1⟩)⟩)
        (.mapRangeK none (some "c") tStr tU64
          wordFreqFunc.wfRangeBody (rEnv a na) (rKRes a na))) ch
      = .ok (rHead a na kvs,
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false (tail ++ [(Loc.base ⟨na⟩, su64 0)]) (na + 1), ch) := by
    refine stepFnIter_one (stepFn_snapshot ?_)
    exact snapshot_toEntriesW
      (lookup_five hWD' (by omega : (1 : Nat) < 5)) hkv
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2) h3)
        h4) h5) h6) h7) h8) h9) h10

end RangeHead

/-! ## The counts-list length bound (for the fuel arithmetic) -/

private theorem bumpW_length_le (kvs : List (List UInt8 × Nat))
    (w : List UInt8) : (bumpW kvs w).length ≤ kvs.length + 1 := by
  induction kvs with
  | nil => simp [bumpW]
  | cons kv rest ih =>
      obtain ⟨kk, c⟩ := kv
      by_cases hk : kk = w
      · simp [bumpW, hk]
      · simp only [bumpW, if_neg hk, List.length_cons]
        omega

private theorem countsFoldW_length_le_aux (ws : List (List UInt8)) :
    ∀ kvs : List (List UInt8 × Nat),
    (List.foldl bumpW kvs ws).length ≤ kvs.length + ws.length := by
  induction ws with
  | nil => intro kvs; simp
  | cons w rest ih =>
      intro kvs
      simp only [List.foldl_cons, List.length_cons]
      have h1 := ih (bumpW kvs w)
      have h2 := bumpW_length_le kvs w
      omega

/-- The counts list never has more entries than words folded. -/
theorem countsFoldW_length_le (ws : List (List UInt8)) :
    (countsFoldW ws).length ≤ ws.length := by
  have := countsFoldW_length_le_aux ws []
  simpa [countsFoldW] using this

end GoLean.Examples.WordFreq
