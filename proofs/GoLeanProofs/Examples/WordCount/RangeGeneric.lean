import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Examples.WordCount.CanonCount

/-!
# WordCount — RangeGeneric

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

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The range loop (§10b): segments and the choice-pick induction -/

private theorem set_append_left {h₁ h₂ : Heap} {l : Loc} {c₀ c : HeapCell}
    (h : Heap.lookup h₁ l = some c₀) :
    Heap.set (h₁ ++ h₂) l c = Heap.set h₁ l c ++ h₂ := by
  induction h₁ with
  | nil => cases h
  | cons p rest ih =>
      obtain ⟨k, c'⟩ := p
      simp only [Heap.lookup] at h
      cases hb : (k == l) with
      | true => simp [Heap.set, hb]
      | false =>
          rw [hb] at h
          simp only [List.cons_append, Heap.set, hb, Bool.false_eq_true,
            if_false]
          exact congrArg _ (ih h)

/-- `Choices.consume`'s `% bound` contract: the pick is in range. -/
private theorem consume_lt (ch : Choices) {n : Nat} (hn : 0 < n) :
    (Choices.consume ch n).1 < n := by
  cases ch with
  | nil => simpa [Choices.consume] using hn
  | cons c rest =>
      simp only [Choices.consume]
      have : max 1 n = n := by omega
      rw [this]
      exact Nat.mod_lt _ hn

private theorem mem_of_mem_eraseIdx {α : Type} :
    ∀ {l : List α} {i : Nat} {a : α}, a ∈ l.eraseIdx i → a ∈ l := by
  intro l
  induction l with
  | nil => intro i a h; cases h
  | cons x rest ih =>
      intro i a h
      cases i with
      | zero =>
          rw [List.eraseIdx_cons_zero] at h
          exact List.mem_cons.mpr (.inr h)
      | succ n =>
          rw [List.eraseIdx_cons_succ] at h
          rcases List.mem_cons.mp h with h | h
          · exact List.mem_cons.mpr (.inl h)
          · exact List.mem_cons.mpr (.inr (ih h))

/-! ### The placement-generic range loop (consolidation slice: the
§10b choice-pick induction stated once)

The range body's segments never touch the heap — they are proven ONCE
over a fully abstract `σ : ExecState` (the state rides through). The
per-placement content is exactly four transitions: the pick (allocates
the iteration's value cell), the two variable reads (`c`, `best`), and
the `best` store — hypotheses whose types pin every state (the E-form
made structural, as in the counting layer). -/

section RangeGeneric

variable (envRBg : Nat → LocalEnv) (kRg : Nat → Cont)

/-- The iteration env: `c` at the pick cell over the placement's
range env. -/
def envIterR (B na : Nat) : LocalEnv :=
  [("c", .base ⟨na⟩)] :: envRBg B
def envIfR (B na : Nat) : LocalEnv := [] :: envIterR envRBg B na
def thenBlkR : Stmt :=
  .block #[] #[.seqn #[.assign (.var "best") (.var "c")]]
def iterKR (B : Nat) (rem : List (Int × Nat)) : Cont :=
  .mapIterK none (some "c") tU64 tU64 wcRangeBody (toEntries rem)
    (envRBg B) (kRg B)
def ifKRR (B na : Nat) (rem : List (Int × Nat)) : Cont :=
  .ifK thenBlkR (.seqn #[]) (envIfR envRBg B na)
    (.seq [] (envIfR envRBg B na) (iterKR envRBg kRg B rem))
def env4R (B na : Nat) : LocalEnv := [] :: envIfR envRBg B na
def storeBestKR (B na : Nat) (rem : List (Int × Nat)) : Cont :=
  .seq [] (env4R envRBg B na)
    (.seq [] (envIfR envRBg B na) (iterKR envRBg kRg B rem))
/-- The range head at the placement. -/
def rangeHeadR (B : Nat) (rem : List (Int × Nat)) : Config :=
  .next (iterKR envRBg kRg B rem)

/-- R1: body entry → the `c` read of the comparison. 4 steps —
σ-abstract (no heap touch). -/
private theorem segR1_g (σ : ExecState) (rem : List (Int × Nat))
    (B na₀ : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.exec wcRangeBody (envIterR envRBg B na₀) (iterKR envRBg kRg B rem))
      ch
      = .ok (.evalE (.var "c") (envIfR envRBg B na₀)
            (.strictK .greaterCmp [] [.var "best"] (envIfR envRBg B na₀)
              (ifKRR envRBg kRg B na₀ rem)),
          σ, ch) := by
  with_unfolding_all rfl

/-- R2: `c` delivered → the `best` read. 1 step. -/
private theorem segR2_g (σ : ExecState) (rem : List (Int × Nat))
    (B na₀ : Nat) (cv : GoValue) (ch : Choices) :
    stepFnIter 1 σ
      (.retV cv
        (.strictK .greaterCmp [] [.var "best"] (envIfR envRBg B na₀)
          (ifKRR envRBg kRg B na₀ rem))) ch
      = .ok (.evalE (.var "best") (envIfR envRBg B na₀)
            (.strictK .greaterCmp [cv] [] (envIfR envRBg B na₀)
              (ifKRR envRBg kRg B na₀ rem)),
          σ, ch) := by
  with_unfolding_all rfl

/-- R3: `best` delivered → the `>` apply, riding symbolically. 1
step. -/
private theorem segR3_g (σ : ExecState) (rem : List (Int × Nat))
    (B na₀ : Nat) (cv bv : Int) (ch : Choices) :
    stepFnIter 1 σ
      (.retV (.int bv .uint64)
        (.strictK .greaterCmp [.int cv .uint64] [] (envIfR envRBg B na₀)
          (ifKRR envRBg kRg B na₀ rem))) ch
      = .ok (.retV (.bool (decide (bv < cv))) (ifKRR envRBg kRg B na₀ rem),
          σ, ch) := by
  with_unfolding_all rfl

/-- R4a (then): comparison true → the inner `.seqn` splice point. 3
steps. -/
private theorem segR4a_g (σ : ExecState) (rem : List (Int × Nat))
    (B na₀ : Nat) (ch : Choices) :
    stepFnIter 3 σ (.retV (.bool true) (ifKRR envRBg kRg B na₀ rem)) ch
      = .ok (.exec (.seqn #[.assign (.var "best") (.var "c")])
            (env4R envRBg B na₀)
            (.seq [] (env4R envRBg B na₀)
              (.seq [] (envIfR envRBg B na₀) (iterKR envRBg kRg B rem))),
          σ, ch) := by
  with_unfolding_all rfl

/-- R4c: the store value delivered → the store point. 1 step. -/
private theorem segR4c_g (σ : ExecState) (rem : List (Int × Nat))
    (B na₀ : Nat) (cv : GoValue) (ch : Choices) :
    stepFnIter 1 σ
      (.retV cv
        (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
          (.seqn #[]) (env4R envRBg B na₀)
          (storeBestKR envRBg kRg B na₀ rem))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []] [cv]
            (.seqn #[]) (env4R envRBg B na₀)
            (storeBestKR envRBg kRg B na₀ rem)),
          σ, ch) := by
  with_unfolding_all rfl

/-- R5: `best` stored → the next pick point. 4 steps. -/
private theorem segR5_g (σ : ExecState) (rem : List (Int × Nat))
    (B na₀ : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.next (.storeK [] [] (.seqn #[]) (env4R envRBg B na₀)
        (storeBestKR envRBg kRg B na₀ rem))) ch
      = .ok (rangeHeadR envRBg kRg B rem, σ, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σ) (body := .seqn #[])
    (env := env4R envRBg B na₀) (k := storeBestKR envRBg kRg B na₀ rem)
    (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σ) (ss := #[]) (env := env4R envRBg B na₀)
    (rest := []) (k := .seq [] (envIfR envRBg B na₀)
      (iterKR envRBg kRg B rem)) (ch := ch))
  have h3 : stepFnIter 2 σ
      (.next (.seq ((#[] : Array Stmt).toList ++ []) (env4R envRBg B na₀)
        (.seq [] (envIfR envRBg B na₀) (iterKR envRBg kRg B rem)))) ch
      = .ok (rangeHeadR envRBg kRg B rem, σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- R4e (else): comparison false → the next pick point. 3 steps. -/
private theorem segR4e_g (σ : ExecState) (rem : List (Int × Nat))
    (B na₀ : Nat) (ch : Choices) :
    stepFnIter 3 σ (.retV (.bool false) (ifKRR envRBg kRg B na₀ rem)) ch
      = .ok (rangeHeadR envRBg kRg B rem, σ, ch) := by
  have h1 : stepFnIter 1 σ
      (.retV (.bool false) (ifKRR envRBg kRg B na₀ rem)) ch
      = .ok (.exec (.seqn #[]) (envIfR envRBg B na₀)
            (.seq [] (envIfR envRBg B na₀) (iterKR envRBg kRg B rem)),
          σ, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σ) (ss := #[]) (env := envIfR envRBg B na₀)
    (rest := []) (k := iterKR envRBg kRg B rem) (ch := ch))
  have h3 : stepFnIter 1 σ
      (.next (.seq ((#[] : Array Stmt).toList ++ []) (envIfR envRBg B na₀)
        (iterKR envRBg kRg B rem))) ch
      = .ok (rangeHeadR envRBg kRg B rem, σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- The empty-snapshot drain: no choice consumed, the loop exits. 1
step. -/
private theorem segRexit_g (σ : ExecState) (B : Nat) (ch : Choices) :
    stepFnIter 1 σ (rangeHeadR envRBg kRg B []) ch
      = .ok (.next (kRg B), σ, ch) := by
  with_unfolding_all rfl

/-- **The placement-generic range loop, at every choice stream** —
induction on the snapshot size, ∀ remaining sub-list, ∀ accumulator
`bv` with the max-fold invariant, ∀ choices (§10b). The placement
enters through four pinned transition hypotheses: the choice-pick
(allocating the iteration's value cell), the `c`/`best` reads, and the
`best` store. -/
theorem wcRange_generic
    (S : List (Int × Nat) → Int → Bool → Heap → Nat → ExecState)
    (ivP : Int) (base0 bound : Nat)
    (hbound : bound < 2 ^ 63)
    (hEnvBest : ∀ B na₀ : Nat,
      LocalEnv.lookup (envIfR envRBg B na₀) "best" = some (.base ⟨B⟩))
    (hPick : ∀ (kvs rem : List (Int × Nat)) (idx : Nat) (ch ch₂ : Choices)
      (p : Int × Nat) (tail : Heap) (B na : Nat),
      Choices.consume ch rem.length = (idx, ch₂) → idx < rem.length →
      rem[idx]? = some p →
      IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) →
      base0 ≤ na → DeadFrom tail na →
      stepFn (S kvs ivP false tail na) (rangeHeadR envRBg kRg B rem) ch
        = .ok (.exec wcRangeBody (envIterR envRBg B na)
              (iterKR envRBg kRg B (rem.eraseIdx idx)),
            S kvs ivP false
              (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
              (na + 1), ch₂))
    (hR4b : ∀ (kvs rem : List (Int × Nat)) (tail : Heap) (B na₀ na : Nat)
      (ch : Choices),
      stepFnIter 4 (S kvs ivP false tail na)
          (.next (.seq [.assign (.var "best") (.var "c")]
            (env4R envRBg B na₀)
            (.seq [] (envIfR envRBg B na₀) (iterKR envRBg kRg B rem)))) ch
        = .ok (.evalE (.var "c") (env4R envRBg B na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
                (.seqn #[]) (env4R envRBg B na₀)
                (storeBestKR envRBg kRg B na₀ rem)),
            S kvs ivP false tail na, ch))
    (hVarC : ∀ (kvs : List (Int × Nat)) (tail : Heap) (na₀ na : Nat)
      (v : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "c" = some (.base ⟨na₀⟩) →
      base0 ≤ na₀ → DeadFrom tail na₀ →
      stepFn (S kvs ivP false
          (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]) na)
          (.evalE (.var "c") env k) ch
        = .ok (.retV (.int v .uint64) k,
            S kvs ivP false
              (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]) na, ch))
    (hVarBest : ∀ (kvs : List (Int × Nat)) (tail : Heap) (B na : Nat)
      (bv : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "best" = some (.base ⟨B⟩) → base0 ≤ B →
      Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      stepFn (S kvs ivP false tail na) (.evalE (.var "best") env k) ch
        = .ok (.retV (.int bv .uint64) k, S kvs ivP false tail na, ch))
    (hStB : ∀ (kvs rem : List (Int × Nat)) (tail : Heap) (B na₀ na : Nat)
      (bv v : Int) (ch : Choices),
      base0 ≤ B → Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      IntKind.normalize .uint64 v = v →
      stepFn (S kvs ivP false tail na)
          (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int v .uint64] (.seqn #[]) (env4R envRBg B na₀)
            (storeBestKR envRBg kRg B na₀ rem))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (env4R envRBg B na₀)
              (storeBestKR envRBg kRg B na₀ rem)),
            S kvs ivP false
              (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int v .uint64⟩) na,
            ch)) :
    ∀ (m : Nat) (kvs rem : List (Int × Nat)), rem.length = m →
    ∀ (bv : Nat) (B na : Nat) (tail : Heap) (ch : Choices),
    (∀ p ∈ rem, p.2 ≤ bound) → bv ≤ bound →
    base0 ≤ B → B < na →
    Heap.lookup tail (.base ⟨B⟩) = some (u64cell (bv : Int)) →
    DeadFrom tail na →
    ∃ (k : Nat) (ch' : Choices) (tail' : Heap) (na' : Nat),
      k ≤ 24 * m + 1 ∧ na ≤ na'
      ∧ Heap.lookup tail' (.base ⟨B⟩)
          = some (u64cell ((max bv (maxOf (rem.map Prod.snd)) : Nat) : Int))
      ∧ DeadFrom tail' na'
      ∧ stepFnIter k (S kvs ivP false tail na)
          (rangeHeadR envRBg kRg B rem) ch
        = .ok (.next (kRg B), S kvs ivP false tail' na', ch') := by
  intro m
  induction m with
  | zero =>
      intro kvs rem hm bv B na tail ch hrem hbv hB hBna hbest htail
      have hnil : rem = [] := List.eq_nil_of_length_eq_zero hm
      subst hnil
      refine ⟨1, ch, tail, na, by omega, Nat.le_refl na, ?_, htail, ?_⟩
      · simpa [maxOf_nil] using hbest
      · exact segRexit_g envRBg kRg (S kvs ivP false tail na) B ch
  | succ m ih =>
      intro kvs rem hm bv B na tail ch hrem hbv hB hBna hbest htail
      rcases hcons : Choices.consume ch rem.length with ⟨idx, ch₂⟩
      have hidx : idx < rem.length := by
        have := consume_lt ch (show 0 < rem.length by omega)
        rw [hcons] at this
        exact this
      obtain ⟨p, hp⟩ : ∃ p, rem[idx]? = some p :=
        ⟨_, List.getElem?_eq_getElem hidx⟩
      have hpmem : p ∈ rem := by
        obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp hp
        exact h2 ▸ List.getElem_mem h1
      have hpc : p.2 ≤ bound := hrem p hpmem
      have hvnorm : IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) := by
        refine unorm_of_range (by omega) ?_
        have : p.2 < 2 ^ 64 := by omega
        exact_mod_cast this
      have h1 := stepFnIter_one
        (hPick kvs rem idx ch ch₂ p tail B na hcons hidx hp hvnorm
          (by omega) htail)
      have hR1 := segR1_g envRBg kRg
        (S kvs ivP false
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          (na + 1))
        (rem.eraseIdx idx) B na ch₂
      have h2 := stepFnIter_chain h1 hR1
      have hbest₁ : Heap.lookup
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          (.base ⟨B⟩) = some (u64cell (bv : Int)) :=
        lookup_append_left hbest
      have h3 := stepFnIter_chain h2 (stepFnIter_one
        (hVarC kvs tail na (na + 1) (p.2 : Int)
          (envIfR envRBg B na) _ ch₂ rfl (by omega) htail))
      have hR2 := segR2_g envRBg kRg
        (S kvs ivP false
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          (na + 1))
        (rem.eraseIdx idx) B na (.int (p.2 : Int) .uint64) ch₂
      have h4 := stepFnIter_chain h3 hR2
      have h5 := stepFnIter_chain h4 (stepFnIter_one
        (hVarBest kvs
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          B (na + 1) (bv : Int) (envIfR envRBg B na) _ ch₂ (hEnvBest B na)
          hB hbest₁))
      have hR3 := segR3_g envRBg kRg
        (S kvs ivP false
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          (na + 1))
        (rem.eraseIdx idx) B na (p.2 : Int) (bv : Int) ch₂
      have h6 := stepFnIter_chain h5 hR3
      have hgetbang : (rem.map Prod.snd)[idx]! = p.2 := by
        have hmap : (rem.map Prod.snd)[idx]? = some p.2 := by
          simp [List.getElem?_map, hp]
        simp [List.getElem!_eq_getElem?_getD, hmap]
      have hmaxsplit : maxOf (rem.map Prod.snd)
          = max p.2 (maxOf ((rem.eraseIdx idx).map Prod.snd)) := by
        rw [← maxOf_eraseIdx (rem.map Prod.snd) idx
            (by simpa using hidx), hgetbang, map_eraseIdx]
      have hlenerase : (rem.eraseIdx idx).length = m := by
        rw [List.length_eraseIdx_of_lt hidx]
        omega
      have hremerase : ∀ q ∈ rem.eraseIdx idx, q.2 ≤ bound :=
        fun q hq => hrem q (mem_of_mem_eraseIdx hq)
      by_cases hcmp : bv < p.2
      · rw [show (decide ((bv : Int) < (p.2 : Int))) = true from
          decide_eq_true (by exact_mod_cast hcmp)] at h6
        have hR4a := segR4a_g envRBg kRg
          (S kvs ivP false
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1))
          (rem.eraseIdx idx) B na ch₂
        have h7 := stepFnIter_chain h6 hR4a
        have h8 := stepFnIter_chain h7 (stepFnIter_one (stepFn_seqn_splice
          (σ := S kvs ivP false
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1))
          (ss := #[.assign (.var "best") (.var "c")])
          (env := env4R envRBg B na)
          (rest := []) (k := .seq [] (envIfR envRBg B na)
            (iterKR envRBg kRg B (rem.eraseIdx idx))) (ch := ch₂)))
        have hR4b := hR4b kvs (rem.eraseIdx idx)
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          B na (na + 1) ch₂
        have h9 := stepFnIter_chain h8 hR4b
        have h10 := stepFnIter_chain h9 (stepFnIter_one
          (hVarC kvs tail na (na + 1) (p.2 : Int)
            (env4R envRBg B na) _ ch₂ rfl (by omega) htail))
        have hR4c := segR4c_g envRBg kRg
          (S kvs ivP false
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1))
          (rem.eraseIdx idx) B na (.int (p.2 : Int) .uint64) ch₂
        have h11 := stepFnIter_chain h10 hR4c
        have h12 := stepFnIter_chain h11 (stepFnIter_one
          (hStB kvs (rem.eraseIdx idx)
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            B na (na + 1) (bv : Int) (p.2 : Int) ch₂ hB hbest₁ hvnorm))
        rw [set_append_left hbest] at h12
        have hR5 := segR5_g envRBg kRg
          (S kvs ivP false
            (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int (p.2 : Int) .uint64⟩
              ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1))
          (rem.eraseIdx idx) B na ch₂
        have h13 := stepFnIter_chain h12 hR5
        have hbest' : Heap.lookup
            (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int (p.2 : Int) .uint64⟩
              ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (.base ⟨B⟩) = some (u64cell (p.2 : Int)) :=
          lookup_append_left Frame.Heap.lookup_set_self
        have htail' : DeadFrom
            (Heap.set tail (.base ⟨B⟩)
                ⟨some tU64, .int (p.2 : Int) .uint64⟩
              ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1) := by
          intro x hx
          rw [lookup_append_right (by
            rw [Machine.Heap.lookup_set_ne
              (show (.base ⟨B⟩ : Loc) ≠ .base ⟨x⟩ from by
                simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]
                omega)]
            exact htail x (by omega)),
            lookup_cons_ne (base_beq_false (by omega : na ≠ x))]
          rfl
        obtain ⟨k', ch', tail₃, na₃, hk', hna₃, hbest₃, htail₃, hrun⟩ :=
          ih kvs (rem.eraseIdx idx) hlenerase p.2 B (na + 1)
            (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int (p.2 : Int) .uint64⟩
              ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            ch₂ hremerase hpc hB (by omega) hbest' htail'
        refine ⟨1 + 4 + 1 + 1 + 1 + 1 + 3 + 1 + 4 + 1 + 1 + 1 + 4 + k',
          ch', tail₃, na₃, by omega, by omega, ?_, htail₃, ?_⟩
        · rw [show max bv (maxOf (rem.map Prod.snd))
              = max p.2 (maxOf ((rem.eraseIdx idx).map Prod.snd)) from by
            rw [hmaxsplit]
            omega]
          exact hbest₃
        · exact stepFnIter_chain h13 hrun
      · rw [show (decide ((bv : Int) < (p.2 : Int))) = false from
          decide_eq_false (by
            intro hc
            exact hcmp (by exact_mod_cast hc))] at h6
        have hR4e := segR4e_g envRBg kRg
          (S kvs ivP false
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1))
          (rem.eraseIdx idx) B na ch₂
        have h7 := stepFnIter_chain h6 hR4e
        have hbest' : Heap.lookup
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (.base ⟨B⟩) = some (u64cell (bv : Int)) :=
          lookup_append_left hbest
        have htail' : DeadFrom
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1) := DeadFrom.push htail
        obtain ⟨k', ch', tail₃, na₃, hk', hna₃, hbest₃, htail₃, hrun⟩ :=
          ih kvs (rem.eraseIdx idx) hlenerase bv B (na + 1)
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            ch₂ hremerase hbv hB (by omega) hbest' htail'
        refine ⟨1 + 4 + 1 + 1 + 1 + 1 + 3 + k', ch', tail₃, na₃, by omega,
          by omega, ?_, htail₃, ?_⟩
        · rw [show max bv (maxOf (rem.map Prod.snd))
              = max bv (maxOf ((rem.eraseIdx idx).map Prod.snd)) from by
            rw [hmaxsplit]
            omega]
          exact hbest₃
        · exact stepFnIter_chain h7 hrun

end RangeGeneric

end GoLean.Examples.WordCount
