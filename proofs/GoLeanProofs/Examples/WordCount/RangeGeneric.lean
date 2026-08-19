import GoLeanProofs.MapMem
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Sim
import GoLeanProofs.MapLoops
import GoLeanProofs.Examples.WordCount.Machine
import GoLeanProofs.Examples.WordCount.Pure

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
open GoLean.MapLoops

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The range loop (§10b): segments and the choice-pick induction -/

-- (`set_append_left`, `consume_lt` and `mem_of_mem_eraseIdx` are the
-- kit's — `GoLean.Surface` / `GoLean.MapLoops` — the private copies
-- were deleted in the GAP-C1/R1 closures.)

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
variable (mbR : Nat) (startR : Array GoValue)

/-- The iteration env: `c` at the pick cell over the placement's
range env. -/
def envIterR (B na : Nat) : LocalEnv :=
  [("c", .base ⟨na⟩)] :: envRBg B
def envIfR (B na : Nat) : LocalEnv := [] :: envIterR envRBg B na
private def thenBlkR : Stmt :=
  .block #[] #[.seqn #[.assign (.var "best") (.var "c")]]
def iterKR (B : Nat) (pr : Array GoValue) : Cont :=
  .mapIterK none (some "c") tU64 tU64 wcRangeBody (some (.base ⟨mbR⟩))
    pr startR (envRBg B) (kRg B)
private def ifKRR (B na : Nat) (pr : Array GoValue) : Cont :=
  .ifK thenBlkR (.seqn #[]) (envIfR envRBg B na)
    (.seq [] (envIfR envRBg B na) (iterKR envRBg kRg mbR startR B pr))
def env4R (B na : Nat) : LocalEnv := [] :: envIfR envRBg B na
def storeBestKR (B na : Nat) (pr : Array GoValue) : Cont :=
  .seq [] (env4R envRBg B na)
    (.seq [] (envIfR envRBg B na) (iterKR envRBg kRg mbR startR B pr))
/-- The range head at the placement. -/
def rangeHeadR (B : Nat) (pr : Array GoValue) : Config :=
  .next (iterKR envRBg kRg mbR startR B pr)

/-- R1: body entry → the `c` read of the comparison. 4 steps —
σ-abstract (no heap touch). -/
private theorem segR1_g (σ : ExecState) (pr : Array GoValue)
    (B na₀ : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.exec wcRangeBody (envIterR envRBg B na₀) (iterKR envRBg kRg mbR startR B pr))
      ch
      = .ok (.evalE (.var "c") (envIfR envRBg B na₀)
            (.strictK .greaterCmp [] [.var "best"] (envIfR envRBg B na₀)
              (ifKRR envRBg kRg mbR startR B na₀ pr)),
          σ, ch) := by
  with_unfolding_all rfl

/-- R2: `c` delivered → the `best` read. 1 step. -/
private theorem segR2_g (σ : ExecState) (pr : Array GoValue)
    (B na₀ : Nat) (cv : GoValue) (ch : Choices) :
    stepFnIter 1 σ
      (.retV cv
        (.strictK .greaterCmp [] [.var "best"] (envIfR envRBg B na₀)
          (ifKRR envRBg kRg mbR startR B na₀ pr))) ch
      = .ok (.evalE (.var "best") (envIfR envRBg B na₀)
            (.strictK .greaterCmp [cv] [] (envIfR envRBg B na₀)
              (ifKRR envRBg kRg mbR startR B na₀ pr)),
          σ, ch) := by
  with_unfolding_all rfl

/-- R3: `best` delivered → the `>` apply, riding symbolically. 1
step. -/
private theorem segR3_g (σ : ExecState) (pr : Array GoValue)
    (B na₀ : Nat) (cv bv : Int) (ch : Choices) :
    stepFnIter 1 σ
      (.retV (.int bv .uint64)
        (.strictK .greaterCmp [.int cv .uint64] [] (envIfR envRBg B na₀)
          (ifKRR envRBg kRg mbR startR B na₀ pr))) ch
      = .ok (.retV (.bool (decide (bv < cv))) (ifKRR envRBg kRg mbR startR B na₀ pr),
          σ, ch) := by
  with_unfolding_all rfl

/-- R4a (then): comparison true → the inner `.seqn` splice point. 3
steps. -/
private theorem segR4a_g (σ : ExecState) (pr : Array GoValue)
    (B na₀ : Nat) (ch : Choices) :
    stepFnIter 3 σ (.retV (.bool true) (ifKRR envRBg kRg mbR startR B na₀ pr)) ch
      = .ok (.exec (.seqn #[.assign (.var "best") (.var "c")])
            (env4R envRBg B na₀)
            (.seq [] (env4R envRBg B na₀)
              (.seq [] (envIfR envRBg B na₀) (iterKR envRBg kRg mbR startR B pr))),
          σ, ch) := by
  with_unfolding_all rfl

/-- R4c: the store value delivered → the store point. 1 step. -/
private theorem segR4c_g (σ : ExecState) (pr : Array GoValue)
    (B na₀ : Nat) (cv : GoValue) (ch : Choices) :
    stepFnIter 1 σ
      (.retV cv
        (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
          (.seqn #[]) (env4R envRBg B na₀)
          (storeBestKR envRBg kRg mbR startR B na₀ pr))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []] [cv]
            (.seqn #[]) (env4R envRBg B na₀)
            (storeBestKR envRBg kRg mbR startR B na₀ pr)),
          σ, ch) := by
  with_unfolding_all rfl

/-- R5: `best` stored → the next pick point. 4 steps. -/
private theorem segR5_g (σ : ExecState) (pr : Array GoValue)
    (B na₀ : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.next (.storeK [] [] (.seqn #[]) (env4R envRBg B na₀)
        (storeBestKR envRBg kRg mbR startR B na₀ pr))) ch
      = .ok (rangeHeadR envRBg kRg mbR startR B pr, σ, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σ) (body := .seqn #[])
    (env := env4R envRBg B na₀) (k := storeBestKR envRBg kRg mbR startR B na₀ pr)
    (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σ) (ss := #[]) (env := env4R envRBg B na₀)
    (rest := []) (k := .seq [] (envIfR envRBg B na₀)
      (iterKR envRBg kRg mbR startR B pr)) (ch := ch))
  have h3 : stepFnIter 2 σ
      (.next (.seq ((#[] : Array Stmt).toList ++ []) (env4R envRBg B na₀)
        (.seq [] (envIfR envRBg B na₀) (iterKR envRBg kRg mbR startR B pr)))) ch
      = .ok (rangeHeadR envRBg kRg mbR startR B pr, σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- R4e (else): comparison false → the next pick point. 3 steps. -/
private theorem segR4e_g (σ : ExecState) (pr : Array GoValue)
    (B na₀ : Nat) (ch : Choices) :
    stepFnIter 3 σ (.retV (.bool false) (ifKRR envRBg kRg mbR startR B na₀ pr)) ch
      = .ok (rangeHeadR envRBg kRg mbR startR B pr, σ, ch) := by
  have h1 : stepFnIter 1 σ
      (.retV (.bool false) (ifKRR envRBg kRg mbR startR B na₀ pr)) ch
      = .ok (.exec (.seqn #[]) (envIfR envRBg B na₀)
            (.seq [] (envIfR envRBg B na₀) (iterKR envRBg kRg mbR startR B pr)),
          σ, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σ) (ss := #[]) (env := envIfR envRBg B na₀)
    (rest := []) (k := iterKR envRBg kRg mbR startR B pr) (ch := ch))
  have h3 : stepFnIter 1 σ
      (.next (.seq ((#[] : Array Stmt).toList ++ []) (envIfR envRBg B na₀)
        (iterKR envRBg kRg mbR startR B pr))) ch
      = .ok (rangeHeadR envRBg kRg mbR startR B pr, σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- **One range iteration, GIVEN the pick** (both branches of the
body): within 24 steps the state advances — the picked key joins the
produced set — with `best` at `max bv p.2` and one fresh dead value
cell. The (L) surgery's delta: the frame carries (base, produced,
start) instead of the retired snapshot; the LIST model `rem` (the
remaining candidates) lives only in the walk's bookkeeping, tied to
the frame by the placement's pick fact `hPick`. -/
private theorem wcRangeIter_generic
    (S : List (Int × Nat) → Int → Bool → Heap → Nat → ExecState)
    (ivP : Int) (base0 : Nat)
    (PC : List (Int × Nat) → Array GoValue → List (Int × Nat) → Prop)
    (hEnvBest : ∀ B na₀ : Nat,
      LocalEnv.lookup (envIfR envRBg B na₀) "best" = some (.base ⟨B⟩))
    (hPick : ∀ (kvs rem : List (Int × Nat)) (pr : Array GoValue)
      (idx : Nat) (ch ch₂ : Choices)
      (p : Int × Nat) (tail : Heap) (B na : Nat),
      PC kvs pr rem →
      Choices.consume ch rem.length = (idx, ch₂) → idx < rem.length →
      rem[idx]? = some p →
      IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) →
      base0 ≤ na → DeadFrom tail na →
      stepFn (S kvs ivP false tail na)
          (rangeHeadR envRBg kRg mbR startR B pr) ch
        = .ok (.exec wcRangeBody (envIterR envRBg B na)
              (iterKR envRBg kRg mbR startR B
                (pr.push (.int p.1 .uint64))),
            S kvs ivP false
              (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
              (na + 1), ch₂))
    (hR4b : ∀ (kvs : List (Int × Nat)) (pr : Array GoValue) (tail : Heap)
      (B na₀ na : Nat) (ch : Choices),
      stepFnIter 4 (S kvs ivP false tail na)
          (.next (.seq [.assign (.var "best") (.var "c")]
            (env4R envRBg B na₀)
            (.seq [] (envIfR envRBg B na₀)
              (iterKR envRBg kRg mbR startR B pr)))) ch
        = .ok (.evalE (.var "c") (env4R envRBg B na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
                (.seqn #[]) (env4R envRBg B na₀)
                (storeBestKR envRBg kRg mbR startR B na₀ pr)),
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
    (hStB : ∀ (kvs : List (Int × Nat)) (pr : Array GoValue) (tail : Heap)
      (B na₀ na : Nat) (bv v : Int) (ch : Choices),
      base0 ≤ B → Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      IntKind.normalize .uint64 v = v →
      stepFn (S kvs ivP false tail na)
          (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int v .uint64] (.seqn #[]) (env4R envRBg B na₀)
            (storeBestKR envRBg kRg mbR startR B na₀ pr))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (env4R envRBg B na₀)
              (storeBestKR envRBg kRg mbR startR B na₀ pr)),
            S kvs ivP false
              (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int v .uint64⟩) na,
            ch))
    (kvs rem : List (Int × Nat)) (pr : Array GoValue) (idx : Nat)
    (p : Int × Nat)
    (ch ch₂ : Choices) (B na : Nat) (bv : Nat) (tail : Heap)
    (hPC : PC kvs pr rem)
    (hcons : Choices.consume ch rem.length = (idx, ch₂))
    (hidx : idx < rem.length) (hp : rem[idx]? = some p)
    (hvnorm : IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int))
    (hB : base0 ≤ B) (hBna : B < na)
    (hbest : Heap.lookup tail (.base ⟨B⟩) = some (u64cell (bv : Int)))
    (htail : DeadFrom tail na) :
    ∃ (k : Nat) (tail' : Heap),
      k ≤ 24
      ∧ Heap.lookup tail' (.base ⟨B⟩)
          = some (u64cell ((max bv p.2 : Nat) : Int))
      ∧ DeadFrom tail' (na + 1)
      ∧ stepFnIter k (S kvs ivP false tail na)
          (rangeHeadR envRBg kRg mbR startR B pr) ch
        = .ok (rangeHeadR envRBg kRg mbR startR B
              (pr.push (.int p.1 .uint64)),
            S kvs ivP false tail' (na + 1), ch₂) := by
  have h1 := stepFnIter_one
    (hPick kvs rem pr idx ch ch₂ p tail B na hPC hcons hidx hp hvnorm
      (by omega) htail)
  have hR1 := segR1_g envRBg kRg mbR startR
    (S kvs ivP false
      (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
      (na + 1))
    (pr.push (.int p.1 .uint64)) B na ch₂
  have h2 := stepFnIter_chain h1 hR1
  have hbest₁ : Heap.lookup
      (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
      (.base ⟨B⟩) = some (u64cell (bv : Int)) :=
    lookup_append_left hbest
  have h3 := stepFnIter_chain h2 (stepFnIter_one
    (hVarC kvs tail na (na + 1) (p.2 : Int)
      (envIfR envRBg B na) _ ch₂ rfl (by omega) htail))
  have hR2 := segR2_g envRBg kRg mbR startR
    (S kvs ivP false
      (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
      (na + 1))
    (pr.push (.int p.1 .uint64)) B na (.int (p.2 : Int) .uint64) ch₂
  have h4 := stepFnIter_chain h3 hR2
  have h5 := stepFnIter_chain h4 (stepFnIter_one
    (hVarBest kvs
      (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
      B (na + 1) (bv : Int) (envIfR envRBg B na) _ ch₂ (hEnvBest B na)
      hB hbest₁))
  have hR3 := segR3_g envRBg kRg mbR startR
    (S kvs ivP false
      (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
      (na + 1))
    (pr.push (.int p.1 .uint64)) B na (p.2 : Int) (bv : Int) ch₂
  have h6 := stepFnIter_chain h5 hR3
  by_cases hcmp : bv < p.2
  · rw [show (decide ((bv : Int) < (p.2 : Int))) = true from
      decide_eq_true (by exact_mod_cast hcmp)] at h6
    have hR4a := segR4a_g envRBg kRg mbR startR
      (S kvs ivP false
        (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
        (na + 1))
      (pr.push (.int p.1 .uint64)) B na ch₂
    have h7 := stepFnIter_chain h6 hR4a
    have h8 := stepFnIter_chain h7 (stepFnIter_one (stepFn_seqn_splice
      (σ := S kvs ivP false
        (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
        (na + 1))
      (ss := #[.assign (.var "best") (.var "c")])
      (env := env4R envRBg B na)
      (rest := []) (k := .seq [] (envIfR envRBg B na)
        (iterKR envRBg kRg mbR startR B (pr.push (.int p.1 .uint64)))) (ch := ch₂)))
    have hR4b' := hR4b kvs (pr.push (.int p.1 .uint64))
      (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
      B na (na + 1) ch₂
    have h9 := stepFnIter_chain h8 hR4b'
    have h10 := stepFnIter_chain h9 (stepFnIter_one
      (hVarC kvs tail na (na + 1) (p.2 : Int)
        (env4R envRBg B na) _ ch₂ rfl (by omega) htail))
    have hR4c := segR4c_g envRBg kRg mbR startR
      (S kvs ivP false
        (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
        (na + 1))
      (pr.push (.int p.1 .uint64)) B na (.int (p.2 : Int) .uint64) ch₂
    have h11 := stepFnIter_chain h10 hR4c
    have h12 := stepFnIter_chain h11 (stepFnIter_one
      (hStB kvs (pr.push (.int p.1 .uint64))
        (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
        B na (na + 1) (bv : Int) (p.2 : Int) ch₂ hB hbest₁ hvnorm))
    rw [set_append_left hbest] at h12
    have hR5 := segR5_g envRBg kRg mbR startR
      (S kvs ivP false
        (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int (p.2 : Int) .uint64⟩
          ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
        (na + 1))
      (pr.push (.int p.1 .uint64)) B na ch₂
    have h13 := stepFnIter_chain h12 hR5
    refine ⟨1 + 4 + 1 + 1 + 1 + 1 + 3 + 1 + 4 + 1 + 1 + 1 + 4,
      Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int (p.2 : Int) .uint64⟩
        ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)],
      by omega, ?_, ?_, h13⟩
    · rw [show ((max bv p.2 : Nat) : Int) = (p.2 : Int) from by
        rw [Nat.max_eq_right (Nat.le_of_lt hcmp)]]
      exact lookup_append_left Frame.Heap.lookup_set_self
    · intro x hx
      rw [lookup_append_right (by
        rw [Machine.Heap.lookup_set_ne
          (show (.base ⟨B⟩ : Loc) ≠ .base ⟨x⟩ from by
            simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]
            omega)]
        exact htail x (by omega)),
        lookup_cons_ne (base_beq_false (by omega : na ≠ x))]
      rfl
  · rw [show (decide ((bv : Int) < (p.2 : Int))) = false from
      decide_eq_false (by
        intro hc
        exact hcmp (by exact_mod_cast hc))] at h6
    have hR4e := segR4e_g envRBg kRg mbR startR
      (S kvs ivP false
        (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
        (na + 1))
      (pr.push (.int p.1 .uint64)) B na ch₂
    have h7 := stepFnIter_chain h6 hR4e
    refine ⟨1 + 4 + 1 + 1 + 1 + 1 + 3,
      tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)],
      by omega, ?_, DeadFrom.push htail, h7⟩
    rw [show ((max bv p.2 : Nat) : Int) = (bv : Int) from by
      rw [Nat.max_eq_left (by omega)]]
    exact lookup_append_left hbest

/-- **The placement-generic range loop, at every choice stream** — the
kit's `mapPickLoop_generic` at this placement's iteration
(`wcRangeIter_generic`), with the max-fold carried as the CONSERVATION
invariant. The (L) surgery's deltas: the walk state carries the
PRODUCED-KEY array (the frame's), the pick-coherence relation `PC`
ties it to the remaining-candidates list model (the placement proves
`PC` from its cell shape via `MapMem.candidates_toEntries` /
`mandatory_toEntries`), and the EXIT is the placement-supplied done
step (`hExit`, one step — `MapMem.stepFn_iter_done` at the
placement's cell). -/
theorem wcRange_generic
    (S : List (Int × Nat) → Int → Bool → Heap → Nat → ExecState)
    (ivP : Int) (base0 bound : Nat)
    (hbound : bound < 2 ^ 63)
    (PC : List (Int × Nat) → Array GoValue → List (Int × Nat) → Prop)
    (hPCstep : ∀ (kvs : List (Int × Nat)) (pr : Array GoValue)
      (r : List (Int × Nat)) (idx : Nat)
      (p : Int × Nat), r[idx]? = some p → PC kvs pr r →
      PC kvs (pr.push (.int p.1 .uint64)) (r.eraseIdx idx))
    (hEnvBest : ∀ B na₀ : Nat,
      LocalEnv.lookup (envIfR envRBg B na₀) "best" = some (.base ⟨B⟩))
    (hPick : ∀ (kvs rem : List (Int × Nat)) (pr : Array GoValue)
      (idx : Nat) (ch ch₂ : Choices)
      (p : Int × Nat) (tail : Heap) (B na : Nat),
      PC kvs pr rem →
      Choices.consume ch rem.length = (idx, ch₂) → idx < rem.length →
      rem[idx]? = some p →
      IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) →
      base0 ≤ na → DeadFrom tail na →
      stepFn (S kvs ivP false tail na)
          (rangeHeadR envRBg kRg mbR startR B pr) ch
        = .ok (.exec wcRangeBody (envIterR envRBg B na)
              (iterKR envRBg kRg mbR startR B
                (pr.push (.int p.1 .uint64))),
            S kvs ivP false
              (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
              (na + 1), ch₂))
    (hExit : ∀ (kvs : List (Int × Nat)) (pr : Array GoValue) (tail : Heap)
      (B na : Nat) (ch : Choices), PC kvs pr [] →
      stepFnIter 1 (S kvs ivP false tail na)
          (rangeHeadR envRBg kRg mbR startR B pr) ch
        = .ok (.next (kRg B), S kvs ivP false tail na, ch))
    (hR4b : ∀ (kvs : List (Int × Nat)) (pr : Array GoValue) (tail : Heap)
      (B na₀ na : Nat) (ch : Choices),
      stepFnIter 4 (S kvs ivP false tail na)
          (.next (.seq [.assign (.var "best") (.var "c")]
            (env4R envRBg B na₀)
            (.seq [] (envIfR envRBg B na₀)
              (iterKR envRBg kRg mbR startR B pr)))) ch
        = .ok (.evalE (.var "c") (env4R envRBg B na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
                (.seqn #[]) (env4R envRBg B na₀)
                (storeBestKR envRBg kRg mbR startR B na₀ pr)),
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
    (hStB : ∀ (kvs : List (Int × Nat)) (pr : Array GoValue) (tail : Heap)
      (B na₀ na : Nat) (bv v : Int) (ch : Choices),
      base0 ≤ B → Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      IntKind.normalize .uint64 v = v →
      stepFn (S kvs ivP false tail na)
          (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int v .uint64] (.seqn #[]) (env4R envRBg B na₀)
            (storeBestKR envRBg kRg mbR startR B na₀ pr))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (env4R envRBg B na₀)
              (storeBestKR envRBg kRg mbR startR B na₀ pr)),
            S kvs ivP false
              (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int v .uint64⟩) na,
            ch)) :
    ∀ (m : Nat) (kvs rem : List (Int × Nat)), rem.length = m →
    ∀ (pr : Array GoValue) (bv : Nat) (B na : Nat) (tail : Heap)
      (ch : Choices),
    PC kvs pr rem →
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
          (rangeHeadR envRBg kRg mbR startR B pr) ch
        = .ok (.next (kRg B), S kvs ivP false tail' na', ch') := by
  intro m kvs rem hm pr bv B na tail ch hPC hrem hbv hB hBna hbest htail
  obtain ⟨k, d', ch', hk, hP', hrun⟩ :=
    mapPickLoop_generic
      (T := fun d : Heap × Nat × Nat × Array GoValue =>
        S kvs ivP false d.1 d.2.1)
      (cfg := fun d _ => rangeHeadR envRBg kRg mbR startR B d.2.2.2)
      (exitCfg := .next (kRg B))
      (P := fun d r =>
        d.2.2.1 ≤ bound ∧ (∀ q ∈ r, q.2 ≤ bound) ∧ na ≤ d.2.1 ∧ B < d.2.1
        ∧ Heap.lookup d.1 (.base ⟨B⟩)
            = some (u64cell ((d.2.2.1 : Nat) : Int))
        ∧ DeadFrom d.1 d.2.1
        ∧ PC kvs d.2.2.2 r
        ∧ max d.2.2.1 (maxOf (r.map Prod.snd))
            = max bv (maxOf (rem.map Prod.snd)))
      (c := 24) (e := 1)
      (fun d r idx p ch₀ ch₂ hcons hidx hp hP => by
        obtain ⟨hbv', hr, hna', hBna', hbest', htl, hPCd, hmax⟩ := hP
        have hpmem : p ∈ r := by
          obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp hp
          exact h2 ▸ List.getElem_mem h1
        have hpc : p.2 ≤ bound := hr p hpmem
        have hvnorm : IntKind.normalize .uint64 (p.2 : Int)
            = (p.2 : Int) := by
          refine unorm_of_range (by omega) ?_
          have : p.2 < 2 ^ 64 := by omega
          exact_mod_cast this
        obtain ⟨k₁, tl', hk₁, hb', htl', hrun₁⟩ :=
          wcRangeIter_generic envRBg kRg mbR startR S ivP base0 PC hEnvBest
            hPick hR4b hVarC hVarBest hStB kvs r d.2.2.2 idx p ch₀ ch₂ B
            d.2.1 d.2.2.1 d.1 hPCd hcons hidx hp hvnorm hB hBna' hbest' htl
        have hgetbang : (r.map Prod.snd)[idx]! = p.2 := by
          have hmap : (r.map Prod.snd)[idx]? = some p.2 := by
            simp [List.getElem?_map, hp]
          simp [List.getElem!_eq_getElem?_getD, hmap]
        have hmaxsplit : maxOf (r.map Prod.snd)
            = max p.2 (maxOf ((r.eraseIdx idx).map Prod.snd)) := by
          rw [← maxOf_eraseIdx (r.map Prod.snd) idx
              (by simpa using hidx), hgetbang, map_eraseIdx]
        refine ⟨k₁,
          (tl', d.2.1 + 1, max d.2.2.1 p.2, d.2.2.2.push (.int p.1 .uint64)),
          hk₁,
          ⟨Nat.max_le.mpr ⟨hbv', hpc⟩,
            fun q hq => hr q (mem_of_mem_eraseIdx hq),
            Nat.le_succ_of_le hna', Nat.lt_succ_of_lt hBna', hb', htl',
            hPCstep kvs d.2.2.2 r idx p hp hPCd,
            ?_⟩, hrun₁⟩
        show max (max d.2.2.1 p.2) (maxOf ((r.eraseIdx idx).map Prod.snd))
          = max bv (maxOf (rem.map Prod.snd))
        rw [← hmax, hmaxsplit, Nat.max_assoc])
      (fun d ch₀ hP =>
        hExit kvs d.2.2.2 d.1 B d.2.1 ch₀ hP.2.2.2.2.2.2.1)
      m rem hm (tail, na, bv, pr) ch
      ⟨hbv, hrem, Nat.le_refl na, hBna, hbest, htail, hPC, rfl⟩
  obtain ⟨hbv', -, hna', hBna', hbest', htl', -, hmax⟩ := hP'
  refine ⟨k, ch', d'.1, d'.2.1, by omega, hna', ?_, htl', hrun⟩
  rw [show max bv (maxOf (rem.map Prod.snd)) = d'.2.2.1 from by
    rw [← hmax]
    simp [maxOf_nil]]
  exact hbest'

end RangeGeneric

end GoLean.Examples.WordCount
