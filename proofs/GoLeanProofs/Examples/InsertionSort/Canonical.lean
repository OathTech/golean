import GoLeanProofs.Examples.InsertionSortProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Rename
import GoLeanProofs.Frame.Sim
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Examples.InsertionSort.PassFrame

/-!
# InsertionSort — Canonical

Per-phase shard of `GoLeanProofs.Examples.InsertionSort` (examples
phase-2 slice 0, lever 2, 2026-08-14). Every statement and proof here
is BYTE-IDENTICAL to the pre-split module; only file placement changed,
so Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.InsertionSort`, whose docstring records the
example's design and the shard map.
-/

namespace GoLean.Examples.InsertionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.Frame

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-! ## The OUTER induction (arc design: plain strong induction on the
remaining passes, invariant `sortPrefix` — with each pass transferred
from the tight placement through the frame theorem and rebased) -/

/-- **The outer loop over the true (garbage-laden) run**: from the
outer test delivery after `m` passes — the true state `σA` related to
the tight `sortPrefix` state by the accumulated-garbage frame — the run
reaches the driver terminal with the backing cell fully sorted. -/
private theorem isort_loop (xs : List Int) (n : Nat) (hn : n = xs.length)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (h63 : n < 2 ^ 63) :
    ∀ μ m (σA : ExecState) (fr : Heap), μ = n - (m + 1) →
    FrameSim (ρsh (2 * m)) 4 (4 + 2 * m) fr
      (σOut n (sortPrefix xs (m + 1)) ((m + 1 : Nat) : Int) false) σA →
    ∀ ch : Choices, ∃ (k : Nat) (σf : ExecState),
      k ≤ (92 * n + 160) * μ + 10 ∧
      stepFnIter k σA
        (.retV (.bool (decide (((m + 1 : Nat) : Int) < ((n : Nat) : Int))))
          outerCmpCont) ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨0⟩)
          = some (arrCell n (sortSpec xs)) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro m σA fr hμ hFS ch
    subst hμ
    rcases Nat.lt_or_ge (m + 1) n with hlt | hge
    · -- iterate: one more pass
      rw [show (decide (((m + 1 : Nat) : Int) < ((n : Nat) : Int))) = true
        from decide_eq_true (by omega)]
      have hplen : (sortSpec (xs.take (m + 1))).length = m + 1 := by
        rw [sortSpec_length, List.length_take]
        omega
      obtain ⟨K, jex, hK, hjex, hpass⟩ := pass_seg n
        (sortSpec (xs.take (m + 1))) (xs.drop (m + 2)) (xs.getD (m + 1) 0)
        m h63 hplen (by rw [hplen, List.length_drop]; omega)
        (sortSpec_sorted _)
        (fun x hx => hxs x (List.mem_of_mem_take (mem_sortSpec hx)))
        (hxs _ (getD_mem (by omega)))
        (fun x hx => hxs x (List.mem_of_mem_drop hx)) ch
      rw [← sortPrefix_decomp (by omega)] at hpass
      have hnext : sortPrefix xs (m + 2)
          = insertSpec (xs.getD (m + 1) 0) (sortSpec (xs.take (m + 1)))
            ++ xs.drop (m + 2) := by
        rw [sortPrefix]
        congr 1
        exact sortSpec_take_succ (k := m + 1) (by omega)
      rw [← hnext] at hpass
      obtain ⟨σA', hrunA, hFS'⟩ := transfer_seg hFS hpass
        (renCfg_cmp (2 * m) true) (renCfg_cmp (2 * m) _)
      have hFS2 := rebaseSim hFS'
      obtain ⟨k, σf, hk, hrun, hread⟩ := ih (n - (m + 2)) (by omega) (m + 1)
        σA' (fr ++ [(.base ⟨4 + 2 * m⟩, intcell ((jex : Nat) : Int)),
          (.base ⟨5 + 2 * m⟩, bcell false)]) rfl hFS2 ch
      refine ⟨K + k, σf, ?_, stepFnIter_chain hrunA hrun, hread⟩
      have hmul : (92 * n + 160) * (n - (m + 2)) + (92 * n + 160)
          = (92 * n + 160) * (n - (m + 1)) := by
        rw [← Nat.mul_succ]
        congr 1
        omega
      omega
    · -- exit
      rw [show (decide (((m + 1 : Nat) : Int) < ((n : Nat) : Int))) = false
        from decide_eq_false (by omega)]
      have hX := isort_exitO_raw n (sortPrefix xs (m + 1))
        ((m + 1 : Nat) : Int) [] 4 ch
      obtain ⟨σf, hrunA, hFS'⟩ := transfer_seg hFS hX
        (renCfg_cmp (2 * m) false) (renCfg_stop (2 * m))
      refine ⟨8, σf, by omega, hrunA, ?_⟩
      have hread := hFS'.lookup_some (l := .base ⟨0⟩)
        (c := arrCell n (sortPrefix xs (m + 1))) rfl
      rw [renCell_arr, sortPrefix_full (by omega)] at hread
      exact hread

/-! ## The canonical run, end to end -/

private theorem lookup_seed (xs : List Int) :
    Heap.lookup (isortSeed xs 0 [] 1).heap (.base ⟨0⟩)
      = some ⟨some (.array xs.length (.int .uint64)),
          .array ⟨xs.map (fun v => .int v .uint64)⟩⟩ := by
  simp [isortSeed, sliceCells, Heap.lookup]

/-- **The canonical run**: from the tight seed the driver completes at
the `.normal` terminal within `76 + (92·len + 160)·len` steps, with the
backing cell holding `sortSpec xs`. -/
private theorem isort_runs (xs : List Int)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63)
    (ch : Choices) :
    ∃ (k : Nat) (σf : ExecState),
      k ≤ 76 + (92 * xs.length + 160) * xs.length ∧
      stepFnIter k (isortSeed xs 0 [] 1)
        (.exec (isortCall xs 0) [] .stop) ch
        = .ok (.next .stop, σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨0⟩)
          = some (arrCell xs.length (sortSpec xs)) := by
  -- entry: driver → outer head
  have hA := isort_entryA_raw xs ch
  rw [inorm_nat_of_lt hlen] at hA
  have happ1 : applyStrictOp (isortSeed xs 0 [] 1) (.sliceExpr false)
      [.addr (.base ⟨0⟩), .int 0 .int, .int ((xs.length : Nat) : Int) .int]
      = .ok (sliceH xs.length, isortSeed xs 0 [] 1) :=
    applyStrictOp_sliceExpr_array (lookup_seed xs) (by simp)
  have hB := isort_entryB_raw xs ch
  have h8 := stepFnIter_chain hA
    (stepFnIter_one
      (stepFn_strict_apply (done := [.int 0 .int, .addr (.base ⟨0⟩)]) happ1))
  have h39 := stepFnIter_chain h8 hB
  -- first outer dispatch + test (tight 4-cell state)
  have hO0 := isort_segO0_raw xs.length xs 1 [] 4 ch
  have hlenapp : stepFn (σOutT xs.length xs 1 false [] 4)
      (.retV (sliceH xs.length) (lenTestK 1)) ch
      = .ok (.retV (.int ((xs.length : Nat) : Int) .int)
          (.strictK .lessCmp [.int 1 .int] [] ([] :: envO) outerCmpCont),
        σOutT xs.length xs 1 false [] 4, ch) :=
    stepFn_strict_apply (done := [])
      (applyStrictOp_len_slice (Nat.le_refl xs.length))
  have hOB := isort_segOB_raw xs.length xs 1 [] 4 ch
  have h66 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h39 hO0)
    (stepFnIter_one hlenapp)) hOB
  -- the outer loop from m = 0 (trivial frame: true state = tight state)
  have hFS0 : FrameSim (ρsh (2 * 0)) 4 (4 + 2 * 0) []
      (σOut xs.length (sortPrefix xs (0 + 1)) ((0 + 1 : Nat) : Int) false)
      (σOut xs.length xs 1 false) := by
    show FrameSim (ρsh 0) 4 4 []
      (σOut xs.length (sortPrefix xs 1) ((1 : Nat) : Int) false)
      (σOut xs.length xs 1 false)
    rw [sortPrefix_one]
    show FrameSim (ρsh 0) 4 4 [] (σOut xs.length xs 1 false)
      (σOut xs.length xs 1 false)
    exact frameSim_zero _ _ _ _
  obtain ⟨k, σf, hk, hrun, hread⟩ := isort_loop xs xs.length rfl hxs hlen
    (xs.length - (0 + 1)) 0 (σOut xs.length xs 1 false) [] rfl hFS0 ch
  refine ⟨66 + k, σf, ?_, stepFnIter_chain h66 hrun, hread⟩
  have hmono : (92 * xs.length + 160) * (xs.length - (0 + 1))
      ≤ (92 * xs.length + 160) * xs.length :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Total correctness at the canonical placement**: past fuel
`76 + (92·len + 160)·len`, at every choice stream, execution completes
normally with the sorted permutation in the backing cell. -/
private theorem isort_total_canonical (xs : List Int)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63) :
    ∀ fuel : Nat, 76 + (92 * xs.length + 160) * xs.length ≤ fuel →
    ∀ ch : Choices, ∃ σf : ExecState,
      execStmtLoop fuel (isortSeed xs 0 [] 1)
        (.exec (isortCall xs 0) [] .stop) ch = .ok (.normal σf, ch)
      ∧ Heap.lookup σf.heap (.base ⟨0⟩)
          = some (arrCell xs.length (sortSpec xs)) := by
  intro fuel hfuel ch
  obtain ⟨k, σf, hk, hrun, hread⟩ := isort_runs xs hxs hlen ch
  refine ⟨σf, ?_, hread⟩
  have hfold := execStmtLoop_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hfold, execStmtLoop_next_stop]

/-! ## The framed form: the frame theorem consumed at an
input-RELOCATING renaming (reverse's layer, verbatim-adapted) -/

/-- The input-relocating renaming: `0 ↦ base`, `1 + k ↦ na + k`. -/
def relocShift (base na : Nat) : Nat → Nat :=
  fun x => if x = 0 then base else na + (x - 1)

/-- The seed simulation: the canonical seed beside the framed seed at
an arbitrary placement, through the relocating shift. -/
private theorem isortSeedFrameSim (xs : List Int) (base : Nat) (fr : Heap)
    (na : Nat)
    (hb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hwf : MachineWf
      { functions := isortLowered.funcs,
        heap := sliceCells xs base ++ fr, nextAddr := na }
      (.exec (isortCall xs base) [] .stop)) :
    FrameSim (relocShift base na) 1 na fr (isortSeed xs 0 [] 1)
      (isortSeed xs base fr na) := by
  have hs := hwf.1
  simp only [StateWf, ExecState.locSup, Heap.locSup, sliceCells,
    List.cons_append, List.nil_append, Loc.locSup, Loc.rootBase,
    Nat.max_le] at hs
  have hbase : base + 1 ≤ na := hs.1.1.1
  have hfrsup : Heap.locSup fr ≤ na := hs.1.2
  have hren0 : renameLoc (relocShift base na) (.base ⟨0⟩) = .base ⟨base⟩ := by
    simp [renameLoc, relocShift]
  have hcellid : renameCell (relocShift base na)
      (⟨some (.array xs.length (.int .uint64)),
        .array ⟨xs.map (fun v => .int v .uint64)⟩⟩ : HeapCell)
      = ⟨some (.array xs.length (.int .uint64)),
         .array ⟨xs.map (fun v => .int v .uint64)⟩⟩ := by
    simp [renameCell, renameValue_locFree _ _ (locSup_mapU xs)]
  refine ⟨⟨?_, ?_⟩, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- inj
    intro x y hxy
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
      simp only [relocShift, hx, hy, if_pos, if_neg, if_true, if_false] at hxy <;>
      omega
  · -- shift
    intro k
    simp only [relocShift, if_neg (by omega : ¬ (1 + k = 0))]
    omega
  · -- next_eq: na = ρ 1
    simp [isortSeed, relocShift]
  · -- alloc_reg
    exact Nat.le_refl 1
  · -- lookup_img
    intro l
    by_cases hl : l = .base ⟨0⟩
    · subst hl
      rw [hren0]
      simp only [isortSeed, sliceCells, List.cons_append, List.nil_append,
        Heap.lookup]
      simp [hcellid]
    · have hcanon : Heap.lookup (isortSeed xs 0 [] 1).heap l = none := by
        have hne : ((.base ⟨0⟩ : Loc) == l) = false :=
          beq_false_of_ne (fun h => hl h.symm)
        simp [isortSeed, sliceCells, Heap.lookup, hne]
      rw [hcanon]
      have hne' : ((.base ⟨base⟩ : Loc) == renameLoc (relocShift base na) l)
          = false := by
        refine beq_false_of_ne (fun hc => ?_)
        cases l with
        | base a =>
            simp only [renameLoc, Loc.base.injEq, Addr.mk.injEq] at hc
            by_cases ha : a.id = 0
            · exact hl (by
                obtain ⟨id⟩ := a
                exact congrArg (fun n => Loc.base ⟨n⟩) ha)
            · simp only [relocShift, if_neg ha] at hc
              omega
        | field b tid f => simp [renameLoc] at hc
        | index b i => simp [renameLoc] at hc
      simp only [isortSeed, sliceCells, List.cons_append, List.nil_append,
        Heap.lookup, hne']
      rfl
  · -- frame_pres
    intro l c hl
    have hne : ((.base ⟨base⟩ : Loc) == l) = false := by
      refine beq_false_of_ne (fun hc => ?_)
      rw [← hc, hb] at hl
      cases hl
    simp only [isortSeed, sliceCells, List.cons_append, List.nil_append,
      Heap.lookup, hne]
    exact hl
  · -- fr_avoid
    intro a
    by_cases ha : a = 0
    · subst ha
      simpa [relocShift] using hb
    · cases hlk : Heap.lookup fr (.base ⟨relocShift base na a⟩) with
      | none => rfl
      | some c =>
          exfalso
          have hkey := Heap.lookup_key_locSup hlk
          simp only [Loc.locSup, Loc.rootBase] at hkey
          simp only [relocShift, if_neg ha] at hkey
          omega
  · -- bodies_inv
    exact renameBodies_id (n := 0) (fun x hx => absurd hx (Nat.not_lt_zero x))
      (fs := isortLowered.funcs)
      (by decide : funcListSup isortLowered.funcs.toList ≤ 0)

/-- The driver configuration renames to the framed driver: the
relocating shift carries the `locLit` base pointer to `base`. -/
private theorem isort_cfg_ren (xs : List Int) (base na : Nat) :
    renameConfig (relocShift base na)
      (.exec (isortCall xs 0) [] .stop)
      = .exec (isortCall xs base) [] .stop := by
  simp [renameConfig, renameCont, renameEnv, renameStmt, isortCall,
    renameExprList, renameExpr, renameOptExpr, renameLoc, relocShift]

/-! ## The memory-quantified form (proof-side supporting layer per §11;
the harness restatement is the recorded gap — module header) -/

/-- **The framed total form — proof-side supporting layer per §11 (the
memory-quantified form, kept; renamed from `isort_ok` when the harness
restatement below took that name, 2026-08-13)**: *for any list `xs` of
uint64 values, wherever it lives in memory, with anything else
present: `insertionSort` completes normally — past one fuel bound, at
every nondeterminism-choice stream — the backing cell then holds a
SORTED PERMUTATION of `xs` (`sortSpec xs`; `sortSpec_sorted`,
`sortSpec_count`, `sortSpec_length` make that reading a theorem), and
no other memory is touched.* The USER-FACING headline is `isort_ok`
below (harness ruling 2026-08-13, design note §11); this
memory-quantified form stays as the supporting layer — and it remains
the strongest ∀xs claim shipped (the harness headline quantifies the
input FAMILY `isFamily n seed`).

Statement deltas against the arc-design block: none beyond the
design's own (`hlen : xs.length < 2 ^ 63` — Go's `int` domain; the
driver's `len` literal wraps negative past it and the slice bounds
check panics, so the claim as drafted would be false there).

The proof: total correctness at the TIGHT canonical placement — two
plain nested strong inductions over direct machine-step segments (the
arc design), with each outer pass transferred through the executable
frame theorem at the accumulated-garbage shift `ρsh (2m)` and REBASED
(`rebaseSim`) because the machine re-allocates the inner `j`/`$forFirst`
pair every pass — then the frame theorem ONCE MORE at the
input-relocating renaming `relocShift base na` for the ∀-placement
∀-frame form. Nothing is re-run at any framed placement. -/
theorem isort_framed (xs : List Int) (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64)
    (hlen : xs.length < 2 ^ 63)
    (base : Nat) (fr : Heap) (na : Nat)
    (hb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hwf : MachineWf
      { functions := isortLowered.funcs,
        heap := sliceCells xs base ++ fr, nextAddr := na }
      (.exec (isortCall xs base) [] .stop)) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel [] (isortSeed xs base fr na) ch (isortCall xs base)
          = .ok (.normal σf, ch')
        ∧ Heap.lookup σf.heap (.base ⟨base⟩)
            = some ⟨some (.array xs.length (.int .uint64)),
                .array ⟨(sortSpec xs).map (fun v => .int v .uint64)⟩⟩
        ∧ ∀ (a : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨a⟩) = some c →
            Heap.lookup σf.heap (.base ⟨a⟩) = some c := by
  have hSF := isortSeedFrameSim xs base fr na hb hwf
  refine ⟨76 + (92 * xs.length + 160) * xs.length, fun fuel hfuel ch => ?_⟩
  obtain ⟨σc, hrunC, hreadC⟩ :=
    isort_total_canonical xs hxs hlen fuel hfuel ch
  obtain ⟨outF, hrunF, hout⟩ := Frame.execStmtLoop_ren fuel hSF hrunC
  rw [isort_cfg_ren xs base na] at hrunF
  cases outF with
  | normal σF =>
      obtain ⟨hSF', -⟩ := hout
      refine ⟨σF, ch, hrunF, ?_, ?_⟩
      · have hlook := hSF'.lookup_some hreadC
        have hren0 : renameLoc (relocShift base na) (.base ⟨0⟩)
            = .base ⟨base⟩ := by
          simp [renameLoc, relocShift]
        have hv : renameValue (relocShift base na)
            (.array ⟨(sortSpec xs).map (fun v => .int v .uint64)⟩)
            = .array ⟨(sortSpec xs).map (fun v => .int v .uint64)⟩ :=
          renameValue_locFree _ _ (locSup_mapU (sortSpec xs))
        have hcell : renameCell (relocShift base na)
            (⟨some (.array xs.length (.int .uint64)),
              .array ⟨(sortSpec xs).map (fun v => .int v .uint64)⟩⟩ : HeapCell)
            = ⟨some (.array xs.length (.int .uint64)),
               .array ⟨(sortSpec xs).map (fun v => .int v .uint64)⟩⟩ :=
          congrArg (HeapCell.mk (some (.array xs.length (.int .uint64)))) hv
        rw [hren0, hcell] at hlook
        exact hlook
      · intro a c hac
        exact hSF'.frame_pres (.base ⟨a⟩) c hac
  | returned σF => exact hout.elim
  | broke σF => exact hout.elim
  | continued σF => exact hout.elim

/-- **The D1 run-conditioned twin of the memory-quantified form**
(proof-side supporting layer per §11; renamed from `isort_readout`
with its total twin): any normal completion, at ANY fuel and stream,
delivers the sorted permutation and frame preservation — derived from
`isort_framed`, no second walk. -/
theorem isort_framed_readout (xs : List Int)
    (hxs : ∀ v ∈ xs, 0 ≤ v ∧ v < 2 ^ 64) (hlen : xs.length < 2 ^ 63)
    (base : Nat) (fr : Heap) (na : Nat)
    (hb : Heap.lookup fr (.base ⟨base⟩) = none)
    (hwf : MachineWf
      { functions := isortLowered.funcs,
        heap := sliceCells xs base ++ fr, nextAddr := na }
      (.exec (isortCall xs base) [] .stop)) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel [] (isortSeed xs base fr na) ch (isortCall xs base)
        = .ok (.normal σf, ch') →
      Heap.lookup σf.heap (.base ⟨base⟩)
          = some ⟨some (.array xs.length (.int .uint64)),
              .array ⟨(sortSpec xs).map (fun v => .int v .uint64)⟩⟩
        ∧ ∀ (a : Nat) (c : HeapCell),
            Heap.lookup fr (.base ⟨a⟩) = some c →
            Heap.lookup σf.heap (.base ⟨a⟩) = some c :=
  normal_readout_of_total (isort_framed xs hxs hlen base fr na hb hwf)


end GoLean.Examples.InsertionSort
