import GoLeanProofs.Specs.Callchain

/-!
# C-05 `callchain` — the boundary sentences (the export file)

The quartet's FIRST-ORDER sentences + the `goSpec` exit, split from
the WP walks per the A-TRIP lane's file convention (corpus WP-walk
files are the police class; sentence-export files are the
boundary-sentences class — the walks in `Specs/Callchain.lean` never
mention the executable machine, while the sentences here speak
`execStmt` as their designated vocabulary). Split done against the
convention as landed at a-trip `b4160505`; if the published
boundary-sentences class names a different layout, this file takes
the rename pass at the post-merge rebase. Enrollment in
`scripts/wp-lint-scope.txt` is NOT done here (that file is the
A-TRIP lane's; enrollment happens at the post-merge rebase).

All four sentences are CANDIDATES — nothing here is designated
(designation batches are the [USER]'s N-5 gate).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface (outCell0 outEnv HProp GoSpec GoTriple ProgressExec
  Heaplet heapletOf sat InitialSplit)

namespace GoLean.Iris.Callchain

set_option linter.unusedSimpArgs false

/-- The seeded output cell holding `v` (the `outCell0`/`outCell2`
family, value-generic). -/
def ccOutCellV (v : Int) : HProp :=
  .pointsTo 0 ⟨some (.int .int), .int v .int⟩

/-- The seeded driver at input `n`: call the subject into the pinned
output cell (`outEnv` names it `r`). -/
abbrev callchainDriver (n : Int) : Stmt :=
  .call #[.var "r"] ⟨"ccCaller"⟩ #[.intLit n .int]

/-- The concrete seeded initial state (the `goldenOut` shape at the
callchain tables). -/
def ccSeed : ExecState :=
  { types := callchainLowered.typeDefs.toList,
    functions := callchainLowered.funcs,
    methods := callchainLowered.methods,
    heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
    nextAddr := 1 }

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

/-- The driver, exit form: `{r ↦ 0} r = ccCaller(n) {r ↦ ccSpec n}` as
the WP entailment the Surface exit theorem consumes. -/
theorem wp_callchainDriver (n : Int)
    (hn : IntKind.normalize .int n = n)
    (hprog : GoCoreGS.prog GF = callchainLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) outCell0
      ⊢ WP (Config.exec (callchainDriver n) outEnv .stop)
          {{ _v, embed (ccOutCellV (ccSpec n)) }} := by
  simp only [outCell0, ccOutCellV, embed]
  iintro Hr
  iapply (wp_callchainCall (w := .int 0 .int) rfl hprog hmeths hn rfl)
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply (wp_value' (v := ()))
  iexact Hr

end

/-- **C-05's FuncSpec-analogue sentence (CANDIDATE — NOT designated;
designation is the [USER]'s N-5 batch)**: the frame-closed Surface
judgment `{r ↦ 0} r = ccCaller(n) {r ↦ ccSpec n}` plus interpreter-side
safety, for every in-range int input — one symbolic WP proof, composed
through the bind rule at all three call sites. -/
theorem callchainSpec (n : Int)
    (hn : IntKind.normalize .int n = n) :
    GoSpec callchainLowered.typeDefs.toList callchainLowered.funcs
      callchainLowered.methods outEnv outCell0 (callchainDriver n)
      (ccOutCellV (ccSpec n)) := by
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  exact wp_callchainDriver n hn hprog hmeths

/-- **C-05's first-order readout (CANDIDATE — NOT designated)**: every
terminating `execStmt` run of the seeded driver leaves
`ccSpec n = ((2n mod) + 1 mod) + 3 mod` in the pinned output cell —
interpreter vocabulary only, symbolic in the input. -/
theorem callchainReturns (n : Int)
    (hn : IntKind.normalize .int n = n) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel outEnv ccSeed ch (callchainDriver n)
        = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int (ccSpec n) .int) := by
  intro fuel ch σf ch' hrun
  have htriple := (callchainSpec n hn).1
  have hres := htriple ccSeed.heap 1 (heapletOf ccSeed.heap)
    (∅ : Heaplet)
    { disj := fun k => .inr (by
        rw [heaplet_get?_eq]
        exact LawfulPartialMap.get?_empty (M := GoHeapF) (k := k))
      cover := fun k c => by
        constructor
        · exact fun h => .inl h
        · rintro (h | h)
          · exact h
          · rw [heaplet_get?_eq,
              LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)] at h
            cases h
      sat_pre := by rfl
      wf := of_decide_eq_true rfl }
    fuel ch σf ch' hrun
  obtain ⟨h, _hd, hsub, _hF, hsat⟩ := hres
  rw [show h = (∅ : Heaplet).insert 0
      ⟨some (.int .int), .int (ccSpec n) .int⟩ from hsat] at hsub
  have hget := hsub 0 ⟨some (.int .int), .int (ccSpec n) .int⟩ (by
    rw [heaplet_get?_eq, heaplet_insert_eq]
    exact LawfulPartialMap.get?_insert_eq rfl)
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hget
  exact loadLoc_base_of_lookup hget

/-- The human-checkable instance: `ccCaller(5) = 14` in every
terminating run (double 5 → 10, deferred bump → 11, add 3 → 14). -/
theorem callchainReturnsFourteen :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel outEnv ccSeed ch (callchainDriver 5)
        = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 14 .int) := by
  have h := callchainReturns 5 (by decide)
  rw [show ccSpec 5 = 14 from by decide] at h
  exact h

/-- **C-05's NEGATIVE TWIN (CANDIDATE — NOT designated)**: the output
cell provably does NOT hold `13` in any terminating run at input 5 —
and `13` is exactly what a defer-ordering bug would produce (the
deferred `ccBump` running BEFORE `ccDouble` overwrites: 2·5 + 3; the
plan's "swapped-callee refuted" twin made concrete). Two-line
corollary of the pinned readout. -/
theorem callchainNotThirteen :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel outEnv ccSeed ch (callchainDriver 5)
        = .ok (.normal σf, ch') →
      ¬ loadLoc σf (.base ⟨0⟩) = .ok (.int 13 .int) := by
  intro fuel ch σf ch' hrun h13
  have h14 := callchainReturnsFourteen fuel ch σf ch' hrun
  have := h14.symm.trans h13
  injection this with hval
  injection hval with hn _
  exact absurd hn (by decide)

end GoLean.Iris.Callchain
