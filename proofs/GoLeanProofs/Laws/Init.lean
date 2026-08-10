import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.MachineSound
import GoLeanProofs.Lifting
import GoLeanProofs.Inversions
import GoLeanProofs.Tactics.GoWalk

/-!
# Declaration law + witness
`x := default` — the CEK inline-declaration/allocation law.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **The declaration law `x := default`** (`Stmt.initialization`, the CEK
inline-declaration step): allocates a fresh cell at the parameter type's
default value and extends the *rest of the enclosing sequence*'s env with the
new binding. Like the call law, the continuation receives the freshly
allocated cell at a machine-chosen address (`∀ pa`). `hdef` is the
default-value fact, under the ghost state's type-environment pin —
required, not decoration: `defaultValue` resolves a `.defined` name
through `TypeEnv.lookup σ₁.types` and fails closed on an unknown one, so
the unpinned `∀ σ₁` form is FALSE at every named Go type and a law
carrying it would be vacuous there (`Specs/GoldenQuorumPin`'s
`typeEnv_pin_is_load_bearing`; premise widened 2026-07-31 for the
`main.Index`-typed declarations of the quorum lowering — strictly weaker,
so every existing caller keeps working). Witnesses: `wp_init_int`
(scalar, state-independent) and `wp_ackedIndex_body`'s
`idx : main.Index` declaration (named type, pin-dependent). -/
theorem wp_init {pid : String} {pty : Ty} {v : GoValue} {rest : List Stmt}
    {env k}
    (hdef : ∀ σ₁ : ExecState, σ₁.types = GoCoreGS.types GF →
      defaultValue σ₁ pty = .ok v) :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some pty, v⟩ : HeapCell) -∗
        WP (Config.next (.seq rest (env.declare pid (.base pa)) k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.initialization ⟨pid, pty⟩) env (.seq rest env k))
          @ s ; E {{ Φ }} := by
  iintro Hcont
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  have hstep : Step (.exec (.initialization ⟨pid, pty⟩) env (.seq rest env k)) σ₁
      (.next (.seq rest (env.declare pid (.base ⟨σ₁.nextAddr⟩)) k))
      { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, v⟩,
                nextAddr := σ₁.nextAddr + 1 } :=
    Step.initialization (hdef σ₁ htypes) (ExecState.alloc_eq σ₁ v (some pty))
  have hdet : ∀ c' s',
      Step (.exec (.initialization ⟨pid, pty⟩) env (.seq rest env k)) σ₁ c' s' →
      c' = Config.next (.seq rest (env.declare pid (.base ⟨σ₁.nextAddr⟩)) k) ∧
      s' = { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, v⟩,
                     nextAddr := σ₁.nextAddr + 1 } := by
    intro c' s' hst
    cases hst with
    | stmtOpFirst hplan => simp [stmtPlan] at hplan
    | stmtOpNullary hplan _ => simp [stmtPlan] at hplan
    | chanStFirst hplan => simp [chanPlan] at hplan
    | syncStFirst hplan => simp [syncPlan] at hplan
    | initialization hd ha =>
      rw [hdef σ₁ htypes] at hd
      injection hd with hv
      rw [← hv, ExecState.alloc_eq] at ha
      injection ha with hloc hst'
      rw [← hloc, ← hst']
      exact ⟨rfl, rfl⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], _, _, [], GoPrimStep.step hstep⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    obtain ⟨rfl, rfl⟩ := hdet _ _ st
    imod (genHeap_alloc (v := (⟨some pty, v⟩ : HeapCell)) hwf.fresh_get?)
      $$ Hσ with ⟨Hσ, Hpt, Htok⟩
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iapply (genHeapInterp_eqv
          (fun kk => (heapToMap_set_base σ₁.heap ⟨σ₁.nextAddr⟩ _ kk).symm)) $$ Hσ
      · ipureintro
        exact ⟨hfns, hmeths, htypes, hwf.alloc⟩
    · isplitl [Hpt Hcont]
      · iapply Hcont $$ %(⟨σ₁.nextAddr⟩ : Addr) Hpt
      · itrivial

/-- Witness for `wp_init`: `x := 0` at an int kind — the slice's `x := 0`.
Zero hypotheses (the int default is `0`, state-independently). -/
@[go_walk_law]
theorem wp_init_int {pid : String} {kind : IntKind} {rest : List Stmt} {env k} :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some (.int kind), .int 0 kind⟩ : HeapCell) -∗
        WP (Config.next (.seq rest (env.declare pid (.base pa)) k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.initialization ⟨pid, .int kind⟩) env (.seq rest env k))
          @ s ; E {{ Φ }} :=
  wp_init (fun _ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel])

/-- `var b bool` — zero hypotheses (the bool default is `false`,
state-independently). Deliberately NOT `@[go_walk_law]`-registered
(spec-parity slice 3, recorded in the slice note: registering it moved
the stopping points of the standing quorum walks — the law table is a
global tactic surface, so new laws stay unregistered unless every
consumer is re-validated); walks supply it with `go_walk_step`.
Witness: `GoLean.Iris.ImportedGoose.wp_golean_wrapper_body`'s
call-target declaration (`Specs/GooseParityKit.lean`). [S3 audit
correction: this docstring first claimed that witness while the kit
walk still used the generic `wp_init` inline — the sentence the
non-vacuity doctrine forbids; the kit now applies THIS law at that
step, making the citation true, and the pair is referenced in
`proofs/Audit.lean`'s witness registry.] -/
theorem wp_init_bool {pid : String} {rest : List Stmt} {env k} :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some .bool, .bool false⟩ : HeapCell) -∗
        WP (Config.next (.seq rest (env.declare pid (.base pa)) k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.initialization ⟨pid, .bool⟩) env (.seq rest env k))
          @ s ; E {{ Φ }} :=
  wp_init (fun _ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel])

/-- `var p *T` — zero hypotheses (the pointer default is `nil` at EVERY
pointee type, state-independently: `defaultValueFuel`'s `.pointer` arm
never looks at `t`). NOT table-registered, same reason as
`wp_init_bool` above; walks supply it with `go_walk_step`. Witness: the
imported-goose exemplar's `var $c2 **uint64` (spec-parity slice 3). -/
theorem wp_init_ptr {pid : String} {t : Ty} {rest : List Stmt} {env k} :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some (.pointer t), .nil⟩ : HeapCell) -∗
        WP (Config.next (.seq rest (env.declare pid (.base pa)) k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.initialization ⟨pid, .pointer t⟩) env (.seq rest env k))
          @ s ; E {{ Φ }} :=
  wp_init (fun _ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel])

end

end GoLean.Iris
