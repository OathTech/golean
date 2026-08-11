import GoLeanProofs.Specs.GooseParityKit
import GoLeanProofs.Specs.ImportedGooseVars
import GoLeanProofs.Laws.StmtOps

/-!
# R3 over imported semantics/vars (spec-parity slice 6 — the P-S3-2
driver tranche)

Upstream has NO `test_fun_ok` statements for vars.go (no vars.v in
semantics_proof/ @ 43d4efa) — these are same-class COVERAGE rows, not
parity rows. Two of the unit's three oracles walk with existing laws
and ship the full D1 pair + the slice-6 joint form over the
staleness-guarded pinned lowering (`Specs/ImportedGooseVars.lean`,
ci step 3a2):

* `testPointerAssignment` — proved (`pointerAssignment*` below);
* `testAnonymousAssign` — proved (`anonymousAssign*` below);
* `testAddressOfLocal` — **OUT-OF-TRANCHE, recorded**: its verdict is
  the short-circuit `Expr.and` (`x && *xptr`), the SAME recorded law
  gap that blocks `testInterfaceNilWithType` (manifest row) — a NEW
  law family, which the tranche's hard bound forbids chasing. Its R2
  pins (Terminates + readout) ARE in the pin module; only the R3 walk
  is blocked. Visible row in the manifest, never a silent skip.

NOT designated statements.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface GoLean.Iris GoLean.Iris.ImportedGoose

namespace GoLean.ImportedGoose.SemanticsVars

set_option maxRecDepth 1000000
-- Uniform simp sets across law variants (the golden-walk convention).
set_option linter.unusedSimpArgs false

/-- The kit seed at this program IS the pin module's seed. -/
example : importedSeed varsLowered = varsOut := rfl

/-! ### testPointerAssignment (`var x bool; x = true; return x`) -/

def pointerAssignmentFunc : Func :=
  { id := { key := "testPointerAssignment" },
    args := #[],
    results := #[{ id := "$res0", typ := .bool }],
    body := .block
              #[]
              #[.seqn #[.initialization { id := "x", typ := .bool }],
                .seqn #[.assign (.var "x") (.boolLit true)],
                .seqn
                  #[.assign (.var "$res0") (.var "x"),
                    .returnStmt]],
    variadic := false,
    wrapper := false }

def goleanPointerAssignmentFunc : Func :=
  { id := { key := "goleanTestPointerAssignment" },
    args := #[],
    results := #[{ id := "$res0", typ := .int .int }],
    body := goleanWrapperBody "$c0" ⟨"testPointerAssignment"⟩,
    variadic := false,
    wrapper := false }

example : findFunctionIn? varsLowered.funcs ⟨"testPointerAssignment"⟩
    = some pointerAssignmentFunc := rfl
example : findFunctionIn? varsLowered.funcs ⟨"goleanTestPointerAssignment"⟩
    = some goleanPointerAssignmentFunc := rfl

abbrev pointerAssignmentDriver : Stmt :=
  .call #[.var "r"] ⟨"goleanTestPointerAssignment"⟩ #[]

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- Inner body walk: declare a bool, store `true`, read it back into
the verdict. -/
theorem wp_pointerAssignment_body {ra : Addr} {k} :
    ra.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec pointerAssignmentFunc.body
              [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  simp only [pointerAssignmentFunc]
  go_walk
  go_walk_step wp_init_bool
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some .bool, .bool false⟩)
    (newcell := ⟨some .bool, .bool true⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some .bool, .bool false⟩)
    (newcell := ⟨some .bool, .bool true⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  go_walk_finish Hcont

theorem wp_pointerAssignmentDriver
    (hprog : GoCoreGS.prog GF = varsLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) importedCell0
      ⊢ WP (Config.exec pointerAssignmentDriver importedEnv .stop)
          {{ _v, embed (importedCellV 1) }} := by
  simp only [importedCell0, importedCellV, embed]
  iintro Hr
  iapply (wp_golean_driver (cname := "$c0")
    (wrapperFunc := goleanPointerAssignmentFunc)
    (innerFunc := pointerAssignmentFunc)
    (w := .int 0 .int)
    (hr := rfl)
    (hcname := by decide)
    (hfindW := by rw [hprog]; rfl)
    (hargsW := rfl) (hresW := rfl) (hbodyW := rfl)
    (hnodispW := fun σ h => by
      simp [dynamicDispatch?, methodInfoByFuncId?, h, hmeths,
        Bind.bind, Except.bind])
    (hfind := by rw [hprog]; rfl)
    (hargs := rfl) (hres := rfl)
    (hnodisp := fun σ h => by
      simp [dynamicDispatch?, methodInfoByFuncId?, h, hmeths,
        Bind.bind, Except.bind])
    (Hinner := fun ra' k' => wp_pointerAssignment_body))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply (wp_value' (v := ()))
  iexact Hr

end

theorem pointerAssignmentSpec :
    GoSpec varsLowered.typeDefs.toList varsLowered.funcs
      varsLowered.methods importedEnv importedCell0
      pointerAssignmentDriver (importedCellV 1) := by
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  exact wp_pointerAssignmentDriver hprog hmeths

/-- D1 form 1 (coverage row — no upstream statement). -/
theorem pointerAssignmentSpecC :
    GoSpecC varsLowered.typeDefs.toList varsLowered.funcs
      varsLowered.methods importedEnv importedCell0
      pointerAssignmentDriver (importedCellV 1) :=
  goSpecC_of_goSpec pointerAssignmentSpec

/-- D1 form 2 — the pool-carrier first-order readout twin. -/
theorem pointerAssignmentReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel importedEnv (importedSeed varsLowered) ch
        pointerAssignmentDriver = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_readoutC pointerAssignmentSpec (by decide +kernel)

/-- P-S3-5 joint form. -/
theorem pointerAssignmentTotalReadout :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel importedEnv (importedSeed varsLowered) ch
          pointerAssignmentDriver = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_totalReadout pointerAssignmentSpec (by decide +kernel)
    (by exact testPointerAssignmentTerminates)

/-- The POOL-carrier ∃-completion member for `pointerAssignmentSpecC`
(channel-logic S1 audit round 2 — the completion-pin gate's pin for
this row's program; sequential completion lifted by conservation). -/
theorem pointerAssignmentTerminatesNormallyC :
    TerminatesNormallyC importedEnv (importedSeed varsLowered) pointerAssignmentDriver :=
  goSpec_seeded_terminatesNormallyC pointerAssignmentSpec (by decide +kernel)
    (by exact testPointerAssignmentTerminates)

/-! ### testAnonymousAssign (`_ = uint64(1) + uint64(2); return true` —
the blank-assign lowers to a `$blank0` local; the sum is
constant-folded to `3` by the frontend) -/

def anonymousAssignFunc : Func :=
  { id := { key := "testAnonymousAssign" },
    args := #[],
    results := #[{ id := "$res0", typ := .bool }],
    body := .block
              #[]
              #[.seqn
                  #[.initialization { id := "$blank0", typ := .int .uint64 },
                    .assign (.var "$blank0") (.intLit 3 .uint64)],
                .seqn
                  #[.assign (.var "$res0") (.boolLit true),
                    .returnStmt]],
    variadic := false,
    wrapper := false }

def goleanAnonymousAssignFunc : Func :=
  { id := { key := "goleanTestAnonymousAssign" },
    args := #[],
    results := #[{ id := "$res0", typ := .int .int }],
    body := goleanWrapperBody "$c2" ⟨"testAnonymousAssign"⟩,
    variadic := false,
    wrapper := false }

example : findFunctionIn? varsLowered.funcs ⟨"testAnonymousAssign"⟩
    = some anonymousAssignFunc := rfl
example : findFunctionIn? varsLowered.funcs ⟨"goleanTestAnonymousAssign"⟩
    = some goleanAnonymousAssignFunc := rfl

abbrev anonymousAssignDriver : Stmt :=
  .call #[.var "r"] ⟨"goleanTestAnonymousAssign"⟩ #[]

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- Inner body walk: the blank local takes the folded constant, the
verdict is `true`. -/
theorem wp_anonymousAssign_body {ra : Addr} {k} :
    ra.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec anonymousAssignFunc.body
              [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  simp only [anonymousAssignFunc]
  go_walk
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.int .uint64), .int 0 .uint64⟩)
    (newcell := ⟨some (.int .uint64), .int 3 .uint64⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind,
        show IntKind.normalize .uint64 3 = 3 from by decide]))
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some .bool, .bool false⟩)
    (newcell := ⟨some .bool, .bool true⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  go_walk_finish Hcont

theorem wp_anonymousAssignDriver
    (hprog : GoCoreGS.prog GF = varsLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) importedCell0
      ⊢ WP (Config.exec anonymousAssignDriver importedEnv .stop)
          {{ _v, embed (importedCellV 1) }} := by
  simp only [importedCell0, importedCellV, embed]
  iintro Hr
  iapply (wp_golean_driver (cname := "$c2")
    (wrapperFunc := goleanAnonymousAssignFunc)
    (innerFunc := anonymousAssignFunc)
    (w := .int 0 .int)
    (hr := rfl)
    (hcname := by decide)
    (hfindW := by rw [hprog]; rfl)
    (hargsW := rfl) (hresW := rfl) (hbodyW := rfl)
    (hnodispW := fun σ h => by
      simp [dynamicDispatch?, methodInfoByFuncId?, h, hmeths,
        Bind.bind, Except.bind])
    (hfind := by rw [hprog]; rfl)
    (hargs := rfl) (hres := rfl)
    (hnodisp := fun σ h => by
      simp [dynamicDispatch?, methodInfoByFuncId?, h, hmeths,
        Bind.bind, Except.bind])
    (Hinner := fun ra' k' => wp_anonymousAssign_body))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply (wp_value' (v := ()))
  iexact Hr

end

theorem anonymousAssignSpec :
    GoSpec varsLowered.typeDefs.toList varsLowered.funcs
      varsLowered.methods importedEnv importedCell0
      anonymousAssignDriver (importedCellV 1) := by
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  exact wp_anonymousAssignDriver hprog hmeths

/-- D1 form 1 (coverage row — no upstream statement). -/
theorem anonymousAssignSpecC :
    GoSpecC varsLowered.typeDefs.toList varsLowered.funcs
      varsLowered.methods importedEnv importedCell0
      anonymousAssignDriver (importedCellV 1) :=
  goSpecC_of_goSpec anonymousAssignSpec

/-- D1 form 2 — the pool-carrier first-order readout twin. -/
theorem anonymousAssignReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel importedEnv (importedSeed varsLowered) ch
        anonymousAssignDriver = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_readoutC anonymousAssignSpec (by decide +kernel)

/-- P-S3-5 joint form. -/
theorem anonymousAssignTotalReadout :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel importedEnv (importedSeed varsLowered) ch
          anonymousAssignDriver = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_totalReadout anonymousAssignSpec (by decide +kernel)
    (by exact testAnonymousAssignTerminates)

/-- The POOL-carrier ∃-completion member for `anonymousAssignSpecC`
(channel-logic S1 audit round 2 — the completion-pin gate's pin for
this row's program; sequential completion lifted by conservation). -/
theorem anonymousAssignTerminatesNormallyC :
    TerminatesNormallyC importedEnv (importedSeed varsLowered) anonymousAssignDriver :=
  goSpec_seeded_terminatesNormallyC anonymousAssignSpec (by decide +kernel)
    (by exact testAnonymousAssignTerminates)

end GoLean.ImportedGoose.SemanticsVars
