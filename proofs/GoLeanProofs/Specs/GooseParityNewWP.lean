import GoLeanProofs.Specs.GooseParityKit
import GoLeanProofs.Specs.ImportedGooseNew
import GoLeanProofs.Laws.StmtOps

/-!
# R3 over imported semantics/new (spec-parity slice 6 — the P-S3-2
driver tranche's first backfilled unit)

Both oracles are UPSTREAM-QED (`wp_testNilDefault` new.v:10 Qed :13,
`wp_testNilVal` new.v:15 Qed :19 @ 43d4efa) — genuine parity rows.
Per oracle, the D1 pair over the staleness-guarded pinned lowering
(`Specs/ImportedGooseNew.lean`, ci step 3a2) + the slice-6 joint form:
`GoSpecC` at full `InitialSplit` strength (sequential-degenerate
lane), the pool-carrier first-order readout twin, and the P-S3-5
single-carrier completes-AND-verdict composition with the R2 pin.
Walks are `go_walk`-driven with the recorded side-goal supplies only
(the S3 driver pattern; nothing registered into the law table).
NOT designated statements.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface GoLean.Iris GoLean.Iris.ImportedGoose

namespace GoLean.ImportedGoose.SemanticsNew

set_option maxRecDepth 1000000
-- Uniform simp sets across law variants (the golden-walk convention).
set_option linter.unusedSimpArgs false

/-- `*int` — both oracles' local pointer type. -/
private abbrev ptrint : Ty := .pointer (.int .int)

/-- The kit seed at this program IS the pin module's seed. -/
example : importedSeed newLowered = newOut := rfl

/-! ### testNilDefault (`x := new(int); *x = 1; return true`) -/

def nilDefaultFunc : Func :=
  { id := { key := "testNilDefault" },
    args := #[],
    results := #[{ id := "$res0", typ := .bool }],
    body := .block
              #[]
              #[.seqn
                  #[.initialization { id := "$c0", typ := ptrint },
                    .newValue (.var "$c0")
                      (.defaultValue (.int .int)) (some (.int .int))],
                .seqn
                  #[.initialization { id := "x", typ := ptrint },
                    .assign (.var "x") (.var "$c0")],
                .seqn
                  #[.assign (.addr (.var "x")) (.intLit 1 .int)],
                .seqn
                  #[.assign (.var "$res0") (.boolLit true),
                    .returnStmt]],
    variadic := false,
    wrapper := false }

def goleanNilDefaultFunc : Func :=
  { id := { key := "goleanTestNilDefault" },
    args := #[],
    results := #[{ id := "$res0", typ := .int .int }],
    body := goleanWrapperBody "$c2" ⟨"testNilDefault"⟩,
    variadic := false,
    wrapper := false }

example : findFunctionIn? newLowered.funcs ⟨"testNilDefault"⟩
    = some nilDefaultFunc := rfl
example : findFunctionIn? newLowered.funcs ⟨"goleanTestNilDefault"⟩
    = some goleanNilDefaultFunc := rfl

abbrev nilDefaultDriver : Stmt :=
  .call #[.var "r"] ⟨"goleanTestNilDefault"⟩ #[]

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- Inner body walk: allocate an `int` cell at its default, point `x`
at it, store `1` through the pointer, verdict `true`. -/
theorem wp_nilDefault_body {ra : Addr} {k} :
    ra.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec nilDefaultFunc.body [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  simp only [nilDefaultFunc]
  go_walk
  go_walk_step wp_init_ptr
  go_walk
  go_walk_step (wp_eval_strict_nullary_pure (v := .int 0 .int)
    (hplan := rfl)
    (happly := fun σ => by
      simp [applyStrictOp, defaultValue, defaultValueFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  go_walk_step (wp_new_value (oldcell := ⟨some ptrint, .nil⟩)
    (newcell := fun fa => ⟨some ptrint, .addr (.base fa)⟩)
    (hstore := fun σ fa _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind])) as [fa, Hf, Hc]
  go_walk
  go_walk_step wp_init_ptr
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some ptrint, .nil⟩)
    (newcell := ⟨some ptrint, .addr (.base fa)⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  go_walk
  go_walk_step (wp_assign_store (a := fa)
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int 1 .int⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind,
        show IntKind.normalize .int 1 = 1 from by decide]))
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some .bool, .bool false⟩)
    (newcell := ⟨some .bool, .bool true⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  go_walk_finish Hcont

theorem wp_nilDefaultDriver
    (hprog : GoCoreGS.prog GF = newLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) importedCell0
      ⊢ WP (Config.exec nilDefaultDriver importedEnv .stop)
          {{ _v, embed (importedCellV 1) }} := by
  simp only [importedCell0, importedCellV, embed]
  iintro Hr
  iapply (wp_golean_driver (cname := "$c2")
    (wrapperFunc := goleanNilDefaultFunc) (innerFunc := nilDefaultFunc)
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
    (Hinner := fun ra' k' => wp_nilDefault_body))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply (wp_value' (v := ()))
  iexact Hr

end

theorem nilDefaultSpec :
    GoSpec newLowered.typeDefs.toList newLowered.funcs newLowered.methods
      importedEnv importedCell0 nilDefaultDriver (importedCellV 1) := by
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  exact wp_nilDefaultDriver hprog hmeths

/-- D1 form 1 (a genuine parity row — upstream Qed). -/
theorem nilDefaultSpecC :
    GoSpecC newLowered.typeDefs.toList newLowered.funcs newLowered.methods
      importedEnv importedCell0 nilDefaultDriver (importedCellV 1) :=
  goSpecC_of_goSpec nilDefaultSpec

/-- D1 form 2 — the pool-carrier first-order readout twin. -/
theorem nilDefaultReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel importedEnv (importedSeed newLowered) ch
        nilDefaultDriver = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_readoutC nilDefaultSpec (by decide +kernel)

/-- P-S3-5 joint form: completes-AND-verdict on the single sequential
carrier, from the R2 pin + the spec. -/
theorem nilDefaultTotalReadout :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel importedEnv (importedSeed newLowered) ch
          nilDefaultDriver = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_totalReadout nilDefaultSpec (by decide +kernel)
    (by exact testNilDefaultTerminates)

/-- The POOL-carrier ∃-completion member for `nilDefaultSpecC`
(the D1-BOTH convention's pool-carrier ∃-completion member for this
row's `GoSpecC` export; sequential completion lifted by
conservation). -/
theorem nilDefaultTerminatesNormallyC :
    TerminatesNormallyC importedEnv (importedSeed newLowered) nilDefaultDriver :=
  goSpec_seeded_terminatesNormallyC nilDefaultSpec (by decide +kernel)
    (by exact testNilDefaultTerminates)

/-- The D1 convention's SEQUENTIAL-carrier completion member for `nilDefaultSpec` — the
completion half of the row's `TotalReadout`, projected as a named
theorem. -/
theorem nilDefaultTerminatesNormally :
    TerminatesNormally importedEnv (importedSeed newLowered) nilDefaultDriver := by
  obtain ⟨N, h⟩ := nilDefaultTotalReadout
  exact ⟨N, fun fuel hf ch =>
    let ⟨σf, ch', hr, _⟩ := h fuel hf ch
    ⟨σf, ch', hr⟩⟩

/-! ### testNilVal (`x := new(3); return *x == 3` — goose's
value-carrying `new` extension, lowered as `newValue` with a literal
operand) -/

def nilValFunc : Func :=
  { id := { key := "testNilVal" },
    args := #[],
    results := #[{ id := "$res0", typ := .bool }],
    body := .block
              #[]
              #[.seqn
                  #[.initialization { id := "$c1", typ := ptrint },
                    .newValue (.var "$c1")
                      (.intLit 3 .int) (some (.int .int))],
                .seqn
                  #[.initialization { id := "x", typ := ptrint },
                    .assign (.var "x") (.var "$c1")],
                .seqn
                  #[.assign (.var "$res0")
                      (.eqCmp (.int .int)
                        (.deref (.var "x") (.int .int))
                        (.intLit 3 .int)),
                    .returnStmt]],
    variadic := false,
    wrapper := false }

def goleanNilValFunc : Func :=
  { id := { key := "goleanTestNilVal" },
    args := #[],
    results := #[{ id := "$res0", typ := .int .int }],
    body := goleanWrapperBody "$c3" ⟨"testNilVal"⟩,
    variadic := false,
    wrapper := false }

example : findFunctionIn? newLowered.funcs ⟨"testNilVal"⟩
    = some nilValFunc := rfl
example : findFunctionIn? newLowered.funcs ⟨"goleanTestNilVal"⟩
    = some goleanNilValFunc := rfl

abbrev nilValDriver : Stmt :=
  .call #[.var "r"] ⟨"goleanTestNilVal"⟩ #[]

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- Inner body walk: allocate an `int` cell holding `3`, point `x` at
it, read it back through the pointer, compare to `3` (`true`). -/
theorem wp_nilVal_body {ra : Addr} {k} :
    ra.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec nilValFunc.body [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  simp only [nilValFunc]
  go_walk
  go_walk_step wp_init_ptr
  go_walk
  go_walk_step (wp_new_value (oldcell := ⟨some ptrint, .nil⟩)
    (newcell := fun fa => ⟨some ptrint, .addr (.base fa)⟩)
    (hstore := fun σ fa _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind])) as [fa, Hf, Hc]
  go_walk
  go_walk_step wp_init_ptr
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some ptrint, .nil⟩)
    (newcell := ⟨some ptrint, .addr (.base fa)⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  go_walk
  go_walk_step (wp_strict_apply_pure (out := .bool true)
    (happly := fun σ => by
      simp [applyStrictOp, valueEq, valueEqFuel, typeResolutionFuel,
        Bind.bind, Except.bind]))
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some .bool, .bool false⟩)
    (newcell := ⟨some .bool, .bool true⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  go_walk_finish Hcont

theorem wp_nilValDriver
    (hprog : GoCoreGS.prog GF = newLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) importedCell0
      ⊢ WP (Config.exec nilValDriver importedEnv .stop)
          {{ _v, embed (importedCellV 1) }} := by
  simp only [importedCell0, importedCellV, embed]
  iintro Hr
  iapply (wp_golean_driver (cname := "$c3")
    (wrapperFunc := goleanNilValFunc) (innerFunc := nilValFunc)
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
    (Hinner := fun ra' k' => wp_nilVal_body))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply (wp_value' (v := ()))
  iexact Hr

end

theorem nilValSpec :
    GoSpec newLowered.typeDefs.toList newLowered.funcs newLowered.methods
      importedEnv importedCell0 nilValDriver (importedCellV 1) := by
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  exact wp_nilValDriver hprog hmeths

/-- D1 form 1 (a genuine parity row — upstream Qed). -/
theorem nilValSpecC :
    GoSpecC newLowered.typeDefs.toList newLowered.funcs newLowered.methods
      importedEnv importedCell0 nilValDriver (importedCellV 1) :=
  goSpecC_of_goSpec nilValSpec

/-- D1 form 2 — the pool-carrier first-order readout twin. -/
theorem nilValReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel importedEnv (importedSeed newLowered) ch
        nilValDriver = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_readoutC nilValSpec (by decide +kernel)

/-- P-S3-5 joint form. -/
theorem nilValTotalReadout :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel importedEnv (importedSeed newLowered) ch
          nilValDriver = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_totalReadout nilValSpec (by decide +kernel)
    (by exact testNilValTerminates)

/-- The POOL-carrier ∃-completion member for `nilValSpecC`
(the D1-BOTH convention's pool-carrier ∃-completion member for this
row's `GoSpecC` export; sequential completion lifted by
conservation). -/
theorem nilValTerminatesNormallyC :
    TerminatesNormallyC importedEnv (importedSeed newLowered) nilValDriver :=
  goSpec_seeded_terminatesNormallyC nilValSpec (by decide +kernel)
    (by exact testNilValTerminates)

/-- The D1 convention's SEQUENTIAL-carrier completion member for `nilValSpec` — the
completion half of the row's `TotalReadout`, projected as a named
theorem. -/
theorem nilValTerminatesNormally :
    TerminatesNormally importedEnv (importedSeed newLowered) nilValDriver := by
  obtain ⟨N, h⟩ := nilValTotalReadout
  exact ⟨N, fun fuel hf ch =>
    let ⟨σf, ch', hr, _⟩ := h fuel hf ch
    ⟨σf, ch', hr⟩⟩

end GoLean.ImportedGoose.SemanticsNew
