import GoLeanProofs.Specs.GooseParityKit
import GoLeanProofs.Specs.ImportedGooseBlock

/-!
# R3: semantics/block — `testExplicitBlockStmt` (spec-parity slice 3)

The imported goose oracle `testExplicitBlockStmt` (upstream
`testdata/examples/semantics/block.go` @ 3be88bbb; R1 green, R2 pinned
— `Specs/ImportedGooseBlock.lean`), walked with `go_walk` + the kit to
the D1 pair over the staleness-guarded lowering `blockLowered`.
block.go has NO `test_fun_ok` lemma at the pinned rev (upstream's
measured proved set is 28 of 36 stated — S3 audit correction; see
`docs/spec-parity-r3-manifest.md`) — this row is same-class coverage,
recorded as such in the manifest, not a parity row.

The program is the shadowing pin: an inner block redeclares `x`,
mutates the INNER one, and the verdict compares the untouched OUTER
`x` to its original value:

```go
func testExplicitBlockStmt() bool {
    x := 10
    { x := 11; x = x + 1 }   // shadows; inner x becomes 12
    return x == 10           // outer x — true
}
```
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface GoLean.Iris GoLean.Iris.ImportedGoose
open GoLean.ImportedGoose.SemanticsBlock

namespace GoLean.ImportedGoose.SemanticsBlock

set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-- The inner oracle's `Func` record, pinned by `rfl` below. -/
def explicitBlockFunc : Func :=
  { id := { key := "testExplicitBlockStmt" },
    args := #[],
    results := #[{ id := "$res0", typ := .bool }],
    body := .block
              #[]
              #[.seqn
                  #[.initialization { id := "x", typ := .int .int },
                    .assign (.var "x") (.intLit 10 .int)],
                .block
                  #[]
                  #[.seqn
                      #[.initialization { id := "x", typ := .int .int },
                        .assign (.var "x") (.intLit 11 .int)],
                    .assign (.var "x")
                      (.add (.var "x") (.intLit 1 .int))],
                .seqn
                  #[.assign (.var "$res0")
                      (.eqCmp (.int .int) (.var "x") (.intLit 10 .int)),
                    .returnStmt]],
    variadic := false,
    wrapper := false }

/-- The wrapper's `Func` record — body IS the kit shape. -/
def goleanExplicitBlockFunc : Func :=
  { id := { key := "goleanTestExplicitBlockStmt" },
    args := #[],
    results := #[{ id := "$res0", typ := .int .int }],
    body := goleanWrapperBody "$c0" ⟨"testExplicitBlockStmt"⟩,
    variadic := false,
    wrapper := false }

example : findFunctionIn? blockLowered.funcs ⟨"testExplicitBlockStmt"⟩
    = some explicitBlockFunc := rfl
example : findFunctionIn? blockLowered.funcs ⟨"goleanTestExplicitBlockStmt"⟩
    = some goleanExplicitBlockFunc := rfl

/-- The driver statement — the R1 row's subject (= the R2 pin's
`blockDriver`). -/
abbrev explicitBlockDriver : Stmt :=
  .call #[.var "r"] ⟨"goleanTestExplicitBlockStmt"⟩ #[]

/-- The kit seed at this program IS the existing R2 pin's seed. -/
example : importedSeed blockLowered = blockOut := rfl

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- Inner body walk: the shadowed inner `x` takes the writes; the outer
`x` still holds `10` at the verdict. -/
theorem wp_explicitBlock_body {ra : Addr} {k} :
    ra.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec explicitBlockFunc.body [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  simp only [explicitBlockFunc]
  -- outer `x := 10` up to the store (the int declaration walks itself:
  -- `wp_init_int` is table-registered)
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int 10 .int⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind,
        show IntKind.normalize .int 10 = 10 from by decide]))
  -- inner block, `x := 11` up to its store
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int 11 .int⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind,
        show IntKind.normalize .int 11 = 11 from by decide]))
  -- `x = x + 1` (inner): the add's APPLY walks itself (`go_walk_side`'s
  -- `rfl` computes pure int operators outright); only the store stops
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some (.int .int), .int 11 .int⟩)
    (newcell := ⟨some (.int .int), .int 12 .int⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind,
        show IntKind.normalize .int 12 = 12 from by decide]))
  -- the verdict: OUTER `x == 10` (the inner scope has popped)
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

theorem wp_explicitBlockDriver
    (hprog : GoCoreGS.prog GF = blockLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) importedCell0
      ⊢ WP (Config.exec explicitBlockDriver importedEnv .stop)
          {{ _v, embed (importedCellV 1) }} := by
  simp only [importedCell0, importedCellV, embed]
  iintro Hr
  iapply (wp_golean_driver (cname := "$c0")
    (wrapperFunc := goleanExplicitBlockFunc)
    (innerFunc := explicitBlockFunc)
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
    (Hinner := fun ra' k' => wp_explicitBlock_body))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply (wp_value' (v := ()))
  iexact Hr

end

theorem explicitBlockSpec :
    GoSpec blockLowered.typeDefs.toList blockLowered.funcs
      blockLowered.methods importedEnv importedCell0 explicitBlockDriver
      (importedCellV 1) := by
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  exact wp_explicitBlockDriver hprog hmeths

theorem explicitBlockSpecC :
    GoSpecC blockLowered.typeDefs.toList blockLowered.funcs
      blockLowered.methods importedEnv importedCell0 explicitBlockDriver
      (importedCellV 1) :=
  goSpecC_of_goSpec explicitBlockSpec

theorem explicitBlockReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel importedEnv (importedSeed blockLowered) ch
        explicitBlockDriver = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_readoutC explicitBlockSpec (by decide +kernel)

/-- P-S3-5 joint form (slice 6): completes-AND-verdict on the single
sequential carrier, from the R2 pin (`blockTerminates`) + the spec. -/
theorem explicitBlockTotalReadout :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel importedEnv (importedSeed blockLowered) ch
          explicitBlockDriver = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_totalReadout explicitBlockSpec (by decide +kernel)
    (by exact blockTerminates)

/-- The POOL-carrier ∃-completion member for `explicitBlockSpecC`
(the D1-BOTH convention's pool-carrier ∃-completion member for this
row's `GoSpecC` export; sequential completion lifted by
conservation). -/
theorem explicitBlockTerminatesNormallyC :
    TerminatesNormallyC importedEnv (importedSeed blockLowered) explicitBlockDriver :=
  goSpec_seeded_terminatesNormallyC explicitBlockSpec (by decide +kernel)
    (by exact blockTerminates)

/-- The D1 convention's SEQUENTIAL-carrier completion member for `explicitBlockSpec` — the
completion half of the row's `TotalReadout`, projected as a named
theorem. -/
theorem explicitBlockTerminatesNormally :
    TerminatesNormally importedEnv (importedSeed blockLowered) explicitBlockDriver := by
  obtain ⟨N, h⟩ := explicitBlockTotalReadout
  exact ⟨N, fun fuel hf ch =>
    let ⟨σf, ch', hr, _⟩ := h fuel hf ch
    ⟨σf, ch', hr⟩⟩

end GoLean.ImportedGoose.SemanticsBlock
