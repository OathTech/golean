import GoLeanProofs.Specs.GooseParityKit
import GoLeanProofs.Specs.ImportedGooseNil
import GoLeanProofs.Laws.StmtOps

/-!
# The R3 exemplar: `testCompareNilToNil` (spec-parity slice 3, 2026-08-10)

Design of record: `docs/2026-08-10_wp-walk-driver.md` §1. The imported
goose oracle `testCompareNilToNil` (upstream
`testdata/examples/semantics/nil.go` @ 3be88bbb — one of Perennial's 37
PROVED `test_fun_ok` oracles, `wp_testCompareNilToNil` in
`semantics_proof/nil.v` @ 43d4efab), hand-proven end-to-end through the
laws spine to the full D1 pair:

* `compareNilToNilSpecC` — the designated-shape triple: `GoSpecC`
  `{r ↦ 0} r = goleanTestCompareNilToNil() {r ↦ 1}` at full
  `InitialSplit` strength (sequential-degenerate lane, via
  `goSpecC_of_goSpec`);
* `compareNilToNilReadoutC` — the first-order readout twin on the same
  pool carrier (interpreter vocabulary only).

Both are stated against `nilLowered`, the frontend's ACTUAL lowering of
the imported case (staleness-guarded, ci step 1c5). The per-program
content is exactly `wp_compareNil_body` — the inner body's walk; the
wrapper, driver, exit pipe, pool transfer, and readout derivation are
the once-proven kit (`Specs/GooseParityKit.lean`).

Designation status: CANDIDATES only (charter D3 is curated —
user-owned at the arc-end merge); nothing here joins
`proofs/Audit.lean`'s designated list in this slice.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface GoLean.Iris GoLean.Iris.ImportedGoose
open GoLean.ImportedGoose.SemanticsNil

namespace GoLean.ImportedGoose.SemanticsNil

set_option maxRecDepth 1000000
-- Uniform simp sets across law variants (the golden-walk convention).
set_option linter.unusedSimpArgs false

/-- `*uint64` — the allocated cell's type. -/
private abbrev ptr64 : Ty := .pointer (.int .uint64)

/-- `**uint64` — the local variables' type. -/
private abbrev ptrptr64 : Ty := .pointer ptr64

/-- The inner oracle's `Func` record, verbatim from the pinned lowering
(the `example` pin below ties it by `rfl` — a lowering drift breaks it
loudly, after ci 1c5 has already caught the term drift). -/
def compareNilFunc : Func :=
  { id := { key := "testCompareNilToNil" },
    args := #[],
    results := #[{ id := "$res0", typ := .bool }],
    body := .block
              #[]
              #[.seqn
                  #[.initialization { id := "$c2", typ := ptrptr64 },
                    .newValue (.var "$c2") (.defaultValue ptr64) (some ptr64)],
                .seqn
                  #[.initialization { id := "s", typ := ptrptr64 },
                    .assign (.var "s") (.var "$c2")],
                .seqn
                  #[.assign (.var "$res0")
                      (.eqCmp ptr64 (.deref (.var "s") ptr64) (.nil none)),
                    .returnStmt]],
    variadic := false,
    wrapper := false }

/-- The wrapper's `Func` record — its body IS the kit's
`goleanWrapperBody` at this oracle's names, so the `rfl` pin below also
certifies the wrapper-shape identity the kit walk relies on. -/
def goleanCompareNilFunc : Func :=
  { id := { key := "goleanTestCompareNilToNil" },
    args := #[],
    results := #[{ id := "$res0", typ := .int .int }],
    body := goleanWrapperBody "$c6" ⟨"testCompareNilToNil"⟩,
    variadic := false,
    wrapper := false }

/-- The lowering pin for the inner oracle. -/
example : findFunctionIn? nilLowered.funcs ⟨"testCompareNilToNil"⟩
    = some compareNilFunc := rfl

/-- The lowering pin for the wrapper (incl. wrapper-shape identity). -/
example : findFunctionIn? nilLowered.funcs ⟨"goleanTestCompareNilToNil"⟩
    = some goleanCompareNilFunc := rfl

/-- The driver statement — the R1 differential row's subject, and the
statement every theorem below is about. -/
abbrev compareNilDriver : Stmt :=
  .call #[.var "r"] ⟨"goleanTestCompareNilToNil"⟩ #[]

/-- The kit seed at this program IS the existing R2 pin's seed. -/
example : importedSeed nilLowered = nilOut := rfl

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **The inner body walk** (the exemplar's per-program content):

```go
s := new(*uint64)   // $c2 = new(*uint64); s := $c2
return *s == nil    // $res0 = (*s == nil); return
```

declare `$c2`, allocate the `*uint64` cell at its default (`nil`),
point `$c2` at it, copy into `s`, read `*s` back (`nil`), compare to
`nil` (`true`), write the verdict into the pinned bool result cell,
return. The dead locals (`$c2`, `s`, the allocated cell) are dropped
(affine). -/
theorem wp_compareNil_body {ra : Addr} {k} :
    ra.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec compareNilFunc.body [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  simp only [compareNilFunc]
  -- the walk: block/seq up to the `$c2` declaration
  go_walk
  go_walk_step wp_init_ptr
  -- the `new(*uint64)` operand walk up to the default-value operand
  -- (a nullary strict form whose `∀σ` apply fact the walk cannot
  -- discharge mechanically — a side-goal site by design)
  go_walk
  go_walk_step (wp_eval_strict_nullary_pure (v := .nil) (hplan := rfl)
    (happly := fun σ => by
      simp [applyStrictOp, defaultValue, defaultValueFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  -- the allocate-and-store step. `fa` names the fresh cell.
  go_walk_step (wp_new_value (oldcell := ⟨some ptrptr64, .nil⟩)
    (newcell := fun fa => ⟨some ptrptr64, .addr (.base fa)⟩)
    (hstore := fun σ fa _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind])) as [fa, Hf, Hc]
  -- `var s; s = $c2` up to the pointer-cell store
  go_walk
  go_walk_step wp_init_ptr
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some ptrptr64, .nil⟩)
    (newcell := ⟨some ptrptr64, .addr (.base fa)⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  -- `$res0 = (*s == nil)`: the deref chain, then the comparison's apply
  go_walk
  go_walk_step (wp_strict_apply_pure (out := .bool true)
    (happly := fun σ => by
      simp [applyStrictOp, valueEq, valueEqFuel, typeResolutionFuel,
        Bind.bind, Except.bind]))
  go_walk
  -- the verdict store into the bool result cell
  go_walk_step (wp_assign_store (oldcell := ⟨some .bool, .bool false⟩)
    (newcell := ⟨some .bool, .bool true⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  -- `return`: unwind to the frame and close with the continuation
  go_walk_finish Hcont

/-- The HAND walk of the same body — the exemplar's first, law-by-law
derivation (spec-parity slice 3 phase 1; the tactic-driven proof above
replaced it as `wp_compareNil_body`'s proof in phase 2 with the
statement byte-identical — this copy is kept as the walk-architecture
witness at full detail, exactly the modality-dance shape every law
composes at). -/
theorem wp_compareNil_body_hand {ra : Addr} {k} :
    ra.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec compareNilFunc.body [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  simp only [compareNilFunc]
  iapply wp_block_nil
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc1
  simp only [List.toList_toArray]
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc2
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc3
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc4
  -- `var $c2 **uint64` (default nil)
  iapply (wp_init (v := .nil) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %ca Hc
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc5
  -- `$c2 = new(*uint64)`: target address, default operand, one
  -- allocate-and-store step
  iapply (wp_stmt_op_first (hplan := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc6
  iapply (wp_eval_ref (loc := .base ca) (hres := by
    simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
      Scope.lookup]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc7
  iapply (wp_stmt_op_shift_target (hnt := by simp) (hloc := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc8
  iapply (wp_eval_strict_nullary_pure (v := .nil) (hplan := rfl)
    (happly := fun σ => by
      simp [applyStrictOp, defaultValue, defaultValueFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc9
  iapply (wp_new_value (a := ca) (oldcell := ⟨some ptrptr64, .nil⟩)
    (newcell := fun fa => ⟨some ptrptr64, .addr (.base fa)⟩)
    (hstore := fun σ fa _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  isplitl [Hc]
  · iexact Hc
  iintro %fa ⟨Hf, Hc⟩
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc10
  -- second group: `var s **uint64; s = $c2`
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc11
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc12
  iapply (wp_init (v := .nil) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %sa Hs
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc13
  -- `s = $c2`
  iapply (wp_assign_start (e := .ref "s") (sh := .chain []) (ops := [])
    (hplan := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc14
  iapply (wp_eval_ref (loc := .base sa) (hres := by
    simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
      Scope.lookup]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc15
  iapply (wp_tgtop_rhs (r := .chain (.addr (.base sa)) [] []) (hcomp := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc16
  iapply (wp_eval_var (a := ca) (cell := ⟨some ptrptr64, .addr (.base fa)⟩)
    (hres := by
      simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
        Scope.lookup]))
  isplitl [Hc]
  · iexact Hc
  iintro Hc
  iapply wp_rhs_stores_vals
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc17
  simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
  iapply (wp_assign_store (a := sa) (oldcell := ⟨some ptrptr64, .nil⟩)
    (newcell := ⟨some ptrptr64, .addr (.base fa)⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  isplitl [Hs]
  · iexact Hs
  iintro Hs
  iapply wp_stores_done_nil
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc18
  -- third group: `$res0 = (*s == nil); return`
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc19
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc20
  iapply (wp_assign_start (e := .ref "$res0") (sh := .chain []) (ops := [])
    (hplan := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc21
  iapply (wp_eval_ref (loc := .base ra) (hres := by
    simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
      Scope.lookup]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc22
  iapply (wp_tgtop_rhs (r := .chain (.addr (.base ra)) [] []) (hcomp := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc23
  -- `*s == nil`: enter the comparison, then the deref chain
  iapply (wp_eval_strict (op := .eqCmp ptr64)
    (e₁ := .deref (.var "s") ptr64) (rest := [.nil none]) (hplan := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc24
  iapply (wp_eval_strict (op := .deref ptr64) (e₁ := .var "s")
    (rest := []) (hplan := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc25
  iapply (wp_eval_var (a := sa) (cell := ⟨some ptrptr64, .addr (.base fa)⟩)
    (hres := by
      simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
        Scope.lookup]))
  isplitl [Hs]
  · iexact Hs
  iintro Hs
  iapply (wp_strict_apply_deref (a := fa) (cell := ⟨some ptr64, .nil⟩))
  isplitl [Hf]
  · iexact Hf
  iintro Hf
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc26
  iapply (wp_eval_strict_nullary_pure (v := .nil) (hplan := rfl)
    (happly := fun σ => rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc27
  iapply (wp_strict_apply_pure (out := .bool true)
    (happly := fun σ => by
      simp [applyStrictOp, valueEq, valueEqFuel, typeResolutionFuel,
        Bind.bind, Except.bind]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc28
  iapply wp_rhs_stores_vals
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc29
  simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
  iapply (wp_assign_store (a := ra) (oldcell := ⟨some .bool, .bool false⟩)
    (newcell := ⟨some .bool, .bool true⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply wp_stores_done_nil
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc30
  iapply wp_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc31
  iapply wp_seq_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc32
  iapply Hcont $$ Hr

/-- **The driver, exit form**:
`{r ↦ 0} r = goleanTestCompareNilToNil() {r ↦ 1}` as the WP entailment
`goSpec_of_wp` consumes — the kit's wrapper/driver walks over
`wp_compareNil_body`. -/
theorem wp_compareNilDriver
    (hprog : GoCoreGS.prog GF = nilLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) importedCell0
      ⊢ WP (Config.exec compareNilDriver importedEnv .stop)
          {{ _v, embed (importedCellV 1) }} := by
  simp only [importedCell0, importedCellV, embed]
  iintro Hr
  iapply (wp_golean_driver (cname := "$c6")
    (wrapperFunc := goleanCompareNilFunc) (innerFunc := compareNilFunc)
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
    (Hinner := fun ra' k' => wp_compareNil_body))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply (wp_value' (v := ()))
  iexact Hr

end

/-- **The exemplar's sequential full surface judgment**: the
frame-closed triple `{r ↦ 0} r = goleanTestCompareNilToNil() {r ↦ 1}`
plus interpreter-side safety, through the exit pipe. Per-program work:
exactly the WP walk. -/
theorem compareNilToNilSpec :
    GoSpec nilLowered.typeDefs.toList nilLowered.funcs nilLowered.methods
      importedEnv importedCell0 compareNilDriver (importedCellV 1) := by
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  exact wp_compareNilDriver hprog hmeths

/-- **D1 form 1 — the designated-shape triple (CANDIDATE, not
designated)**: the exemplar on the concurrent carrier at full
`InitialSplit` strength, via the conservation transfer
(sequential-degenerate lane — the program spawns nothing; the
genuinely-spawning form is slice 4's work). -/
theorem compareNilToNilSpecC :
    GoSpecC nilLowered.typeDefs.toList nilLowered.funcs nilLowered.methods
      importedEnv importedCell0 compareNilDriver (importedCellV 1) :=
  goSpecC_of_goSpec compareNilToNilSpec

/-- **D1 form 2 — the first-order readout twin (CANDIDATE, not
designated)**: every `.normal` pool completion of the seeded driver
leaves the oracle's TRUE verdict `1` in the harness cell — interpreter
vocabulary only (the deletion test: no Iris, no relation, no tactic in
this statement's closure). -/
theorem compareNilToNilReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel importedEnv (importedSeed nilLowered) ch
        compareNilDriver = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_readoutC compareNilToNilSpec (by decide +kernel)

/-! ## Scaling across the unit (slice-3 phase 3)

The other four WALKABLE nil oracles, driven by `go_walk` + the kit —
each is: the two `Func` record pins, the inner body walk (the
per-program content, side-goal supplies only), the driver exit form,
and the three assembly theorems. `testInterfaceNilWithType` is NOT
here: its verdict expression uses short-circuit `&&`, for which no WP
law exists yet — a VISIBLE recorded gap (manifest row; the `Expr.and`
law family is future law work, not a silent skip). -/

/-- `[]uint8` — the slice oracles' local type. -/
private abbrev slice8 : Ty := .slice (.int .uint8)

/-- `*uint64` — the pointer oracle's local type. -/
private abbrev ptru64 : Ty := .pointer (.int .uint64)

/-- The empty (nil) slice value — every slice local's default. -/
private abbrev nilSlice : SliceValue := { base := none, offset := 0, len := 0, cap := 0 }

/-! ### testCompareSliceToNil (`s := make([]byte, 0); return s != nil`) -/

def compareSliceFunc : Func :=
  { id := { key := "testCompareSliceToNil" },
    args := #[],
    results := #[{ id := "$res0", typ := .bool }],
    body := .block
              #[]
              #[.seqn
                  #[.initialization { id := "$c0", typ := slice8 },
                    .makeSlice (.var "$c0") (.int .uint8) (.intLit 0 .int) none],
                .seqn
                  #[.initialization { id := "s", typ := slice8 },
                    .assign (.var "s") (.var "$c0")],
                .seqn
                  #[.assign (.var "$res0")
                      (.neqCmp slice8 (.var "s") (.nil none)),
                    .returnStmt]],
    variadic := false,
    wrapper := false }

def goleanCompareSliceFunc : Func :=
  { id := { key := "goleanTestCompareSliceToNil" },
    args := #[],
    results := #[{ id := "$res0", typ := .int .int }],
    body := goleanWrapperBody "$c4" ⟨"testCompareSliceToNil"⟩,
    variadic := false,
    wrapper := false }

example : findFunctionIn? nilLowered.funcs ⟨"testCompareSliceToNil"⟩
    = some compareSliceFunc := rfl
example : findFunctionIn? nilLowered.funcs ⟨"goleanTestCompareSliceToNil"⟩
    = some goleanCompareSliceFunc := rfl

abbrev compareSliceDriver : Stmt :=
  .call #[.var "r"] ⟨"goleanTestCompareSliceToNil"⟩ #[]

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- Inner body walk: `make([]byte, 0)` allocates a zero-length backing
array; a made slice — even empty — is NOT nil (`s != nil` is `true`). -/
theorem wp_compareSlice_body {ra : Addr} {k} :
    ra.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec compareSliceFunc.body [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  simp only [compareSliceFunc]
  go_walk
  go_walk_step (wp_init (v := .slice nilSlice) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  go_walk
  go_walk_step (wp_make_slice (n := 0) (elem := .int .uint8)
    (oldcell := ⟨some slice8, .slice nilSlice⟩)
    (backing := .array #[])
    (newcell := fun fa =>
      ⟨some slice8, .slice { base := some (.base fa), offset := 0, len := 0, cap := 0 }⟩)
    (hbacking := fun σ _ => by
      simp [buildDefaultArrayValue, buildArrayValue, Bind.bind, Except.bind,
        pure, Except.pure])
    (hstore := fun σ fa _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind])) as [fa, Hf, Hc]
  go_walk
  go_walk_step (wp_init (v := .slice nilSlice) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  go_walk
  go_walk_step (wp_assign_store
    (oldcell := ⟨some slice8, .slice nilSlice⟩)
    (newcell := ⟨some slice8,
      .slice { base := some (.base fa), offset := 0, len := 0, cap := 0 }⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  go_walk
  go_walk_step (wp_strict_apply_pure (out := .bool true)
    (happly := fun σ => by
      simp [applyStrictOp, valueEq, valueEqFuel, typeResolutionFuel,
        validateSlice, Bind.bind, Except.bind]))
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some .bool, .bool false⟩)
    (newcell := ⟨some .bool, .bool true⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  go_walk_finish Hcont

theorem wp_compareSliceDriver
    (hprog : GoCoreGS.prog GF = nilLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) importedCell0
      ⊢ WP (Config.exec compareSliceDriver importedEnv .stop)
          {{ _v, embed (importedCellV 1) }} := by
  simp only [importedCell0, importedCellV, embed]
  iintro Hr
  iapply (wp_golean_driver (cname := "$c4")
    (wrapperFunc := goleanCompareSliceFunc) (innerFunc := compareSliceFunc)
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
    (Hinner := fun ra' k' => wp_compareSlice_body))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply (wp_value' (v := ()))
  iexact Hr

end

theorem compareSliceToNilSpec :
    GoSpec nilLowered.typeDefs.toList nilLowered.funcs nilLowered.methods
      importedEnv importedCell0 compareSliceDriver (importedCellV 1) := by
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  exact wp_compareSliceDriver hprog hmeths

theorem compareSliceToNilSpecC :
    GoSpecC nilLowered.typeDefs.toList nilLowered.funcs nilLowered.methods
      importedEnv importedCell0 compareSliceDriver (importedCellV 1) :=
  goSpecC_of_goSpec compareSliceToNilSpec

theorem compareSliceToNilReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel importedEnv (importedSeed nilLowered) ch
        compareSliceDriver = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_readoutC compareSliceToNilSpec (by decide +kernel)

/-! ### testComparePointerToNil (`s := new(uint64); return s != nil`) -/

def comparePointerFunc : Func :=
  { id := { key := "testComparePointerToNil" },
    args := #[],
    results := #[{ id := "$res0", typ := .bool }],
    body := .block
              #[]
              #[.seqn
                  #[.initialization { id := "$c1", typ := ptru64 },
                    .newValue (.var "$c1") (.defaultValue (.int .uint64))
                      (some (.int .uint64))],
                .seqn
                  #[.initialization { id := "s", typ := ptru64 },
                    .assign (.var "s") (.var "$c1")],
                .seqn
                  #[.assign (.var "$res0")
                      (.neqCmp ptru64 (.var "s") (.nil none)),
                    .returnStmt]],
    variadic := false,
    wrapper := false }

def goleanComparePointerFunc : Func :=
  { id := { key := "goleanTestComparePointerToNil" },
    args := #[],
    results := #[{ id := "$res0", typ := .int .int }],
    body := goleanWrapperBody "$c5" ⟨"testComparePointerToNil"⟩,
    variadic := false,
    wrapper := false }

example : findFunctionIn? nilLowered.funcs ⟨"testComparePointerToNil"⟩
    = some comparePointerFunc := rfl
example : findFunctionIn? nilLowered.funcs ⟨"goleanTestComparePointerToNil"⟩
    = some goleanComparePointerFunc := rfl

abbrev comparePointerDriver : Stmt :=
  .call #[.var "r"] ⟨"goleanTestComparePointerToNil"⟩ #[]

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- Inner body walk: `new(uint64)` is a non-nil pointer (`true`). -/
theorem wp_comparePointer_body {ra : Addr} {k} :
    ra.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec comparePointerFunc.body [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  simp only [comparePointerFunc]
  go_walk
  go_walk_step wp_init_ptr
  go_walk
  go_walk_step (wp_eval_strict_nullary_pure (v := .int 0 .uint64)
    (hplan := rfl)
    (happly := fun σ => by
      simp [applyStrictOp, defaultValue, defaultValueFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  go_walk_step (wp_new_value (oldcell := ⟨some ptru64, .nil⟩)
    (newcell := fun fa => ⟨some ptru64, .addr (.base fa)⟩)
    (hstore := fun σ fa _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind])) as [fa, Hf, Hc]
  go_walk
  go_walk_step wp_init_ptr
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some ptru64, .nil⟩)
    (newcell := ⟨some ptru64, .addr (.base fa)⟩)
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

theorem wp_comparePointerDriver
    (hprog : GoCoreGS.prog GF = nilLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) importedCell0
      ⊢ WP (Config.exec comparePointerDriver importedEnv .stop)
          {{ _v, embed (importedCellV 1) }} := by
  simp only [importedCell0, importedCellV, embed]
  iintro Hr
  iapply (wp_golean_driver (cname := "$c5")
    (wrapperFunc := goleanComparePointerFunc)
    (innerFunc := comparePointerFunc)
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
    (Hinner := fun ra' k' => wp_comparePointer_body))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply (wp_value' (v := ()))
  iexact Hr

end

theorem comparePointerToNilSpec :
    GoSpec nilLowered.typeDefs.toList nilLowered.funcs nilLowered.methods
      importedEnv importedCell0 comparePointerDriver (importedCellV 1) := by
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  exact wp_comparePointerDriver hprog hmeths

theorem comparePointerToNilSpecC :
    GoSpecC nilLowered.typeDefs.toList nilLowered.funcs nilLowered.methods
      importedEnv importedCell0 comparePointerDriver (importedCellV 1) :=
  goSpecC_of_goSpec comparePointerToNilSpec

theorem comparePointerToNilReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel importedEnv (importedSeed nilLowered) ch
        comparePointerDriver = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_readoutC comparePointerToNilSpec (by decide +kernel)

/-! ### testComparePointerWrappedToNil
(`var s []byte; s = make([]byte, 1); return s != nil`) -/

def compareWrappedFunc : Func :=
  { id := { key := "testComparePointerWrappedToNil" },
    args := #[],
    results := #[{ id := "$res0", typ := .bool }],
    body := .block
              #[]
              #[.seqn
                  #[.initialization { id := "s", typ := slice8 }],
                .seqn
                  #[.initialization { id := "$c3", typ := slice8 },
                    .makeSlice (.var "$c3") (.int .uint8) (.intLit 1 .int) none],
                .seqn
                  #[.assign (.var "s") (.var "$c3")],
                .seqn
                  #[.assign (.var "$res0")
                      (.neqCmp slice8 (.var "s") (.nil none)),
                    .returnStmt]],
    variadic := false,
    wrapper := false }

def goleanCompareWrappedFunc : Func :=
  { id := { key := "goleanTestComparePointerWrappedToNil" },
    args := #[],
    results := #[{ id := "$res0", typ := .int .int }],
    body := goleanWrapperBody "$c7" ⟨"testComparePointerWrappedToNil"⟩,
    variadic := false,
    wrapper := false }

example : findFunctionIn? nilLowered.funcs ⟨"testComparePointerWrappedToNil"⟩
    = some compareWrappedFunc := rfl
example : findFunctionIn? nilLowered.funcs
    ⟨"goleanTestComparePointerWrappedToNil"⟩
    = some goleanCompareWrappedFunc := rfl

abbrev compareWrappedDriver : Stmt :=
  .call #[.var "r"] ⟨"goleanTestComparePointerWrappedToNil"⟩ #[]

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- Inner body walk: a made one-element slice is not nil (`true`). -/
theorem wp_compareWrapped_body {ra : Addr} {k} :
    ra.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec compareWrappedFunc.body [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  simp only [compareWrappedFunc]
  go_walk
  go_walk_step (wp_init (v := .slice nilSlice) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  go_walk
  go_walk_step (wp_init (v := .slice nilSlice) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  go_walk
  go_walk_step (wp_make_slice (n := 1) (elem := .int .uint8)
    (oldcell := ⟨some slice8, .slice nilSlice⟩)
    (backing := .array #[.int 0 .uint8])
    (newcell := fun fa =>
      ⟨some slice8, .slice { base := some (.base fa), offset := 0, len := 1, cap := 1 }⟩)
    (hbacking := fun σ _ => by
      simp [buildDefaultArrayValue, buildArrayValue, defaultValue,
        defaultValueFuel, typeResolutionFuel,
        Std.Legacy.Range.forIn_eq_forIn_range', List.range',
        List.forIn_cons, List.forIn_nil, Bind.bind, Except.bind,
        pure, Except.pure])
    (hstore := fun σ fa _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind])) as [fa, Hf, Hc]
  go_walk
  go_walk_step (wp_assign_store
    (oldcell := ⟨some slice8, .slice nilSlice⟩)
    (newcell := ⟨some slice8,
      .slice { base := some (.base fa), offset := 0, len := 1, cap := 1 }⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  go_walk
  go_walk_step (wp_strict_apply_pure (out := .bool true)
    (happly := fun σ => by
      simp [applyStrictOp, valueEq, valueEqFuel, typeResolutionFuel,
        validateSlice, Bind.bind, Except.bind]))
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some .bool, .bool false⟩)
    (newcell := ⟨some .bool, .bool true⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  go_walk_finish Hcont

theorem wp_compareWrappedDriver
    (hprog : GoCoreGS.prog GF = nilLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) importedCell0
      ⊢ WP (Config.exec compareWrappedDriver importedEnv .stop)
          {{ _v, embed (importedCellV 1) }} := by
  simp only [importedCell0, importedCellV, embed]
  iintro Hr
  iapply (wp_golean_driver (cname := "$c7")
    (wrapperFunc := goleanCompareWrappedFunc)
    (innerFunc := compareWrappedFunc)
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
    (Hinner := fun ra' k' => wp_compareWrapped_body))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply (wp_value' (v := ()))
  iexact Hr

end

theorem comparePointerWrappedToNilSpec :
    GoSpec nilLowered.typeDefs.toList nilLowered.funcs nilLowered.methods
      importedEnv importedCell0 compareWrappedDriver (importedCellV 1) := by
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  exact wp_compareWrappedDriver hprog hmeths

theorem comparePointerWrappedToNilSpecC :
    GoSpecC nilLowered.typeDefs.toList nilLowered.funcs nilLowered.methods
      importedEnv importedCell0 compareWrappedDriver (importedCellV 1) :=
  goSpecC_of_goSpec comparePointerWrappedToNilSpec

theorem comparePointerWrappedToNilReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel importedEnv (importedSeed nilLowered) ch
        compareWrappedDriver = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_readoutC comparePointerWrappedToNilSpec (by decide +kernel)

/-! ### testComparePointerWrappedDefaultToNil
(`var s []byte; return s == nil`) -/

def compareWrappedDefaultFunc : Func :=
  { id := { key := "testComparePointerWrappedDefaultToNil" },
    args := #[],
    results := #[{ id := "$res0", typ := .bool }],
    body := .block
              #[]
              #[.seqn
                  #[.initialization { id := "s", typ := slice8 }],
                .seqn
                  #[.assign (.var "$res0")
                      (.eqCmp slice8 (.var "s") (.nil none)),
                    .returnStmt]],
    variadic := false,
    wrapper := false }

def goleanCompareWrappedDefaultFunc : Func :=
  { id := { key := "goleanTestComparePointerWrappedDefaultToNil" },
    args := #[],
    results := #[{ id := "$res0", typ := .int .int }],
    body := goleanWrapperBody "$c8" ⟨"testComparePointerWrappedDefaultToNil"⟩,
    variadic := false,
    wrapper := false }

example : findFunctionIn? nilLowered.funcs
    ⟨"testComparePointerWrappedDefaultToNil"⟩
    = some compareWrappedDefaultFunc := rfl
example : findFunctionIn? nilLowered.funcs
    ⟨"goleanTestComparePointerWrappedDefaultToNil"⟩
    = some goleanCompareWrappedDefaultFunc := rfl

abbrev compareWrappedDefaultDriver : Stmt :=
  .call #[.var "r"] ⟨"goleanTestComparePointerWrappedDefaultToNil"⟩ #[]

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- Inner body walk: a default (never-made) slice IS nil (`true`). -/
theorem wp_compareWrappedDefault_body {ra : Addr} {k} :
    ra.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec compareWrappedDefaultFunc.body
            [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  simp only [compareWrappedDefaultFunc]
  go_walk
  go_walk_step (wp_init (v := .slice nilSlice) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  go_walk
  go_walk_step (wp_strict_apply_pure (out := .bool true)
    (happly := fun σ => by
      simp [applyStrictOp, valueEq, valueEqFuel, typeResolutionFuel,
        validateSlice, Bind.bind, Except.bind]))
  go_walk
  go_walk_step (wp_assign_store (oldcell := ⟨some .bool, .bool false⟩)
    (newcell := ⟨some .bool, .bool true⟩)
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  go_walk_finish Hcont

theorem wp_compareWrappedDefaultDriver
    (hprog : GoCoreGS.prog GF = nilLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) importedCell0
      ⊢ WP (Config.exec compareWrappedDefaultDriver importedEnv .stop)
          {{ _v, embed (importedCellV 1) }} := by
  simp only [importedCell0, importedCellV, embed]
  iintro Hr
  iapply (wp_golean_driver (cname := "$c8")
    (wrapperFunc := goleanCompareWrappedDefaultFunc)
    (innerFunc := compareWrappedDefaultFunc)
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
    (Hinner := fun ra' k' => wp_compareWrappedDefault_body))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply (wp_value' (v := ()))
  iexact Hr

end

theorem comparePointerWrappedDefaultToNilSpec :
    GoSpec nilLowered.typeDefs.toList nilLowered.funcs nilLowered.methods
      importedEnv importedCell0 compareWrappedDefaultDriver
      (importedCellV 1) := by
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths _htypes
  exact wp_compareWrappedDefaultDriver hprog hmeths

theorem comparePointerWrappedDefaultToNilSpecC :
    GoSpecC nilLowered.typeDefs.toList nilLowered.funcs nilLowered.methods
      importedEnv importedCell0 compareWrappedDefaultDriver
      (importedCellV 1) :=
  goSpecC_of_goSpec comparePointerWrappedDefaultToNilSpec

theorem comparePointerWrappedDefaultToNilReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel importedEnv (importedSeed nilLowered) ch
        compareWrappedDefaultDriver = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  goSpec_seeded_readoutC comparePointerWrappedDefaultToNilSpec
    (by decide +kernel)

end GoLean.ImportedGoose.SemanticsNil
