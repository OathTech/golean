import GoLeanProofs.SurfaceExit
import GoLeanProofs.Laws.Control
import GoLeanProofs.Laws.Eval
import GoLeanProofs.Laws.Assign
import GoLeanProofs.Laws.Call
import GoLeanProofs.Laws.Init
import GoLeanProofs.Laws.Unwind

/-!
# The imported-goose R3 kit (spec-parity slice 3, 2026-08-10)

Design of record: `docs/2026-08-10_wp-walk-driver.md` §2. The shared,
CONVENTION-level walks for the imported sequential-oracle class — every
`golean<TestName>` wrapper the import pipeline generates has the same
body modulo three parameters (the gensym call-target name, the inner
`FuncId`, the wrapper `FuncId`), so its walk is proven ONCE here and
each oracle supplies only its INNER body walk. Convention-specific
(the imported-goose wrapper and the TotalPins seed shape), hence a
`Specs/` module, never a general law file (layering doctrine).

Contents:
* `goleanWrapperBody` — the wrapper body as a function of the two
  names; per-unit `rfl` pins tie the imported lowering's actual
  wrapper to this term (behind the ci 1c5 staleness guard).
* `wp_golean_wrapper_body` — the wrapper walk: init the call target,
  the inner call's frame entry/exit at a bool cell, the `if`, the
  verdict assign, return. Parameterized by the inner body's spec.
* `wp_golean_driver` — the driver-statement walk
  (`x = golean<Test>()` into any int target cell), ending in the
  `{r ↦ 0} … {r ↦ 1}` shape `goSpec_of_wp` consumes.
* `goSpec_seeded_readout` / `goSpec_seeded_readoutC` — the generic
  first-order readout derivations at the TotalPins seed (sequential
  and pool carrier; the `goldenReturnsTwo`/`goldenReturnsTwoC`
  derivations proven once instead of per-program).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface

namespace GoLean.Iris.ImportedGoose
-- NOTE: the file-level `open` above covers both namespaces below.

-- Uniform simp sets across law variants (the golden-walk convention):
-- the unused-arg linter misfires on them.
set_option linter.unusedSimpArgs false

/-- The import pipeline's wrapper body, as a function of the gensym
call-target name and the inner oracle's `FuncId`:

```go
func goleanTestX() int {
    $cN := testX()        // init $cN bool; call [$cN] testX []
    if $cN { return 1 }
    return 0
}
```

Every oracle's `rfl` pin (`example : … = goleanWrapperBody "$cN" ⟨"testX"⟩`)
ties the imported lowering's actual wrapper to this term; a frontend
wrapper-generation change breaks the pins loudly (after the 1c5
staleness guard has already caught the term drift). -/
def goleanWrapperBody (cname : String) (innerFid : FuncId) : Stmt :=
  .block #[]
    #[.seqn #[.initialization ⟨cname, .bool⟩,
              .call #[.var cname] innerFid #[]],
      .ifThenElse (.var cname)
        (.block #[]
          #[.seqn #[.assign (.var "$res0") (.intLit 1 .int),
                    .returnStmt]])
        (.seqn #[]),
      .seqn #[.assign (.var "$res0") (.intLit 0 .int),
              .returnStmt]]

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **The wrapper walk** — `goleanWrapperBody` under the wrapper's own
frame environment (`$res0` bound to the wrapper's pinned int result
cell), for a TRUE inner verdict: init the call-target cell, enter the
inner oracle's frame (`wp_call_enter_ret1` at the bool result), run the
inner body through the supplied spec `Hinner`, exit the frame writing
`true` into the call-target cell (`wp_frame_return₁`), take the `if`'s
then-branch, write `1` into `$res0`, return.

`Hinner` is the per-oracle content: the inner body's walk, delivering
`$res0 ↦ .bool true` at the returning continuation. `hcname` rules out
the one name collision that would let the call target shadow the
wrapper's result binding (every generated gensym `$cN` satisfies it). -/
theorem wp_golean_wrapper_body {cname : String} {innerFid : FuncId}
    {innerFunc : Func} {ra : Addr} {k}
    (hcname : cname ≠ "$res0")
    (hfind : findFunctionIn? (GoCoreGS.prog GF) innerFid = some innerFunc)
    (hargs : innerFunc.args = #[])
    (hres : innerFunc.results = #[⟨"$res0", .bool⟩])
    (hnodisp : ∀ σ : ExecState, σ.methods = GoCoreGS.methods GF →
      dynamicDispatch? σ innerFunc #[] = .ok none)
    (Hinner : ∀ (ra' : Addr) (k' : Cont),
      iprop(ra'.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
        ∗ (ra'.id ↦ (⟨some .bool, .bool true⟩ : HeapCell) -∗
            WP (Config.returning k') @ s ; E {{ Φ }}))
        ⊢ WP (Config.exec innerFunc.body [[("$res0", Loc.base ra')]] k')
            @ s ; E {{ Φ }}) :
    ra.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell) -∗
          WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (goleanWrapperBody cname innerFid)
            [[("$res0", Loc.base ra)]] k) @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  simp only [goleanWrapperBody]
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
  -- `$cN := false` (the call-target declaration; `wp_init_bool`'s
  -- discharge witness — S3 audit round: the walk first used the
  -- generic `wp_init` inline while the law's docstring claimed this
  -- site as its witness)
  iapply wp_init_bool
  iintro %ca Hc
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc5
  -- the inner call: frame entry at the bool result
  iapply (wp_call_enter_ret1 (dv := .bool false)
    (plans := [(.chain [], [.ref cname])]) (hplan := rfl)
    hfind hargs hres hnodisp
    (hdef := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %ra' Hres
  -- the inner body (the per-oracle content)
  iapply (Hinner ra' _)
  isplitl [Hres]
  · iexact Hres
  iintro Hres
  -- frame exit: write the TRUE verdict into the call-target cell
  iapply (wp_frame_return₁ (ta := ca)
    (rcell := ⟨some .bool, .bool true⟩)
    (tcell := ⟨some .bool, .bool false⟩)
    (tcell' := ⟨some .bool, .bool true⟩)
    (hres := by
      simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
        Scope.lookup])
    (hstore := fun σ _ht hlook => by
      simp [storeLoc, hlook, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, Bind.bind, Except.bind]))
  isplitl [Hres]
  · iexact Hres
  isplitl [Hc]
  · iexact Hc
  iintro ⟨Hres, Hc⟩
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc6
  -- `if $cN { … }`
  iapply wp_if_start
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc7
  iapply (wp_eval_var (a := ca) (cell := ⟨some .bool, .bool true⟩) (hres := by
    simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
      Scope.lookup]))
  isplitl [Hc]
  · iexact Hc
  iintro Hc
  iapply wp_if_bool
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc8
  rw [if_pos rfl]
  -- the then-branch: `$res0 = 1; return`
  iapply wp_block_nil
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc9
  simp only [List.toList_toArray]
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc10
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont_splice, List.cons_append,
    List.nil_append, List.append_nil]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc11
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc12
  iapply (wp_assign_lit (a := ra) (n := 1) (kind := .int) (w := .int 0 .int)
    (hres := by
      simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
        Scope.lookup, hcname]))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  rw [show IntKind.normalize .int 1 = 1 from by decide] at *
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc13
  iapply wp_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc14
  iapply wp_seq_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc15
  iapply wp_seq_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc16
  iapply Hcont $$ Hr

/-- **The driver walk** — `x = golean<Test>()` into any int-typed target
cell over any prior value: the wrapper's frame entry
(`wp_call_enter_ret1` at the int result), the wrapper body
(`wp_golean_wrapper_body`), the value frame exit writing `1` into the
caller's cell (`wp_frame_return_int`). This is the `{x ↦ w} … {x ↦ 1}`
walk `goSpec_of_wp` consumes at the TotalPins driver statement. -/
theorem wp_golean_driver {x cname : String} {wrapperFid innerFid : FuncId}
    {wrapperFunc innerFunc : Func} {ta : Addr} {w : GoValue} {env k}
    (hr : LocalEnv.lookup env x = some (.base ta))
    (hcname : cname ≠ "$res0")
    (hfindW : findFunctionIn? (GoCoreGS.prog GF) wrapperFid = some wrapperFunc)
    (hargsW : wrapperFunc.args = #[])
    (hresW : wrapperFunc.results = #[⟨"$res0", .int .int⟩])
    (hbodyW : wrapperFunc.body = goleanWrapperBody cname innerFid)
    (hnodispW : ∀ σ : ExecState, σ.methods = GoCoreGS.methods GF →
      dynamicDispatch? σ wrapperFunc #[] = .ok none)
    (hfind : findFunctionIn? (GoCoreGS.prog GF) innerFid = some innerFunc)
    (hargs : innerFunc.args = #[])
    (hres : innerFunc.results = #[⟨"$res0", .bool⟩])
    (hnodisp : ∀ σ : ExecState, σ.methods = GoCoreGS.methods GF →
      dynamicDispatch? σ innerFunc #[] = .ok none)
    (Hinner : ∀ (ra' : Addr) (k' : Cont),
      iprop(ra'.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
        ∗ (ra'.id ↦ (⟨some .bool, .bool true⟩ : HeapCell) -∗
            WP (Config.returning k') @ s ; E {{ Φ }}))
        ⊢ WP (Config.exec innerFunc.body [[("$res0", Loc.base ra')]] k')
            @ s ; E {{ Φ }}) :
    ta.id ↦ (⟨some (.int .int), w⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell) -∗
          WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[.var x] wrapperFid #[]) env k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Ht, Hcont⟩
  iapply (wp_call_enter_ret1 (dv := .int 0 .int)
    (plans := [(.chain [], [.ref x])]) (hplan := rfl)
    hfindW hargsW hresW hnodispW
    (hdef := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  iintro %ra Hres
  rw [hbodyW]
  iapply (wp_golean_wrapper_body hcname hfind hargs hres hnodisp Hinner)
  isplitl [Hres]
  · iexact Hres
  iintro Hres
  iapply (wp_frame_return_int (m := 1) (kind := .int) (tkind := .int)
    (w := w) hr)
  isplitl [Hres]
  · iexact Hres
  isplitl [Ht]
  · iexact Ht
  iintro ⟨Hres, Ht⟩
  rw [show IntKind.normalize .int 1 = 1 from by decide] at *
  iapply Hcont $$ Ht

end

end GoLean.Iris.ImportedGoose

/- Namespace note (S3 audit round): these convention-level defs and
readout derivations first lived in `namespace GoLean.Surface` — squatting
the spec-surface namespace from an Iris-importing Specs module. They now
live under `GoLean.ImportedGoose` (the corpus lane's own namespace; the
per-unit proof modules are its children, so references resolve
unqualified). If a consumer is ever DESIGNATED, these defs additionally
move to a def-only, core-import-only module (the
`Statements`/`ForkJoinTargets` pattern) — recorded at the slice note's
P-S3-1. -/
namespace GoLean.ImportedGoose

-- The file-level `open`s above cover this namespace too (delta-review
-- cleanup: the redundant re-opens are gone); `GoLean.Iris` is the one
-- ADDITIONAL namespace the readout derivations below need (the
-- heaplet-bridge lemmas live there).
open GoLean.Iris

/-- The TotalPins seed for an imported program: the harness-owned output
cell at base address 0, `nextAddr = 1` (the convention every imported
R2 pin already uses). -/
def importedSeed (p : Program) : ExecState :=
  { types := p.typeDefs.toList,
    functions := p.funcs,
    methods := p.methods,
    heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
    nextAddr := 1 }

/-- Driver env: `r` names the harness output cell (the convention). -/
abbrev importedEnv : LocalEnv := [[("r", .base ⟨0⟩)]]

/-- The seeded-cell precondition `r ↦ 0`. -/
def importedCell0 : HProp := .pointsTo 0 ⟨some (.int .int), .int 0 .int⟩

/-- The verdict postcondition `r ↦ v`. -/
def importedCellV (v : Int) : HProp :=
  .pointsTo 0 ⟨some (.int .int), .int v .int⟩

/-- **The generic sequential readout at the TotalPins seed** (the
`goldenReturnsTwo` derivation, proven once): a `GoSpec`
`{r ↦ 0} prog {r ↦ v}` plus machine well-formedness of the seeded
initial configuration (at concrete programs: `decide +kernel`) yields
the plain first-order readout — every `.normal` completion leaves
`int v` in the output cell. -/
theorem goSpec_seeded_readout {p : Program} {prog : Stmt} {v : Int}
    (hspec : GoSpec p.typeDefs.toList p.funcs p.methods importedEnv
      importedCell0 prog (importedCellV v))
    (hwf : Machine.MachineWf
      { functions := p.funcs,
        heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
        nextAddr := 1 }
      (.exec prog importedEnv .stop)) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel importedEnv (importedSeed p) ch prog
        = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int v .int) := by
  intro fuel ch σf ch' hrun
  have hsat : sat (heapletOf [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)])
      importedCell0 := rfl
  have hsplit := InitialSplit.noFrame (P := importedCell0)
    (hp := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)]) (na := 1)
    (funcs := p.funcs) (env₀ := importedEnv) (prog := prog) hsat hwf
  have hres := hspec.1 _ 1 _ ∅ hsplit fuel ch σf ch' hrun
  obtain ⟨h, _hd, hsub, _hF, hsatQ⟩ := hres
  rw [show h = (∅ : Heaplet).insert 0 ⟨some (.int .int), .int v .int⟩
    from hsatQ] at hsub
  have hget := hsub 0 ⟨some (.int .int), .int v .int⟩ (by
    rw [heaplet_get?_eq, heaplet_insert_eq]
    exact LawfulPartialMap.get?_insert_eq rfl)
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hget
  exact loadLoc_base_of_lookup hget

/-- **The generic pool-carrier readout twin** (the `goldenReturnsTwoC`
derivation, proven once): the same `GoSpec` yields the readout on the
CONCURRENT carrier — `GoSpec`'s safety half confines the sequential run
to the transferable classes, `execProg_single_eq_execStmt` pins the
pool run to it, and the sequential readout reads the cell. -/
theorem goSpec_seeded_readoutC {p : Program} {prog : Stmt} {v : Int}
    (hspec : GoSpec p.typeDefs.toList p.funcs p.methods importedEnv
      importedCell0 prog (importedCellV v))
    (hwf : Machine.MachineWf
      { functions := p.funcs,
        heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
        nextAddr := 1 }
      (.exec prog importedEnv .stop)) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel importedEnv (importedSeed p) ch prog
        = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int v .int) := by
  intro fuel ch σf ch' hrun
  have hsat : sat (heapletOf [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)])
      importedCell0 := rfl
  have hsplit := InitialSplit.noFrame (P := importedCell0)
    (hp := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)]) (na := 1)
    (funcs := p.funcs) (env₀ := importedEnv) (prog := prog) hsat hwf
  rcases hspec.2 _ _ _ _ hsplit fuel ch with ⟨σs, chs, hseq⟩ | hseq
  · have hpool := execProg_single_eq_execStmt hseq trivial
    have hrun' : execProg fuel importedEnv (importedSeed p) ch prog
        = .ok (.normal σf, ch') := hrun
    rw [show importedSeed p
        = { types := p.typeDefs.toList, functions := p.funcs,
            methods := p.methods,
            heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
            nextAddr := 1 } from rfl] at hrun'
    rw [hrun'] at hpool
    injection hpool with hpair
    injection hpair with hout hch
    injection hout with hσ
    subst hσ
    subst hch
    exact goSpec_seeded_readout hspec hwf fuel ch σf ch' hseq
  · have hpool := execProg_single_eq_execStmt hseq trivial
    have hrun' : execProg fuel importedEnv (importedSeed p) ch prog
        = .ok (.normal σf, ch') := hrun
    rw [show importedSeed p
        = { types := p.typeDefs.toList, functions := p.funcs,
            methods := p.methods,
            heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
            nextAddr := 1 } from rfl] at hrun'
    rw [hrun'] at hpool
    cases hpool

/-- **The joint sequential completes-AND-verdict form at the TotalPins
seed** (P-S3-5, CLOSED at slice 6; the `goldenTotalReadout` precedent
shape): a `GoSpec {r ↦ 0} prog {r ↦ v}`, machine well-formedness of
the seeded configuration, and the R2 ∀-streams `Terminates` pin
yield — on the SINGLE sequential carrier (`execStmt`, the R2 pins')
— past one bound, EVERY choice stream's run completes at `.normal`
AND the final state delivers the verdict. This is exactly the
composition the S3 delta review machine-confirmed could NOT be
assembled from the two shipped halves (the sequential-carrier
`TerminatesNormally` and the `execProg`-hypothesised readout twin —
feeding one's witness into the other is a type error); stating it on
one carrier closes the recorded gap for the sequential class-1 rows,
leaving the "separate halves" caveat to the concurrent rows only. -/
theorem goSpec_seeded_totalReadout {p : Program} {prog : Stmt} {v : Int}
    (hspec : GoSpec p.typeDefs.toList p.funcs p.methods importedEnv
      importedCell0 prog (importedCellV v))
    (hwf : Machine.MachineWf
      { functions := p.funcs,
        heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
        nextAddr := 1 }
      (.exec prog importedEnv .stop))
    (hterm : Terminates importedEnv (importedSeed p) prog) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel importedEnv (importedSeed p) ch prog
          = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int v .int) := by
  have hsat : sat (heapletOf [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)])
      importedCell0 := rfl
  have hsplit := InitialSplit.noFrame (P := importedCell0)
    (hp := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)]) (na := 1)
    (funcs := p.funcs) (env₀ := importedEnv) (prog := prog) hsat hwf
  have hnorm : TerminatesNormally importedEnv (importedSeed p) prog :=
    terminatesNormally_of_progressExec hsplit hspec.2 hterm
  obtain ⟨N, hN⟩ := hnorm
  refine ⟨N, fun fuel hfuel ch => ?_⟩
  obtain ⟨σf, ch', hrun⟩ := hN fuel hfuel ch
  exact ⟨σf, ch', hrun,
    goSpec_seeded_readout hspec hwf fuel ch σf ch' hrun⟩

end GoLean.ImportedGoose
