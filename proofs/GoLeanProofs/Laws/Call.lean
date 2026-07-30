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
import GoLeanProofs.HeapBridge
import GoLeanProofs.Laws.Eval
import GoLeanProofs.Specs.GoldenProgram

/-!
# Call laws (R3 rewrite over the fine-grained machine)

Under the machine a call is a walk: dispatch (`wp_call_first_target` /
`wp_call_first_arg`), the target/argument evaluations (Laws/Eval), then
ONE allocating frame-entry step (`enterFrame`: lookup, arity, dispatch,
parameter binding, result declaration, result-location pinning), the
body, and a frame exit. The frame-entry laws here cover the two shapes
the golden program exercises — unary-argument void-result
(`wp_call_enter_arg1`, the `inc(&x)` shape) and nullary-argument
single-int-result (`wp_call_enter_ret1`, the `r = incViaCall()` shape) —
each with its premises discharged on the CONCRETE golden functions as the
non-vacuity witnesses (`wp_call_enter_inc`, `wp_call_enter_incViaCall`;
the genuinely-external premises are the program/method-table pins, as in
the old `wp_inc_call`). `wp_frame_return_int` is the value frame exit
(read the pinned result cell, store to the caller's target — the
`wp_store_step₂` two-cell core), premise-free given the resources.

Dynamic dispatch note: the machine consults `σ.methods` at frame entry,
so `GoCoreGS` now pins the method table like the program; the
`hnodisp` premise closes by computation once the table is pinned
concrete (`#[]` for the golden program).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris

-- Uniform simp sets across law variants; the unused-arg linter misfires
-- per-instance.
set_option linter.unusedSimpArgs false

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- Dispatch a call with at least one target: evaluate the first target
address. -/
theorem wp_call_first_target {targets : Array Assignee} {fid : FuncId}
    {args : Array Expr} {te : Expr} {rest : List Expr} {env k}
    (hplan : assigneesExprs targets.toList = some (te :: rest)) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE te env (.callTargetsK fid [] rest args.toList env k))
        @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.call targets fid args) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.callFirstTarget hplan)

/-- Dispatch a targetless call with at least one argument: evaluate the
first argument. -/
theorem wp_call_first_arg {targets : Array Assignee} {fid : FuncId}
    {args : Array Expr} {a : Expr} {rest : List Expr} {env k}
    (htargets : assigneesExprs targets.toList = some [])
    (hargs : args.toList = a :: rest) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE a env (.callArgsK fid [] [] rest env k))
        @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.call targets fid args) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.callFirstArg htargets hargs)

/-- **Frame entry, unary argument / void result** (the `inc(&x)` shape):
the last argument value arrives, and one step allocates the parameter
cell (normalized at declared type) and enters the body under the fresh
one-binding frame environment. The continuation receives the
machine-chosen cell (`∀ pa`). -/
theorem wp_call_enter_arg1 {fid : FuncId} {func : Func} {pid : String}
    {pty : Ty} {v v' : GoValue} {locs : List Loc} {env k}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) fid = some func)
    (hargs : func.args = #[⟨pid, pty⟩])
    (hres : func.results = #[])
    (hnodisp : ∀ σ : ExecState, σ.methods = GoCoreGS.methods GF →
      dynamicDispatch? σ func #[v] = .ok none)
    (hnorm : ∀ σ : ExecState, normalizeValueForTy σ pty v = .ok v') :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some pty, v'⟩ : HeapCell) -∗
        WP (Config.exec func.body [[(pid, Loc.base pa)]] (.frame locs [] [] k))
          @ s ; E {{ Φ }})
      ⊢ WP (Config.retV v (.callArgsK fid locs [] [] env k)) @ s ; E {{ Φ }} := by
  have henter : ∀ σ₁ : ExecState, σ₁.functions = GoCoreGS.prog GF →
      σ₁.methods = GoCoreGS.methods GF →
      enterFrame σ₁ fid [v]
        = .ok (func, [[(pid, Loc.base ⟨σ₁.nextAddr⟩)]], [],
            { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, v'⟩, nextAddr := σ₁.nextAddr + 1 }) := by
    intro σ₁ hfns hmeths
    unfold enterFrame
    rw [hfns, hfind]
    simp [hargs, hres, Bind.bind, Except.bind, hnodisp σ₁ hmeths, bindParams,
      hnorm σ₁, ExecState.alloc, ExecState.freshLoc, allocDecls, pinResultLocs,
      LocalEnv.declare]
    exact hfns
  iintro Hcont
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, hwf⟩ := Hinv
  have hstep := Step.callArgsDoneEnter (vals := []) (locs := locs) (env := env)
    (k := k) (henter σ₁ hfns hmeths)
  have hdet : ∀ c' s',
      Step (.retV v (.callArgsK fid locs [] [] env k)) σ₁ c' s' →
      c' = Config.exec func.body [[(pid, Loc.base ⟨σ₁.nextAddr⟩)]]
             (.frame locs [] [] k)
        ∧ s' = { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, v'⟩, nextAddr := σ₁.nextAddr + 1 } := by
    intro c' s' hst
    obtain ⟨h1, h2⟩ := step_det (by trivial) hstep hst
    exact ⟨h1.symm, h2.symm⟩
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
    imod (genHeap_alloc (v := (⟨some pty, v'⟩ : HeapCell)) hwf.fresh_get?)
      $$ Hσ with ⟨Hσ, Hpt, Htok⟩
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iapply (genHeapInterp_eqv
          (fun kk => (heapToMap_set_base σ₁.heap ⟨σ₁.nextAddr⟩ _ kk).symm)) $$ Hσ
      · ipureintro
        exact ⟨hfns, hmeths, hwf.alloc⟩
    · isplitl [Hpt Hcont]
      · iapply Hcont $$ %(⟨σ₁.nextAddr⟩ : Addr) Hpt
      · itrivial

/-- **Frame entry, nullary argument / single result** (the
`r = incViaCall()` shape): the (single) target address arrives, and one
step allocates the result cell at its default and enters the body; the
frame pins the caller target and the result location. -/
theorem wp_call_enter_ret1 {fid : FuncId} {func : Func} {rid : String}
    {rty : Ty} {dv : GoValue} {tl : Loc} {env k}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) fid = some func)
    (hargs : func.args = #[])
    (hres : func.results = #[⟨rid, rty⟩])
    (hnodisp : ∀ σ : ExecState, σ.methods = GoCoreGS.methods GF →
      dynamicDispatch? σ func #[] = .ok none)
    (hdef : ∀ σ : ExecState, defaultValue σ rty = .ok dv) :
    iprop(∀ ra : Addr, ra.id ↦ (⟨some rty, dv⟩ : HeapCell) -∗
        WP (Config.exec func.body [[(rid, Loc.base ra)]]
              (.frame [tl] [Loc.base ra] [] k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.addr tl) (.callTargetsK fid [] [] [] env k))
          @ s ; E {{ Φ }} := by
  have henter : ∀ σ₁ : ExecState, σ₁.functions = GoCoreGS.prog GF →
      σ₁.methods = GoCoreGS.methods GF →
      enterFrame σ₁ fid []
        = .ok (func, [[(rid, Loc.base ⟨σ₁.nextAddr⟩)]], [Loc.base ⟨σ₁.nextAddr⟩],
            { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some rty, dv⟩, nextAddr := σ₁.nextAddr + 1 }) := by
    intro σ₁ hfns hmeths
    unfold enterFrame
    rw [hfns, hfind]
    simp [hargs, hres, Bind.bind, Except.bind, hnodisp σ₁ hmeths, bindParams,
      hdef σ₁, ExecState.alloc, ExecState.freshLoc, allocDecls, pinResultLocs,
      LocalEnv.declare, LocalEnv.lookup, Scope.lookup]
    exact hfns
  iintro Hcont
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, hwf⟩ := Hinv
  have hstep := Step.callTargetsDoneEnter (locs := []) (env := env) (k := k)
    (rfl : valueAsLoc (.addr tl) = .ok tl) (henter σ₁ hfns hmeths)
  have hdet : ∀ c' s',
      Step (.retV (.addr tl) (.callTargetsK fid [] [] [] env k)) σ₁ c' s' →
      c' = Config.exec func.body [[(rid, Loc.base ⟨σ₁.nextAddr⟩)]]
             (.frame ([] ++ [tl]) [Loc.base ⟨σ₁.nextAddr⟩] [] k)
        ∧ s' = { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some rty, dv⟩, nextAddr := σ₁.nextAddr + 1 } := by
    intro c' s' hst
    obtain ⟨h1, h2⟩ := step_det (by trivial) hstep hst
    exact ⟨h1.symm, h2.symm⟩
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
    simp only [List.nil_append]
    imod (genHeap_alloc (v := (⟨some rty, dv⟩ : HeapCell)) hwf.fresh_get?)
      $$ Hσ with ⟨Hσ, Hpt, Htok⟩
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iapply (genHeapInterp_eqv
          (fun kk => (heapToMap_set_base σ₁.heap ⟨σ₁.nextAddr⟩ _ kk).symm)) $$ Hσ
      · ipureintro
        exact ⟨hfns, hmeths, hwf.alloc⟩
    · isplitl [Hpt Hcont]
      · iapply Hcont $$ %(⟨σ₁.nextAddr⟩ : Addr) Hpt
      · itrivial

/-- **Value frame exit**: `return` at a frame with one pinned int result
location and one int-typed caller target — read the result cell, store
(normalizing) into the target. The `wp_store_step₂` two-cell core: the
result cell is read-only, the target is written. Premise-free given the
resources (the store side-condition is internalized by
`storeLoc_int_any`). -/
theorem wp_frame_return_int {ta ra : Addr} {kind tkind : IntKind}
    {m : Int} {w : GoValue} {k}
    : ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.int tkind), w⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
          ∗ ta.id ↦ (⟨some (.int tkind), .int (tkind.normalize m) tkind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.returning (.frame [.base ta] [.base ra] [] k))
          @ s ; E {{ Φ }} := by
  iapply wp_store_step₂ (hnv := rfl)
  intro σ₁ hlookr hlookt
  have hload : loadMany σ₁ [Loc.base ra] = .ok [GoValue.int m kind] := by
    simp [loadMany, loadLoc, hlookr, Bind.bind, Except.bind]
  have hstore : storeMany σ₁ [Loc.base ta] [GoValue.int m kind]
      = .ok { σ₁ with heap := Heap.set σ₁.heap (.base ta) ⟨some (.int tkind), .int (tkind.normalize m) tkind⟩ } := by
    simp [storeMany, storeLoc_int_any hlookt m, Bind.bind, Except.bind]
  have hstep := Step.frameReturn (k := k) hload hstore
  refine ⟨hstep, ?_⟩
  intro c' s' hst
  obtain ⟨h1, h2⟩ := step_det (by trivial) hstep hst
  exact ⟨h1.symm, h2.symm⟩

/-- **Value frame exit on the FALL path**: normal completion (no explicit
`return`) at a frame with one pinned int result location and one int-typed
caller target — the machine's `Step.frameFall` performs the SAME
pinned-location read and caller-target store as `frameReturn`. This is
Go's "the surrounding function returns normally" exit after a recovered
panic (`panicResumeRecovered` resumes the frame on its fall path), and
the exit of any result-carrying function that falls off its end. Witness:
the recover composition walk (`Specs/GoldenRecover.lean`, `m := 7`). -/
theorem wp_frame_fall_int {ta ra : Addr} {kind tkind : IntKind}
    {m : Int} {w : GoValue} {k}
    : ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.int tkind), w⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
          ∗ ta.id ↦ (⟨some (.int tkind), .int (tkind.normalize m) tkind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.frame [.base ta] [.base ra] [] k))
          @ s ; E {{ Φ }} := by
  iapply wp_store_step₂ (hnv := rfl)
  intro σ₁ hlookr hlookt
  have hload : loadMany σ₁ [Loc.base ra] = .ok [GoValue.int m kind] := by
    simp [loadMany, loadLoc, hlookr, Bind.bind, Except.bind]
  have hstore : storeMany σ₁ [Loc.base ta] [GoValue.int m kind]
      = .ok { σ₁ with heap := Heap.set σ₁.heap (.base ta) ⟨some (.int tkind), .int (tkind.normalize m) tkind⟩ } := by
    simp [storeMany, storeLoc_int_any hlookt m, Bind.bind, Except.bind]
  have hstep := Step.frameFall (k := k) hload hstore
  refine ⟨hstep, ?_⟩
  intro c' s' hst
  obtain ⟨h1, h2⟩ := step_det (by trivial) hstep hst
  exact ⟨h1.symm, h2.symm⟩

/-- **Invariant-opening value frame exit** (the invariance-readout form of
`wp_frame_return_int`): the caller target lives in an Iris invariant with
content `Icnt` (`S`-shaped int cells, per `hint`), opened around the
single frame-exit store and closed at the written value. On the
`wp_store_step₂_inv` core. -/
theorem wp_frame_return_int_inv {ta ra : Addr} {kind tkind : IntKind}
    {m : Int} {S : HeapCell → Prop} {Icnt : IProp GF} {k} {N : Namespace}
    (hN : ↑N ⊆ E)
    (hint : ∀ cell, S cell → ∃ w', cell = ⟨some (.int tkind), w'⟩)
    (hopen : Icnt ⊢ iprop(∃ cell, ⌜S cell⌝ ∗ ta.id ↦ cell))
    (hclose : (iprop(ta.id ↦ (⟨some (.int tkind), .int (tkind.normalize m) tkind⟩ : HeapCell)) : IProp GF) ⊢ Icnt) :
    Iris.inv N Icnt
      ∗ ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.returning (.frame [.base ta] [.base ra] [] k))
          @ s ; E {{ Φ }} := by
  iapply wp_store_step₂_inv (hN := hN) (hnv := rfl) (hopen := hopen)
    (hclose := hclose)
  intro σ₁ oldcell hS hlookr hlookt
  obtain ⟨w', rfl⟩ := hint oldcell hS
  have hload : loadMany σ₁ [Loc.base ra] = .ok [GoValue.int m kind] := by
    simp [loadMany, loadLoc, hlookr, Bind.bind, Except.bind]
  have hstore : storeMany σ₁ [Loc.base ta] [GoValue.int m kind]
      = .ok { σ₁ with heap := Heap.set σ₁.heap (.base ta) ⟨some (.int tkind), .int (tkind.normalize m) tkind⟩ } := by
    simp [storeMany, storeLoc_int_any hlookt m, Bind.bind, Except.bind]
  have hstep := Step.frameReturn (k := k) hload hstore
  refine ⟨hstep, ?_⟩
  intro c' s' hst
  obtain ⟨h1, h2⟩ := step_det (by trivial) hstep hst
  exact ⟨h1.symm, h2.symm⟩

/-! ### Non-vacuity witnesses on the golden functions -/


/-- Witness for `wp_call_enter_arg1` on the CONCRETE golden `inc`: every
premise discharges by computation given the two genuinely-external pins
(program and method table). -/
theorem wp_call_enter_inc {xa : Addr} {locs : List Loc} {env k}
    (hprog : GoCoreGS.prog GF = GoldenSlice.sliceLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    iprop(∀ pa : Addr,
        pa.id ↦ (⟨some (.pointer (.int .int)), .addr (.base xa)⟩ : HeapCell) -∗
        WP (Config.exec GoldenSlice.incFunc.body [[("p", Loc.base pa)]] (.frame locs [] [] k))
          @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.addr (.base xa))
            (.callArgsK ⟨"inc"⟩ locs [] [] env k)) @ s ; E {{ Φ }} :=
  wp_call_enter_arg1
    (hfind := by rw [hprog, GoldenSlice.sliceLowered_funcs_eq]; rfl)
    (hargs := rfl)
    (hres := rfl)
    (hnodisp := fun σ h => by
      simp [dynamicDispatch?, methodInfoByFuncId?, h, hmeths, Bind.bind, Except.bind])
    (hnorm := fun σ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel])

/-- Witness for `wp_call_enter_ret1` on the CONCRETE golden `incViaCall`
(nullary, one int result `$res0` defaulting to 0). -/
theorem wp_call_enter_incViaCall {tl : Loc} {env k}
    (hprog : GoCoreGS.prog GF = GoldenSlice.sliceLowered.funcs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    iprop(∀ ra : Addr,
        ra.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell) -∗
        WP (Config.exec GoldenSlice.incViaCallFunc.body [[("$res0", Loc.base ra)]]
              (.frame [tl] [Loc.base ra] [] k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.addr tl)
            (.callTargetsK ⟨"incViaCall"⟩ [] [] [] env k)) @ s ; E {{ Φ }} :=
  wp_call_enter_ret1
    (hfind := by rw [hprog, GoldenSlice.sliceLowered_funcs_eq]; rfl)
    (hargs := rfl)
    (hres := rfl)
    (hnodisp := fun σ h => by
      simp [dynamicDispatch?, methodInfoByFuncId?, h, hmeths, Bind.bind, Except.bind])
    (hdef := fun σ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel])

end

end GoLean.Iris
