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
    (hnorm : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ pty v = .ok v') :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some pty, v'⟩ : HeapCell) -∗
        WP (Config.exec func.body [[(pid, Loc.base pa)]] (.frame locs [] [] k))
          @ s ; E {{ Φ }})
      ⊢ WP (Config.retV v (.callArgsK fid locs [] [] env k)) @ s ; E {{ Φ }} := by
  have henter : ∀ σ₁ : ExecState, σ₁.functions = GoCoreGS.prog GF →
      σ₁.methods = GoCoreGS.methods GF → σ₁.types = GoCoreGS.types GF →
      enterFrame σ₁ fid [v]
        = .ok (func, [[(pid, Loc.base ⟨σ₁.nextAddr⟩)]], [],
            { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, v'⟩, nextAddr := σ₁.nextAddr + 1 }) := by
    intro σ₁ hfns hmeths htypes
    unfold enterFrame
    rw [hfns, hfind]
    simp [hargs, hres, Bind.bind, Except.bind, hnodisp σ₁ hmeths, bindParams,
      hnorm σ₁ htypes, ExecState.alloc, ExecState.freshLoc, allocDecls,
      pinResultLocs, LocalEnv.declare]
    exact hfns
  iintro Hcont
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  have hstep := Step.callArgsDoneEnter (vals := []) (locs := locs) (env := env)
    (k := k) (henter σ₁ hfns hmeths htypes)
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
        exact ⟨hfns, hmeths, htypes, hwf.alloc⟩
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
    (hdef : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      defaultValue σ rty = .ok dv) :
    iprop(∀ ra : Addr, ra.id ↦ (⟨some rty, dv⟩ : HeapCell) -∗
        WP (Config.exec func.body [[(rid, Loc.base ra)]]
              (.frame [tl] [Loc.base ra] [] k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.addr tl) (.callTargetsK fid [] [] [] env k))
          @ s ; E {{ Φ }} := by
  have henter : ∀ σ₁ : ExecState, σ₁.functions = GoCoreGS.prog GF →
      σ₁.methods = GoCoreGS.methods GF → σ₁.types = GoCoreGS.types GF →
      enterFrame σ₁ fid []
        = .ok (func, [[(rid, Loc.base ⟨σ₁.nextAddr⟩)]], [Loc.base ⟨σ₁.nextAddr⟩],
            { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some rty, dv⟩, nextAddr := σ₁.nextAddr + 1 }) := by
    intro σ₁ hfns hmeths htypes
    unfold enterFrame
    rw [hfns, hfind]
    simp [hargs, hres, Bind.bind, Except.bind, hnodisp σ₁ hmeths, bindParams,
      hdef σ₁ htypes, ExecState.alloc, ExecState.freshLoc, allocDecls,
      pinResultLocs, LocalEnv.declare, LocalEnv.lookup, Scope.lookup]
    exact hfns
  iintro Hcont
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  have hstep := Step.callTargetsDoneEnter (locs := []) (env := env) (k := k)
    (rfl : valueAsLoc (.addr tl) = .ok tl) (henter σ₁ hfns hmeths htypes)
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
        exact ⟨hfns, hmeths, htypes, hwf.alloc⟩
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
  intro σ₁ _hfns _hmeths _htypes hlookr hlookt
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
  intro σ₁ _hfns _hmeths _htypes hlookr hlookt
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

/-! ## Frame entry through DYNAMIC DISPATCH (quorum pilot phase 4)

Go's interface call: the callsite names an *anchor* — the interface
method's `FuncId`, whose `Func` has no body — and `enterFrame` redirects
to the concrete implementation for the receiver box's dynamic type,
replacing the boxed receiver argument by the unboxed value
(`dynamicDispatch?` = `methodInfoByFuncId?` → `methodRecvInterfaceName?`
→ `concreteMethodForDynamic?`, with `needsDeref` handling `*T`'s method
set). Nothing about that is specific to any program: the law below fixes
only the ARITY (two parameters — receiver plus one — and two results),
exactly as `wp_call_enter_arg1`/`wp_call_enter_ret1`/`enterFrame_cap1`
fix theirs. Anchor id, concrete callee, dynamic type, parameter and
result names/types, and every value are law variables.

Widening owed (recorded, not silently target-fitted): general
`(n args, m results)` frame entry needs the list-indexed allocation core
(`wp_alloc_step₄`'s scope note) plus list-shaped `bindParams`/`allocDecls`
equations. Comparison with Perennial: `new/golang/defn/interface.v`'s
`interface.get`/method resolution is receiver-generic and arity-generic
because GooseLang function values are curried closures, so no arity
family arises there; ours is arity-specialized for the same reason the
`cap1` family is — GoCore's frame entry allocates a cell per parameter in
ONE step, so the WP law must name them. -/

/-- `bindParams` at two parameters: two normalized allocations, innermost
scope carrying both bindings (declaration order, so the second parameter
is at the head). General — no program, type or value fixed. -/
theorem bindParams₂ {σ : ExecState} {p₀ p₁ : Param} {v₀ v₁ w₀ w₁ : GoValue}
    (h0 : normalizeValueForTy σ p₀.typ v₀ = .ok w₀)
    (h1 : normalizeValueForTy (allocMany σ [⟨some p₀.typ, w₀⟩]) p₁.typ v₁
      = .ok w₁) :
    bindParams [] σ [p₀, p₁] [v₀, v₁]
      = .ok ([[(p₁.id, Loc.base ⟨σ.nextAddr + 1⟩),
               (p₀.id, Loc.base ⟨σ.nextAddr⟩)]],
          allocMany σ [⟨some p₀.typ, w₀⟩, ⟨some p₁.typ, w₁⟩]) := by
  simp only [allocMany] at h1 ⊢
  simp [bindParams, h0, h1, ExecState.alloc, ExecState.freshLoc,
    LocalEnv.declare, Bind.bind, Except.bind]

/-- `allocDecls` at two results: two default-valued allocations. General. -/
theorem allocDecls₂ {σ : ExecState} {env : LocalEnv} {r₀ r₁ : Param}
    {d₀ d₁ : GoValue}
    (h0 : defaultValue σ r₀.typ = .ok d₀)
    (h1 : defaultValue (allocMany σ [⟨some r₀.typ, d₀⟩]) r₁.typ = .ok d₁) :
    allocDecls env σ [r₀, r₁]
      = .ok (((env.declare r₀.id (Loc.base ⟨σ.nextAddr⟩)).declare r₁.id
                (Loc.base ⟨σ.nextAddr + 1⟩)),
          allocMany σ [⟨some r₀.typ, d₀⟩, ⟨some r₁.typ, d₁⟩]) := by
  simp only [allocMany] at h1 ⊢
  simp [allocDecls, h0, h1, ExecState.alloc, ExecState.freshLoc,
    Bind.bind, Except.bind]

/-- **Frame entry through an interface anchor — two arguments (receiver +
one) and two results.** The last argument value arrives at the
`callArgsK` frame; ONE machine step looks the anchor up, redirects to the
concrete method for the receiver box's dynamic type, allocates the two
parameter cells (normalized at the CONCRETE method's declared parameter
types — this is what needs the `σ.types` pin) and the two result cells
(defaulted at their declared types), pins the result locations, and
enters the body. The continuation receives the four machine-chosen
addresses.

All the state-quantified premises carry the `σ.types = GoCoreGS.types GF`
hypothesis: without it they would be false at any named type, and the law
vacuous (`Laws/QuorumOps.typeEnv_pin_is_load_bearing`). -/
theorem wp_call_dynamic_enter₂ {fid : FuncId} {anchor concrete : Func}
    {recvBox recv v₁ w₀ w₁ dv₀ dv₁ : GoValue}
    {pid₀ pid₁ rid₀ rid₁ : String} {pty₀ pty₁ rty₀ rty₁ : Ty}
    {locs : List Loc} {env k}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) fid = some anchor)
    (hanchor : anchor.args.size = 2)
    (hdisp : ∀ σ : ExecState, σ.functions = GoCoreGS.prog GF →
      σ.methods = GoCoreGS.methods GF → σ.types = GoCoreGS.types GF →
      dynamicDispatch? σ anchor #[recvBox, v₁] = .ok (some (concrete, #[recv, v₁])))
    (hargs : concrete.args = #[⟨pid₀, pty₀⟩, ⟨pid₁, pty₁⟩])
    (hres : concrete.results = #[⟨rid₀, rty₀⟩, ⟨rid₁, rty₁⟩])
    (hrid : (rid₁ == rid₀) = false)
    (hnorm₀ : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ pty₀ recv = .ok w₀)
    (hnorm₁ : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ pty₁ v₁ = .ok w₁)
    (hdef₀ : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      defaultValue σ rty₀ = .ok dv₀)
    (hdef₁ : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      defaultValue σ rty₁ = .ok dv₁) :
    iprop(∀ a₀ : Addr, ∀ a₁ : Addr, ∀ a₂ : Addr, ∀ a₃ : Addr,
        a₀.id ↦ (⟨some pty₀, w₀⟩ : HeapCell)
          ∗ a₁.id ↦ (⟨some pty₁, w₁⟩ : HeapCell)
          ∗ a₂.id ↦ (⟨some rty₀, dv₀⟩ : HeapCell)
          ∗ a₃.id ↦ (⟨some rty₁, dv₁⟩ : HeapCell) -∗
        WP (Config.exec concrete.body
              [[(rid₁, Loc.base a₃), (rid₀, Loc.base a₂),
                (pid₁, Loc.base a₁), (pid₀, Loc.base a₀)]]
              (.frame locs [Loc.base a₂, Loc.base a₃] [] k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV v₁ (.callArgsK fid locs [recvBox] [] env k))
          @ s ; E {{ Φ }} := by
  have henter : ∀ σ : ExecState, σ.functions = GoCoreGS.prog GF →
      σ.methods = GoCoreGS.methods GF → σ.types = GoCoreGS.types GF →
      enterFrame σ fid [recvBox, v₁]
        = .ok (concrete,
            [[(rid₁, Loc.base ⟨σ.nextAddr + 3⟩), (rid₀, Loc.base ⟨σ.nextAddr + 2⟩),
              (pid₁, Loc.base ⟨σ.nextAddr + 1⟩), (pid₀, Loc.base ⟨σ.nextAddr⟩)]],
            [Loc.base ⟨σ.nextAddr + 2⟩, Loc.base ⟨σ.nextAddr + 3⟩],
            allocMany σ [⟨some pty₀, w₀⟩, ⟨some pty₁, w₁⟩,
                         ⟨some rty₀, dv₀⟩, ⟨some rty₁, dv₁⟩]) := by
    intro σ hfns hmeths htypes
    have hbind := bindParams₂ (σ := σ) (p₀ := ⟨pid₀, pty₀⟩) (p₁ := ⟨pid₁, pty₁⟩)
      (v₀ := recv) (v₁ := v₁) (w₀ := w₀) (w₁ := w₁)
      (hnorm₀ σ htypes) (hnorm₁ _ htypes)
    have hdecl := allocDecls₂
      (σ := allocMany σ [⟨some pty₀, w₀⟩, ⟨some pty₁, w₁⟩])
      (env := [[(pid₁, Loc.base ⟨σ.nextAddr + 1⟩), (pid₀, Loc.base ⟨σ.nextAddr⟩)]])
      (r₀ := ⟨rid₀, rty₀⟩) (r₁ := ⟨rid₁, rty₁⟩) (d₀ := dv₀) (d₁ := dv₁)
      (hdef₀ _ htypes) (hdef₁ _ htypes)
    simp only [allocMany] at hbind hdecl ⊢
    unfold enterFrame
    rw [hfns, hfind]
    simp [hanchor, hdisp σ hfns hmeths htypes, hargs, hres, hbind, hdecl,
      pinResultLocs, LocalEnv.declare, LocalEnv.lookup, Scope.lookup, hrid,
      Bind.bind, Except.bind]
    exact hfns
  iintro Hcont
  iapply (wp_alloc_step₄ (hnv := rfl)
    (kof := fun a₀ a₁ a₂ a₃ => Config.exec concrete.body
      [[(rid₁, Loc.base a₃), (rid₀, Loc.base a₂),
        (pid₁, Loc.base a₁), (pid₀, Loc.base a₀)]]
      (.frame locs [Loc.base a₂, Loc.base a₃] [] k))
    (hred := by
      intro σ₁ hfns hmeths htypes
      have hstep := Step.callArgsDoneEnter (vals := [recvBox]) (locs := locs)
        (env := env) (k := k) (by simpa using henter σ₁ hfns hmeths htypes)
      refine ⟨hstep, ?_⟩
      intro c' s' hst
      obtain ⟨h1, h2⟩ := step_det (by trivial) hstep hst
      exact ⟨h1.symm, h2.symm⟩))
  iexact Hcont

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
    (hnorm := fun σ _ => by
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
    (hdef := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel])

end

end GoLean.Iris
