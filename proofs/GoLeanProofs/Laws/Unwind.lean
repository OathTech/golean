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
import GoLeanProofs.Laws.Control
import GoLeanProofs.Tactics.GoWalk

/-!
# Call-value, breakable, defer, and unwinding laws (proof-corpus catch-up)

The proof face of the sequential-coverage rungs merged since the reshape
(`docs/2026-07-26_proof-corpus-catchup-arc.md`): call-through-value (§8
lambda lifting), breakable scopes (switch), the defer chain, and the
unwinding arc's panic/recover machinery. Nearly every rule in these
families is a PURE deterministic step — state untouched, next
configuration a function of the current one — so the laws are
`wp_pure_det` instances whose premises are exactly the rule premises
(`pushDefer`/`panicPassthrough`/`recoverResult`/`chainNewestRecovered`
equations, all decidable on concrete continuations). The stateful
exceptions (frame entry for value calls and the defer drain, which
allocate) live below with the `wp_call_enter_*` shape.

Non-vacuity (wording corrected 2026-07-30, pre-merge audit): the
composition walk `wp_recover_catch_seven` (`defer rec(&result);
panic("boom")` returning 7) traverses the defer/panic/recover SPINE —
11 of this file's 21 laws. Every law the walk does not traverse has its
own NAMED instantiation witness at the bottom of this file, each
referenced from `proofs/Audit.lean` (anonymous `example` witnesses were
invisible to the reference gate — deleting one broke nothing).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris

set_option linter.unusedSimpArgs false

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-! ### Call through a value (§8): dispatch -/

/-- Dispatch a value call: evaluate the callee expression first, the
caller-target plans riding untouched (BUG-052 order pin). -/
@[go_walk_law]
theorem wp_call_value_start {targets : Array Assignee} {callee : Expr}
    {args : Array Expr} {plans : List (TargetShape × List Expr)} {env k}
    (hplan : targetsPlan targets.toList = some plans) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE callee env (.callValCalleeK plans args.toList env k))
        @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.callValue targets callee args) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.callValueStart hplan)

/-! ### Breakable scopes (switch bodies) -/

@[go_walk_law]
theorem wp_breakable_enter {b : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.exec b env (.breakableK k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.breakable b) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.breakableEnter)

@[go_walk_law]
theorem wp_breakable_done {k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.breakableK k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree]) (fun _ => Step.breakableDone)

@[go_walk_law]
theorem wp_breakable_break {k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.breaking (.breakableK k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree]) (fun _ => Step.breakableBreak)

/-! ### Defer registration -/

/-- `defer f(args)`: evaluate the callee expression first. -/
@[go_walk_law]
theorem wp_defer_stmt {callee : Expr} {args : Array Expr} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE callee env (.deferCalleeK args.toList env k))
        @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.deferCall callee args) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.deferStmt)

/-- A nullary deferred callee value registers onto the innermost frame's
chain (`pushDefer`, LIFO). -/
@[go_walk_law]
theorem wp_defer_register_noargs {cv : GoValue} {env k k'}
    (hcallee : deferrableCallee cv = true)
    (hpush : pushDefer (cv, []) k = some k') :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k') @ s ; E {{ Φ }}) ⊢
      WP (Config.retV cv (.deferCalleeK [] env k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree])
    (fun _ => Step.deferCalleeNoArgs hcallee hpush)

/-! ### The unwinding family (the unwinding arc's proof face) -/

/-- `panic(e)`: evaluate the payload. -/
@[go_walk_law]
theorem wp_panic_stmt {e : Expr} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE e env (.panicArgK k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.panicStmt e) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.panicStmt)

/-- The payload arrives: unwinding starts with a fresh one-entry chain. -/
@[go_walk_law]
theorem wp_panic_value {v : GoValue} {k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.panicking [⟨panicPayload v, false⟩] k) @ s ; E {{ Φ }}) ⊢
      WP (Config.retV v (.panicArgK k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree]) (fun _ => Step.panicArgValue)

/-- Unwinding strips a non-frame, non-marker continuation. -/
@[go_walk_law]
theorem wp_panic_unwind {chain : List PanicEntry} {k k'}
    (hpass : panicPassthrough k = some k') :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.panicking chain k') @ s ; E {{ Φ }}) ⊢
      WP (Config.panicking chain k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree])
    (fun _ => Step.panicUnwind hpass)

/-- Unwinding past a frame whose defers are exhausted: results NOT read. -/
@[go_walk_law]
theorem wp_panic_frame_empty {chain : List PanicEntry} {targets tenv results k}
    {w : Bool} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.panicking chain k) @ s ; E {{ Φ }}) ⊢
      WP (Config.panicking chain (.frame targets tenv results [] k w)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree])
    (fun _ => Step.panicFrameEmpty)

/-- A panic-path deferred call completed with the newest entry recovered:
the unwind cancels and the frame below resumes its NORMAL exit path. -/
@[go_walk_law]
theorem wp_panic_resume_recovered {chain : List PanicEntry} {k}
    (hrec : chainNewestRecovered chain = true) :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.panicResumeK chain k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree])
    (fun _ => Step.panicResumeRecovered hrec)

/-- …and with it unrecovered: unwinding resumes below. -/
@[go_walk_law]
theorem wp_panic_resume_continue {chain : List PanicEntry} {k}
    (hrec : chainNewestRecovered chain = false) :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.panicking chain k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.panicResumeK chain k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree])
    (fun _ => Step.panicResumeContinue hrec)

/-- A NEW panic unwinding through a suspended chain's marker merges
behind it. -/
@[go_walk_law]
theorem wp_panic_resume_merge {chain suspended : List PanicEntry} {k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.panicking (suspended ++ chain) k) @ s ; E {{ Φ }}) ⊢
      WP (Config.panicking chain (.panicResumeK suspended k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree])
    (fun _ => Step.panicResumeMerge)

/-- `recover()`: the continuation walk, as one deterministic step — the
whole called-directly-by-a-deferred-function rule is inside
`recoverResult`'s equation, decidable on any concrete continuation. -/
@[go_walk_law]
theorem wp_recover {env k} {v : GoValue} {k'}
    (hrec : recoverResult k = (v, k')) :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.retV v k') @ s ; E {{ Φ }}) ⊢
      WP (Config.evalE .recoverCall env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree])
    (fun _ => Step.evalRecover hrec)

/-! ### Small pure gaps the composition walk needs -/

@[go_walk_law]
theorem wp_eval_stringLit {v : GoString} {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.retV (.string v) k) @ s ; E {{ Φ }}) ⊢
      WP (Config.evalE (.stringLit v) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.evalStringLit)

/-- A NULLARY strict form whose apply is state-independent (`nil`
literals, default values). -/
@[go_walk_law]
theorem wp_eval_strict_nullary_pure {e : Expr} {op : StrictOp}
    {v : GoValue} {env k}
    (hplan : strictPlan e = some (op, []))
    (happly : ∀ σ : ExecState, applyStrictOp σ op [] = .ok (v, σ)) :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.retV v k) @ s ; E {{ Φ }}) ⊢
      WP (Config.evalE e env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree, stmtPlan])
    (fun σ => Step.evalStrictNullary hplan (happly σ))

/-- `return` at a VOID pure-barrier frame (no targets, no results, no
defers): resume the caller — the `.returning` twin of `wp_frame_fall`. -/
@[go_walk_law]
theorem wp_frame_return_void {tenv : LocalEnv} {k} {w : Bool} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.returning (.frame [] tenv [] [] k w)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree])
    (fun _ => Step.frameReturn)

/-! ### Frame entry for value calls and the defer drain (stateful)

The lambda-lifting protocol's proof face: a one-capture nullary closure
enters its frame with the captured value bound as the (pointer)
parameter. The same `enterFrame` core serves the direct value call, the
normal-path defer drain (both exits), and the PANIC-path drain — the four
laws differ only in the source configuration and the continuation the
body runs under. -/

/-- The shared frame-entry computation: a one-capture nullary closure's
`enterFrame` allocates exactly the parameter cell. -/
theorem enterFrame_cap1 {fid : FuncId} {func : Func} {pid : String}
    {pty : Ty} {cv cv' : GoValue}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) fid = some func)
    (hargs : func.args = #[⟨pid, pty⟩])
    (hres : func.results = #[])
    (hnodisp : ∀ σ : ExecState, σ.methods = GoCoreGS.methods GF →
      dynamicDispatch? σ func #[cv] = .ok none)
    (hnorm : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ pty cv = .ok cv') :
    ∀ σ₁ : ExecState, σ₁.functions = GoCoreGS.prog GF →
      σ₁.methods = GoCoreGS.methods GF → σ₁.types = GoCoreGS.types GF →
      enterFrame σ₁ fid [cv]
        = .ok (func, [[(pid, Loc.base ⟨σ₁.nextAddr⟩)]], [],
            { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, cv'⟩, nextAddr := σ₁.nextAddr + 1 }) := by
  intro σ₁ hfns hmeths htypes
  unfold enterFrame
  rw [hfns, hfind]
  simp [hargs, hres, Bind.bind, Except.bind, hnodisp σ₁ hmeths, bindParams,
    hnorm σ₁ htypes, ExecState.alloc, ExecState.freshLoc, allocDecls, pinResultLocs,
    LocalEnv.declare]
  exact hfns

/-- The shared WP lift for a deterministic frame-entry step that allocates
the one parameter cell: given the step (as a function of the entry
equation) the law's conclusion follows. Instantiated four times below. -/
private theorem wp_enter_cap1_core {fid : FuncId} {func : Func}
    {pid : String} {pty : Ty} {cv cv' : GoValue} {c₀ : Config}
    (hnv : ToVal.toVal c₀ = (none : Option Unit))
    (hcf : c₀.choiceFree)
    (henter : ∀ σ₁ : ExecState, σ₁.functions = GoCoreGS.prog GF →
      σ₁.methods = GoCoreGS.methods GF → σ₁.types = GoCoreGS.types GF →
      enterFrame σ₁ fid [cv]
        = .ok (func, [[(pid, Loc.base ⟨σ₁.nextAddr⟩)]], [],
            { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, cv'⟩, nextAddr := σ₁.nextAddr + 1 }))
    (kof : Cont)
    (hstep : ∀ σ₁ : ExecState,
      enterFrame σ₁ fid [cv]
        = .ok (func, [[(pid, Loc.base ⟨σ₁.nextAddr⟩)]], [],
            { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, cv'⟩, nextAddr := σ₁.nextAddr + 1 }) →
      Step c₀ σ₁
        (Config.exec func.body [[(pid, Loc.base ⟨σ₁.nextAddr⟩)]] kof)
        { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, cv'⟩, nextAddr := σ₁.nextAddr + 1 }) :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some pty, cv'⟩ : HeapCell) -∗
        WP (Config.exec func.body [[(pid, Loc.base pa)]] kof) @ s ; E {{ Φ }})
      ⊢ WP c₀ @ s ; E {{ Φ }} := by
  iintro Hcont
  iapply wp_lift_step (h := hnv)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  have hst := hstep σ₁ (henter σ₁ hfns hmeths htypes)
  have hdet : ∀ c' s', Step c₀ σ₁ c' s' →
      c' = Config.exec func.body [[(pid, Loc.base ⟨σ₁.nextAddr⟩)]] kof
        ∧ s' = { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, cv'⟩, nextAddr := σ₁.nextAddr + 1 } := by
    intro c' s' h
    obtain ⟨h1, h2⟩ := step_det hcf hst h
    exact ⟨h1.symm, h2.symm⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], _, _, [], GoPrimStep.step hst⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    obtain ⟨rfl, rfl⟩ := hdet _ _ st
    imod (genHeap_alloc (v := (⟨some pty, cv'⟩ : HeapCell)) hwf.fresh_get?)
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

/-- **Value-call frame entry, one capture / nullary / void** (the
`f()` closure shape): the funcVal callee arrives, one step allocates the
capture-parameter cell and enters the body. -/
theorem wp_call_value_enter_cap1 {fid : FuncId} {func : Func}
    {pid : String} {pty : Ty} {cv cv' : GoValue}
    {locs : List (TargetShape × List Expr)} {env k}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) fid = some func)
    (hargs : func.args = #[⟨pid, pty⟩])
    (hres : func.results = #[])
    (hnodisp : ∀ σ : ExecState, σ.methods = GoCoreGS.methods GF →
      dynamicDispatch? σ func #[cv] = .ok none)
    (hnorm : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ pty cv = .ok cv') :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some pty, cv'⟩ : HeapCell) -∗
        WP (Config.exec func.body [[(pid, Loc.base pa)]]
              (.frame locs env [] [] k func.wrapper))
          @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.funcVal fid [cv]) (.callValCalleeK locs [] env k))
          @ s ; E {{ Φ }} :=
  wp_enter_cap1_core rfl (by trivial)
    (enterFrame_cap1 hfind hargs hres hnodisp hnorm)
    (.frame locs env [] [] k func.wrapper)
    (fun _ henter => Step.callValCalleeEnter henter)

/-- **Defer drain on the RETURN path**, one capture / no arguments: the
deferred closure enters over the rest-of-chain frame; its results are
discarded (`[] [] []`). -/
theorem wp_frame_defer_return_cap1 {fid : FuncId} {func : Func}
    {pid : String} {pty : Ty} {cv cv' : GoValue}
    {targets : List (TargetShape × List Expr)} {tenv : LocalEnv}
    {results : List Loc} {ds : List (GoValue × List GoValue)} {k}
    {wsrc : Bool}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) fid = some func)
    (hargs : func.args = #[⟨pid, pty⟩])
    (hres : func.results = #[])
    (hnodisp : ∀ σ : ExecState, σ.methods = GoCoreGS.methods GF →
      dynamicDispatch? σ func #[cv] = .ok none)
    (hnorm : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ pty cv = .ok cv') :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some pty, cv'⟩ : HeapCell) -∗
        WP (Config.exec func.body [[(pid, Loc.base pa)]]
              (.frame [] [] [] [] (.frame targets tenv results ds k wsrc) func.wrapper))
          @ s ; E {{ Φ }})
      ⊢ WP (Config.returning
            (.frame targets tenv results ((.funcVal fid [cv], []) :: ds) k wsrc))
          @ s ; E {{ Φ }} :=
  wp_enter_cap1_core rfl (by trivial)
    (enterFrame_cap1 hfind hargs hres hnodisp hnorm)
    (.frame [] [] [] [] (.frame targets tenv results ds k wsrc) func.wrapper)
    (fun _ henter => Step.frameDeferReturn (by simpa using henter))

/-- **Defer drain on the FALL path** (normal completion), same shape. -/
theorem wp_frame_defer_fall_cap1 {fid : FuncId} {func : Func}
    {pid : String} {pty : Ty} {cv cv' : GoValue}
    {targets : List (TargetShape × List Expr)} {tenv : LocalEnv}
    {results : List Loc} {ds : List (GoValue × List GoValue)} {k}
    {wsrc : Bool}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) fid = some func)
    (hargs : func.args = #[⟨pid, pty⟩])
    (hres : func.results = #[])
    (hnodisp : ∀ σ : ExecState, σ.methods = GoCoreGS.methods GF →
      dynamicDispatch? σ func #[cv] = .ok none)
    (hnorm : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ pty cv = .ok cv') :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some pty, cv'⟩ : HeapCell) -∗
        WP (Config.exec func.body [[(pid, Loc.base pa)]]
              (.frame [] [] [] [] (.frame targets tenv results ds k wsrc) func.wrapper))
          @ s ; E {{ Φ }})
      ⊢ WP (Config.next
            (.frame targets tenv results ((.funcVal fid [cv], []) :: ds) k wsrc))
          @ s ; E {{ Φ }} :=
  wp_enter_cap1_core rfl (by trivial)
    (enterFrame_cap1 hfind hargs hres hnodisp hnorm)
    (.frame [] [] [] [] (.frame targets tenv results ds k wsrc) func.wrapper)
    (fun _ henter => Step.frameDeferFall (by simpa using henter))

/-- **Defer drain on the PANIC path**: the deferred closure runs above
the suspended chain's marker — the configuration `recover`'s walk
detects. The unwinding arc's central stateful law. -/
theorem wp_panic_frame_defer_cap1 {fid : FuncId} {func : Func}
    {pid : String} {pty : Ty} {cv cv' : GoValue} {wsrc : Bool}
    {chain : List PanicEntry}
    {targets : List (TargetShape × List Expr)} {tenv : LocalEnv}
    {results : List Loc} {ds : List (GoValue × List GoValue)} {k}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) fid = some func)
    (hargs : func.args = #[⟨pid, pty⟩])
    (hres : func.results = #[])
    (hnodisp : ∀ σ : ExecState, σ.methods = GoCoreGS.methods GF →
      dynamicDispatch? σ func #[cv] = .ok none)
    (hnorm : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ pty cv = .ok cv') :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some pty, cv'⟩ : HeapCell) -∗
        WP (Config.exec func.body [[(pid, Loc.base pa)]]
              (.frame [] [] [] []
                (.panicResumeK chain (.frame targets tenv results ds k wsrc))
                func.wrapper))
          @ s ; E {{ Φ }})
      ⊢ WP (Config.panicking chain
            (.frame targets tenv results ((.funcVal fid [cv], []) :: ds) k wsrc))
          @ s ; E {{ Φ }} :=
  wp_enter_cap1_core rfl (by trivial)
    (enterFrame_cap1 hfind hargs hres hnodisp hnorm)
    (.frame [] [] [] [] (.panicResumeK chain (.frame targets tenv results ds k wsrc)) func.wrapper)
    (fun _ henter => Step.panicFrameDefer (by simpa using henter))

end

/-! ### The composition witness: recover-catch returns 7

The non-vacuity witness for THIS ENTIRE FILE, and the proof corpus'
defer/recover composition entry: the concrete two-function program

    func rec(rp *int)          { if recover() != nil { *rp = 7 } }
    func recoverCatch() (r int) { defer rec(&r); panic("boom") }

walked end to end — defer registration, panic entry, unwinding through
the statement spine, the PANIC-path drain, the recover walk catching the
chain, the write through the captured pointer, the recovered marker
cancelling the unwind, and the normal frame exits. The differential twin
is `defer/recover-normal-return`'s family and the eval-test pin
`GoCore recover catches panic-path defer` (same shape, result 7). -/

namespace RecoverWitness

open GoLean.GoCore

abbrev recBody : Stmt :=
  .seqn #[
    .ifThenElse (.neqCmp (.interface ⟨"empty_interface"⟩) .recoverCall (.nil none))
      (.assign (.addr (.var "rp")) (.intLit 7 .int))
      (.seqn #[]),
    .returnStmt]

abbrev recFunc : Func :=
  { id := ⟨"rec$0"⟩, args := #[⟨"rp", .pointer (.int .int)⟩],
    results := #[], body := recBody }

abbrev catchBody : Stmt :=
  .seqn #[
    .deferCall (.funcVal ⟨"rec$0"⟩ #[.ref "r"]) #[],
    .panicStmt (.toInterface (.interface ⟨"empty_interface"⟩) .string
      (.stringLit (GoString.fromLeanString "boom"))),
    .returnStmt]

abbrev catchFunc : Func :=
  { id := ⟨"recoverCatch"⟩, args := #[], results := #[⟨"r", .int .int⟩],
    body := catchBody }

abbrev progFuncs : Array Func := #[recFunc, catchFunc]

/-- The panic payload after the `any`-conversion. -/
abbrev payload : GoValue :=
  .interface .string (.string (GoString.fromLeanString "boom"))

end RecoverWitness

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open RecoverWitness in
/-- **The recover walk, end to end**: from `recoverCatch`'s body over the
entry barrier frame, with the result cell at 0, execution panics,
recovers in the deferred closure, writes 7 through the captured pointer,
and resumes the caller with `r ↦ 7`. The deferred closure's parameter
cell is dropped at the end (affine). -/
theorem wp_recover_catch_seven {ra : Addr} {k}
    (hprog : GoCoreGS.prog GF = RecoverWitness.progFuncs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    ra.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int .int), .int 7 .int⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec catchBody [[("r", Loc.base ra)]]
              (.frame [] [] [] [] k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  -- catchBody's spine: seqn → defer → panic → (return, never reached)
  iapply wp_seqn
  simp only [seqCont, List.toList_toArray]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc1
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc2
  -- defer rec(&r): callee funcVal evaluates its capture (&r), registers
  iapply wp_defer_stmt
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc3
  iapply (wp_eval_strict (hplan := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc4
  iapply (wp_eval_ref (loc := Loc.base ra) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc5
  iapply (wp_strict_apply_pure
    (out := .funcVal ⟨"rec$0"⟩ [.addr (.base ra)])
    (happly := fun σ => rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc6
  iapply (wp_defer_register_noargs (hcallee := rfl) (hpush := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc7
  -- panic("boom"): payload converts to any, unwinding starts
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc8
  iapply wp_panic_stmt
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc9
  iapply (wp_eval_strict (hplan := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc10
  iapply wp_eval_stringLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc11
  iapply (wp_strict_apply_pure (out := RecoverWitness.payload)
    (happly := fun σ => by
      simp [applyStrictOp, canonicalDynamicTy, canonicalTy, canonicalTyFuel,
        Ty.mentionsUnsupported, Ty.mentionsUnsupportedFuel, typeResolutionFuel,
        RecoverWitness.payload, Bind.bind, Except.bind]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc12
  iapply wp_panic_value
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc13
  -- unwind the statement spine onto the frame, drain the deferred closure
  iapply (wp_panic_unwind (hpass := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc14
  iapply (wp_panic_frame_defer_cap1
    (func := RecoverWitness.recFunc)
    (cv' := .addr (.base ra))
    (hfind := by rw [hprog]; rfl)
    (hargs := rfl) (hres := rfl)
    (hnodisp := fun σ h => by
      simp [dynamicDispatch?, methodInfoByFuncId?, h, hmeths, Bind.bind,
        Except.bind])
    (hnorm := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel]))
  iintro %pa Hp
  -- the deferred closure's body: if recover() != nil { *rp = 7 }
  iapply wp_seqn
  simp only [seqCont, List.toList_toArray]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc15
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc16
  iapply wp_if_start
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc17
  iapply (wp_eval_strict (hplan := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc18
  -- recover(): the walk crosses the strict/if/seq frames, lands on the
  -- marker under the drain frame, marks the chain, returns the payload
  iapply (wp_recover (hrec := rfl))
  simp only [recoverResult, recoverThroughWrappers, markNewestRecovered,
    Option.map, Bool.false_eq_true, reduceIte]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc19
  iapply wp_strict_shift
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc20
  iapply (wp_eval_strict_nullary_pure (hplan := rfl)
    (happly := fun σ => rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc21
  iapply (wp_strict_apply_pure (out := .bool true)
    (happly := fun σ => by
      simp [applyStrictOp, panicPayload, valueEq, valueEqFuel, typeResolutionFuel,
        Bind.bind, Except.bind]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc22
  iapply wp_if_bool
  simp only [reduceIte]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc23
  -- *rp = 7 through the captured pointer
  iapply (wp_assign_start (e := .var "rp") (sh := .chain []) (ops := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc24
  iapply (wp_eval_var
    (cell := ⟨some (.pointer (.int .int)), .addr (.base ra)⟩) rfl)
  isplitl [Hp]
  · iexact Hp
  iintro Hp
  iapply (wp_tgtop_rhs rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc25
  iapply wp_eval_intLit
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc26
  iapply wp_rhs_stores_vals
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc27
  simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
  iapply (wp_assign_store (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int (IntKind.normalize .int 7) .int⟩)
    (fun σ₁ _ht hlook => storeLoc_int_cell hlook 7))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply wp_stores_done_nil
  -- the deferred closure returns; the recovered marker cancels the unwind
  iapply wp_seq_next
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc28
  iapply wp_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc29
  iapply wp_seq_return
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc30
  iapply wp_frame_return_void
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc31
  iapply (wp_panic_resume_recovered (hrec := rfl))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc32
  iapply wp_frame_fall
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc33
  rw [show IntKind.normalize .int 7 = 7 from by decide]
  iapply Hcont $$ Hr

/-! ### Instantiation witnesses for the laws the composition walk does
not traverse (the non-vacuity discipline: every premise discharged on a
concrete instance; the genuinely-external pins stay). -/

open RecoverWitness in
/-- Value-call frame entry witnessed on the concrete `rec$0` closure
(the `f()` shape of `functions/closure-share`). -/
theorem wp_call_value_enter_rec {ra : Addr}
    {locs : List (TargetShape × List Expr)} {env k}
    (hprog : GoCoreGS.prog GF = RecoverWitness.progFuncs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    iprop(∀ pa : Addr,
        pa.id ↦ (⟨some (.pointer (.int .int)), .addr (.base ra)⟩ : HeapCell) -∗
        WP (Config.exec RecoverWitness.recFunc.body [[("rp", Loc.base pa)]]
              (.frame locs env [] [] k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.funcVal ⟨"rec$0"⟩ [.addr (.base ra)])
            (.callValCalleeK locs [] env k)) @ s ; E {{ Φ }} :=
  wp_call_value_enter_cap1
    (func := RecoverWitness.recFunc) (cv' := .addr (.base ra))
    (hfind := by rw [hprog]; rfl)
    (hargs := rfl) (hres := rfl)
    (hnodisp := fun σ h => by
      simp [dynamicDispatch?, methodInfoByFuncId?, h, hmeths, Bind.bind,
        Except.bind])
    (hnorm := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel])

open RecoverWitness in
/-- Normal-path defer drain (return exit) witnessed on `rec$0`. -/
theorem wp_frame_defer_return_rec {ra : Addr}
    {targets : List (TargetShape × List Expr)} {tenv : LocalEnv}
    {results : List Loc} {k}
    (hprog : GoCoreGS.prog GF = RecoverWitness.progFuncs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    iprop(∀ pa : Addr,
        pa.id ↦ (⟨some (.pointer (.int .int)), .addr (.base ra)⟩ : HeapCell) -∗
        WP (Config.exec RecoverWitness.recFunc.body [[("rp", Loc.base pa)]]
              (.frame [] [] [] [] (.frame targets tenv results [] k)))
          @ s ; E {{ Φ }})
      ⊢ WP (Config.returning
            (.frame targets tenv results
              ((.funcVal ⟨"rec$0"⟩ [.addr (.base ra)], []) :: []) k))
          @ s ; E {{ Φ }} :=
  wp_frame_defer_return_cap1
    (func := RecoverWitness.recFunc) (cv' := .addr (.base ra))
    (hfind := by rw [hprog]; rfl)
    (hargs := rfl) (hres := rfl)
    (hnodisp := fun σ h => by
      simp [dynamicDispatch?, methodInfoByFuncId?, h, hmeths, Bind.bind,
        Except.bind])
    (hnorm := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel])

open RecoverWitness in
/-- Normal-path defer drain (fall exit), same instance. -/
theorem wp_frame_defer_fall_rec {ra : Addr}
    {targets : List (TargetShape × List Expr)} {tenv : LocalEnv}
    {results : List Loc} {k}
    (hprog : GoCoreGS.prog GF = RecoverWitness.progFuncs)
    (hmeths : GoCoreGS.methods GF = #[]) :
    iprop(∀ pa : Addr,
        pa.id ↦ (⟨some (.pointer (.int .int)), .addr (.base ra)⟩ : HeapCell) -∗
        WP (Config.exec RecoverWitness.recFunc.body [[("rp", Loc.base pa)]]
              (.frame [] [] [] [] (.frame targets tenv results [] k)))
          @ s ; E {{ Φ }})
      ⊢ WP (Config.next
            (.frame targets tenv results
              ((.funcVal ⟨"rec$0"⟩ [.addr (.base ra)], []) :: []) k))
          @ s ; E {{ Φ }} :=
  wp_frame_defer_fall_cap1
    (func := RecoverWitness.recFunc) (cv' := .addr (.base ra))
    (hfind := by rw [hprog]; rfl)
    (hargs := rfl) (hres := rfl)
    (hnodisp := fun σ h => by
      simp [dynamicDispatch?, methodInfoByFuncId?, h, hmeths, Bind.bind,
        Except.bind])
    (hnorm := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel])

/-- The remaining premise-carrying pure laws instantiated on concrete
shapes: dispatch, an unrecovered marker resuming the unwind, unwinding
past a spent frame, a chain merge, and the breakable family. NAMED
theorems (2026-07-30 pre-merge audit: as anonymous `example`s these were
structurally invisible to `Audit.lean`'s reference gate — deleting one
broke nothing), each referenced from the Audit non-vacuity block. -/
theorem wp_call_value_start_witness {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE (.var "f") env
        (.callValCalleeK [] [] env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.callValue #[] (.var "f") #[]) env k) @ s ; E {{ Φ }} :=
  wp_call_value_start (plans := []) rfl

theorem wp_panic_resume_continue_witness {k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.panicking [⟨.nil, false⟩] k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.panicResumeK [⟨.nil, false⟩] k)) @ s ; E {{ Φ }} :=
  wp_panic_resume_continue rfl

theorem wp_panic_frame_empty_witness {k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.panicking [⟨.nil, false⟩] k) @ s ; E {{ Φ }}) ⊢
      WP (Config.panicking [⟨.nil, false⟩] (.frame [] [] [] [] k)) @ s ; E {{ Φ }} :=
  wp_panic_frame_empty

theorem wp_panic_resume_merge_witness {k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.panicking ([⟨.nil, true⟩] ++ [⟨.nil, false⟩]) k)
        @ s ; E {{ Φ }}) ⊢
      WP (Config.panicking [⟨.nil, false⟩]
            (.panicResumeK [⟨.nil, true⟩] k)) @ s ; E {{ Φ }} :=
  wp_panic_resume_merge

theorem wp_breakable_enter_witness {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.exec (.seqn #[]) env (.breakableK k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.breakable (.seqn #[])) env k) @ s ; E {{ Φ }} :=
  wp_breakable_enter

theorem wp_breakable_break_witness {k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.breaking (.breakableK k)) @ s ; E {{ Φ }} :=
  wp_breakable_break

/-- `wp_breakable_done`'s witness (2026-07-30 pre-merge audit: the ONE
unwitnessed law in the family — a repo-wide grep found only its own
definition). An empty breakable body falls through: enter, empty seqn,
seq-done, breakable-done — all four laws discharged on the concrete
statement, composed end to end. -/
theorem wp_breakable_done_witness {env k} :
    WP (Config.next k) @ s ; E {{ Φ }} ⊢
      WP (Config.exec (.breakable (.seqn #[])) env k) @ s ; E {{ Φ }} := by
  iintro H
  iapply wp_breakable_enter
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc1
  iapply wp_seqn
  simp only [List.toList_toArray, seqCont]
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc2
  iapply wp_seq_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc3
  iapply wp_breakable_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hc4
  iexact H

end

end GoLean.Iris
