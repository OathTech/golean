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
non-vacuity witnesses (`wp_call_enter_inc`, `wp_call_enter_incViaCall` —
relocated to `Specs/GoldenSliceWP.lean` at the proof-automation close-out
so this GENERAL module imports no `Specs/*` pin, per the layering
doctrine; the genuinely-external premises are the program/method-table
pins, as in the old `wp_inc_call`). `wp_frame_return_int` is the value frame exit
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

/-- Dispatch a call with at least one argument: evaluate the first
argument, the caller-target PLANS riding untouched (BUG-052 order pin:
the call evaluates first, target operands at frame exit — gc's realized
point inside spec §Order of evaluation's unordered carve-out). -/
@[go_walk_law]
theorem wp_call_start {targets : Array Assignee} {fid : FuncId}
    {args : Array Expr} {plans : List (TargetShape × List Expr)}
    {a : Expr} {rest : List Expr} {env k}
    (hplan : targetsPlan targets.toList = some plans)
    (hargs : args.toList = a :: rest) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE a env (.callArgsK fid plans [] rest env k))
        @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.call targets fid args) env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.callStart hplan hargs)

/-- **Frame entry, unary argument / void result** (the `inc(&x)` shape):
the last argument value arrives, and one step allocates the parameter
cell (normalized at declared type) and enters the body under the fresh
one-binding frame environment. The continuation receives the
machine-chosen cell (`∀ pa`). -/
theorem wp_call_enter_arg1 {fid : FuncId} {func : Func} {pid : String}
    {pty : Ty} {v v' : GoValue}
    {plans : List (TargetShape × List Expr)} {env k}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) fid = some func)
    (hargs : func.args = #[⟨pid, pty⟩])
    (hres : func.results = #[])
    (hnodisp : ∀ σ : ExecState, σ.methods = GoCoreGS.methods GF →
      dynamicDispatch? σ func #[v] = .ok none)
    (hnorm : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ pty v = .ok v') :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some pty, v'⟩ : HeapCell) -∗
        WP (Config.exec func.body [[(pid, Loc.base pa)]]
              (.frame plans env [] [] k func.wrapper))
          @ s ; E {{ Φ }})
      ⊢ WP (Config.retV v (.callArgsK fid plans [] [] env k)) @ s ; E {{ Φ }} := by
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
  have hstep := Step.callArgsDoneEnter (vals := []) (plans := plans) (env := env)
    (k := k) (henter σ₁ hfns hmeths htypes)
  have hdet : ∀ c' s',
      Step (.retV v (.callArgsK fid plans [] [] env k)) σ₁ c' s' →
      c' = Config.exec func.body [[(pid, Loc.base ⟨σ₁.nextAddr⟩)]]
             (.frame plans env [] [] k func.wrapper)
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
`r = incViaCall()` shape): the call statement's ONE step (BUG-052 order
pin — no target operand evaluates pre-call) allocates the result cell at
its default and enters the body; the frame pins the caller-target PLAN
and the caller environment for the post-call write-back, plus the
result location. -/
theorem wp_call_enter_ret1 {targets : Array Assignee} {fid : FuncId}
    {func : Func} {rid : String}
    {rty : Ty} {dv : GoValue} {plans : List (TargetShape × List Expr)} {env k}
    (hplan : targetsPlan targets.toList = some plans)
    (hfind : findFunctionIn? (GoCoreGS.prog GF) fid = some func)
    (hargs : func.args = #[])
    (hres : func.results = #[⟨rid, rty⟩])
    (hnodisp : ∀ σ : ExecState, σ.methods = GoCoreGS.methods GF →
      dynamicDispatch? σ func #[] = .ok none)
    (hdef : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      defaultValue σ rty = .ok dv) :
    iprop(∀ ra : Addr, ra.id ↦ (⟨some rty, dv⟩ : HeapCell) -∗
        WP (Config.exec func.body [[(rid, Loc.base ra)]]
              (.frame plans env [Loc.base ra] [] k func.wrapper)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call targets fid #[]) env k)
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
  have hstep := Step.callImmediate (env := env) (k := k)
    hplan rfl (henter σ₁ hfns hmeths htypes)
  have hdet : ∀ c' s',
      Step (.exec (.call targets fid #[]) env k) σ₁ c' s' →
      c' = Config.exec func.body [[(rid, Loc.base ⟨σ₁.nextAddr⟩)]]
             (.frame plans env [Loc.base ⟨σ₁.nextAddr⟩] [] k func.wrapper)
        ∧ s' = { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some rty, dv⟩, nextAddr := σ₁.nextAddr + 1 } := by
    intro c' s' hst
    obtain ⟨h1, h2⟩ := step_det (by simp [Config.choiceFree, stmtPlan]) hstep hst
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
theorem wp_frame_return_int {x : String} {tenv : LocalEnv} {ta ra : Addr}
    {kind tkind : IntKind} {m : Int} {w : GoValue} {k} {wf : Bool}
    (hres : LocalEnv.lookup tenv x = some (.base ta)) :
    ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.int tkind), w⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
          ∗ ta.id ↦ (⟨some (.int tkind), .int (tkind.normalize m) tkind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.returning (.frame [(.chain [], [.ref x])] tenv [.base ra] [] k wf))
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Ht, Hcont⟩
  -- Step 1 (BUG-052 order pin): the frame exit READS the pinned result
  -- cell and enters the tgtOpK spine — the caller-target OPERANDS
  -- evaluate POST-CALL in the caller's environment (gc's realized
  -- point), then the store.
  iapply (wp_det_step_keep
    (P := iprop(ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)))
    (c₁ := Config.evalE (.ref x) tenv (.tgtOpK (.chain []) [] [] [] []
      .vals [] [.int m kind] (.seqn #[]) tenv k))
    (hnv := rfl)
    (hred := fun σ₁ _hfns _hmeths _htypes => by
      iintro ⟨Hσ, Hpt⟩
      ihave %Hmap : ⌜get? (heapToMap σ₁.heap) ra.id
          = some (⟨some (.int kind), .int m kind⟩ : HeapCell)⌝ $$ [Hσ Hpt]
      · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
        itrivial
      have hlook : Heap.lookup σ₁.heap (.base ra)
          = some ⟨some (.int kind), .int m kind⟩ := by
        rw [get?_heapToMap] at Hmap; simpa using Hmap
      have hload : loadMany σ₁ [Loc.base ra] = .ok [GoValue.int m kind] := by
        simp [loadMany, loadLoc, hlook, Bind.bind, Except.bind]
      imodintro
      ipureintro
      refine ⟨Step.frameReturnTargets hload, ?_⟩
      intro c' s' hst
      obtain ⟨h1, h2⟩ := step_det (by trivial) (Step.frameReturnTargets hload) hst
      exact ⟨h1.symm, h2.symm⟩))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  -- Step 2: the target operand (post-call, phase 1).
  iapply (wp_eval_ref hres)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  -- Step 3: the target completes; phase 2 begins.
  iapply (wp_tgtop_stores (r := .chain (.addr (.base ta)) [] []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  simp only [List.nil_append]
  -- Step 4: the store (deferred check firing here).
  iapply (wp_assign_store_loc
    (oldcell := ⟨some (.int tkind), w⟩)
    (newcell := ⟨some (.int tkind), .int (tkind.normalize m) tkind⟩)
    (hstore := fun σ₁ _ht hlook => storeLoc_int_any hlook m))
  isplitl [Ht]
  · iexact Ht
  iintro Ht
  iapply wp_stores_done_nil
  iapply Hcont $$ [$Hr $Ht]

/-- **Value frame exit on the FALL path**: normal completion (no explicit
`return`) at a frame with one pinned int result location and one int-typed
caller target — the machine's `Step.frameFall` performs the SAME
pinned-location read and caller-target store as `frameReturn`. This is
Go's "the surrounding function returns normally" exit after a recovered
panic (`panicResumeRecovered` resumes the frame on its fall path), and
the exit of any result-carrying function that falls off its end. Witness:
the recover composition walk (`Specs/GoldenRecover.lean`, `m := 7`). -/
theorem wp_frame_fall_int {x : String} {tenv : LocalEnv} {ta ra : Addr}
    {kind tkind : IntKind} {m : Int} {w : GoValue} {k} {wf : Bool}
    (hres : LocalEnv.lookup tenv x = some (.base ta)) :
    ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.int tkind), w⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
          ∗ ta.id ↦ (⟨some (.int tkind), .int (tkind.normalize m) tkind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.frame [(.chain [], [.ref x])] tenv [.base ra] [] k wf))
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Ht, Hcont⟩
  -- Step 1 (BUG-052 order pin): the frame exit READS the pinned result
  -- cell and enters the tgtOpK spine — the caller-target OPERANDS
  -- evaluate POST-CALL in the caller's environment (gc's realized
  -- point), then the store.
  iapply (wp_det_step_keep
    (P := iprop(ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)))
    (c₁ := Config.evalE (.ref x) tenv (.tgtOpK (.chain []) [] [] [] []
      .vals [] [.int m kind] (.seqn #[]) tenv k))
    (hnv := rfl)
    (hred := fun σ₁ _hfns _hmeths _htypes => by
      iintro ⟨Hσ, Hpt⟩
      ihave %Hmap : ⌜get? (heapToMap σ₁.heap) ra.id
          = some (⟨some (.int kind), .int m kind⟩ : HeapCell)⌝ $$ [Hσ Hpt]
      · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
        itrivial
      have hlook : Heap.lookup σ₁.heap (.base ra)
          = some ⟨some (.int kind), .int m kind⟩ := by
        rw [get?_heapToMap] at Hmap; simpa using Hmap
      have hload : loadMany σ₁ [Loc.base ra] = .ok [GoValue.int m kind] := by
        simp [loadMany, loadLoc, hlook, Bind.bind, Except.bind]
      imodintro
      ipureintro
      refine ⟨Step.frameFallTargets hload, ?_⟩
      intro c' s' hst
      obtain ⟨h1, h2⟩ := step_det (by trivial) (Step.frameFallTargets hload) hst
      exact ⟨h1.symm, h2.symm⟩))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  -- Step 2: the target operand (post-call, phase 1).
  iapply (wp_eval_ref hres)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  -- Step 3: the target completes; phase 2 begins.
  iapply (wp_tgtop_stores (r := .chain (.addr (.base ta)) [] []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  simp only [List.nil_append]
  -- Step 4: the store (deferred check firing here).
  iapply (wp_assign_store_loc
    (oldcell := ⟨some (.int tkind), w⟩)
    (newcell := ⟨some (.int tkind), .int (tkind.normalize m) tkind⟩)
    (hstore := fun σ₁ _ht hlook => storeLoc_int_any hlook m))
  isplitl [Ht]
  · iexact Ht
  iintro Ht
  iapply wp_stores_done_nil
  iapply Hcont $$ [$Hr $Ht]

/-- **Invariant-opening value frame exit** (the invariance-readout form of
`wp_frame_return_int`): the caller target lives in an Iris invariant with
content `Icnt` (`S`-shaped int cells, per `hint`), opened around the
single frame-exit store and closed at the written value. On the
`wp_store_step₂_inv` core. -/
theorem wp_frame_return_int_inv {x : String} {tenv : LocalEnv}
    {ta ra : Addr} {kind tkind : IntKind}
    {m : Int} {S : HeapCell → Prop} {Icnt : IProp GF} {k} {wf : Bool} {N : Namespace}
    (hN : ↑N ⊆ E)
    (hres : LocalEnv.lookup tenv x = some (.base ta))
    (hint : ∀ cell, S cell → ∃ w', cell = ⟨some (.int tkind), w'⟩)
    (hopen : Icnt ⊢ iprop(∃ cell, ⌜S cell⌝ ∗ ta.id ↦ cell))
    (hclose : (iprop(ta.id ↦ (⟨some (.int tkind), .int (tkind.normalize m) tkind⟩ : HeapCell)) : IProp GF) ⊢ Icnt) :
    Iris.inv N Icnt
      ∗ ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.returning (.frame [(.chain [], [.ref x])] tenv [.base ra] [] k wf))
          @ s ; E {{ Φ }} := by
  iintro ⟨HinvT, Hr, Hcont⟩
  -- Step 1 (BUG-052 order pin): the exit READS the result cell and
  -- enters the tgtOpK spine; the invariant-managed target write is the
  -- separate store step below, opened around exactly that step.
  iapply (wp_det_step_keep
    (P := iprop(ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)))
    (c₁ := Config.evalE (.ref x) tenv (.tgtOpK (.chain []) [] [] [] []
      .vals [] [.int m kind] (.seqn #[]) tenv k))
    (hnv := rfl)
    (hred := fun σ₁ _hfns _hmeths _htypes => by
      iintro ⟨Hσ, Hpt⟩
      ihave %Hmap : ⌜get? (heapToMap σ₁.heap) ra.id
          = some (⟨some (.int kind), .int m kind⟩ : HeapCell)⌝ $$ [Hσ Hpt]
      · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
        itrivial
      have hlook : Heap.lookup σ₁.heap (.base ra)
          = some ⟨some (.int kind), .int m kind⟩ := by
        rw [get?_heapToMap] at Hmap; simpa using Hmap
      have hload : loadMany σ₁ [Loc.base ra] = .ok [GoValue.int m kind] := by
        simp [loadMany, loadLoc, hlook, Bind.bind, Except.bind]
      imodintro
      ipureintro
      refine ⟨Step.frameReturnTargets hload, ?_⟩
      intro c' s' hst
      obtain ⟨h1, h2⟩ := step_det (by trivial) (Step.frameReturnTargets hload) hst
      exact ⟨h1.symm, h2.symm⟩))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  -- Step 2: the target operand (post-call, phase 1).
  iapply (wp_eval_ref hres)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  -- Step 3: the target completes; phase 2 begins.
  iapply (wp_tgtop_stores (r := .chain (.addr (.base ta)) [] []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  simp only [List.nil_append]
  -- Step 4: the store, the invariant opened around exactly this step.
  iapply (wp_store_step₂_inv (pa := ra)
    (pcell := ⟨some (.int kind), .int m kind⟩)
    (hN := hN) (hnv := rfl) (hopen := hopen) (hclose := hclose)
    (hred := fun σ₁ oldcell hS _hlookp hlook => by
      obtain ⟨w', rfl⟩ := hint oldcell hS
      have hst : storeTarget σ₁ (.chain (.addr (.base ta)) [] []) (.int m kind) = .ok { σ₁ with heap := Heap.set σ₁.heap (.base ta) (⟨some (.int tkind), .int (tkind.normalize m) tkind⟩ : HeapCell) } := by
        simp [storeTarget, resolveChain, valueAsLoc, Bind.bind, Except.bind,
          storeLoc_int_any hlook m]
      refine ⟨Step.storeStep hst, ?_⟩
      intro c' s' hst'
      obtain ⟨h1, h2⟩ := step_det (by trivial) (Step.storeStep hst) hst'
      exact ⟨h1.symm, h2.symm⟩))
  isplitl [HinvT]
  · iexact HinvT
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply wp_stores_done_nil
  iapply Hcont $$ Hr

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

/-- `allocDecls` at ONE result: a single default-valued allocation.
General. -/
theorem allocDecls₁ {σ : ExecState} {env : LocalEnv} {r₀ : Param} {d₀ : GoValue}
    (h0 : defaultValue σ r₀.typ = .ok d₀) :
    allocDecls env σ [r₀]
      = .ok (env.declare r₀.id (Loc.base ⟨σ.nextAddr⟩),
          allocMany σ [⟨some r₀.typ, d₀⟩]) := by
  simp only [allocMany]
  simp [allocDecls, h0, ExecState.alloc, ExecState.freshLoc,
    Bind.bind, Except.bind]

/-- **Frame entry, two arguments / ONE result, STATIC callee** — the
arity of every quorum entry point (`run(c, l) Index`,
`(MajorityConfig).CommittedIndex(l) Index`). Sibling of `wp_call_enter₂`
with the result list shortened by one; three cells are allocated in the
single step, so it rides the `wp_alloc_step₃` core. Callee, names, types
and values are law variables; only the arity is fixed (the family's
standing scope note, `wp_alloc_step₄`). -/
theorem wp_call_enter₂₁ {fid : FuncId} {func : Func}
    {v₀ v₁ w₀ w₁ dv₀ : GoValue}
    {pid₀ pid₁ rid₀ : String} {pty₀ pty₁ rty₀ : Ty}
    {locs : List (TargetShape × List Expr)} {env k}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) fid = some func)
    (hargs : func.args = #[⟨pid₀, pty₀⟩, ⟨pid₁, pty₁⟩])
    (hres : func.results = #[⟨rid₀, rty₀⟩])
    (hnodisp : ∀ σ : ExecState, σ.functions = GoCoreGS.prog GF →
      σ.methods = GoCoreGS.methods GF → σ.types = GoCoreGS.types GF →
      dynamicDispatch? σ func #[v₀, v₁] = .ok none)
    (hnorm₀ : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ pty₀ v₀ = .ok w₀)
    (hnorm₁ : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ pty₁ v₁ = .ok w₁)
    (hdef₀ : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      defaultValue σ rty₀ = .ok dv₀) :
    iprop(∀ a₀ : Addr, ∀ a₁ : Addr, ∀ a₂ : Addr,
        a₀.id ↦ (⟨some pty₀, w₀⟩ : HeapCell)
          ∗ a₁.id ↦ (⟨some pty₁, w₁⟩ : HeapCell)
          ∗ a₂.id ↦ (⟨some rty₀, dv₀⟩ : HeapCell) -∗
        WP (Config.exec func.body
              [[(rid₀, Loc.base a₂), (pid₁, Loc.base a₁), (pid₀, Loc.base a₀)]]
              (.frame locs env [Loc.base a₂] [] k func.wrapper)) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV v₁ (.callArgsK fid locs [v₀] [] env k))
          @ s ; E {{ Φ }} := by
  have henter : ∀ σ : ExecState, σ.functions = GoCoreGS.prog GF →
      σ.methods = GoCoreGS.methods GF → σ.types = GoCoreGS.types GF →
      enterFrame σ fid [v₀, v₁]
        = .ok (func,
            [[(rid₀, Loc.base ⟨σ.nextAddr + 2⟩),
              (pid₁, Loc.base ⟨σ.nextAddr + 1⟩), (pid₀, Loc.base ⟨σ.nextAddr⟩)]],
            [Loc.base ⟨σ.nextAddr + 2⟩],
            allocMany σ [⟨some pty₀, w₀⟩, ⟨some pty₁, w₁⟩, ⟨some rty₀, dv₀⟩]) := by
    intro σ hfns hmeths htypes
    have hbind := bindParams₂ (σ := σ) (p₀ := ⟨pid₀, pty₀⟩) (p₁ := ⟨pid₁, pty₁⟩)
      (v₀ := v₀) (v₁ := v₁) (w₀ := w₀) (w₁ := w₁)
      (hnorm₀ σ htypes) (hnorm₁ _ htypes)
    have hdecl := allocDecls₁
      (σ := allocMany σ [⟨some pty₀, w₀⟩, ⟨some pty₁, w₁⟩])
      (env := [[(pid₁, Loc.base ⟨σ.nextAddr + 1⟩), (pid₀, Loc.base ⟨σ.nextAddr⟩)]])
      (r₀ := ⟨rid₀, rty₀⟩) (d₀ := dv₀) (hdef₀ _ htypes)
    simp only [allocMany] at hbind hdecl ⊢
    unfold enterFrame
    rw [hfns, hfind]
    simp [hnodisp σ hfns hmeths htypes, hargs, hres, hbind, hdecl,
      pinResultLocs, LocalEnv.declare, LocalEnv.lookup, Scope.lookup,
      Bind.bind, Except.bind]
    exact hfns
  iintro Hcont
  iapply (wp_alloc_step₃ (hnv := rfl)
    (kof := fun a₀ a₁ a₂ => Config.exec func.body
      [[(rid₀, Loc.base a₂), (pid₁, Loc.base a₁), (pid₀, Loc.base a₀)]]
      (.frame locs env [Loc.base a₂] [] k func.wrapper))
    (hred := by
      intro σ₁ hfns hmeths htypes
      have hstep := Step.callArgsDoneEnter (vals := [v₀]) (plans := locs)
        (env := env) (k := k) (by simpa using henter σ₁ hfns hmeths htypes)
      refine ⟨hstep, ?_⟩
      intro c' s' hst
      obtain ⟨h1, h2⟩ := step_det (by trivial) hstep hst
      exact ⟨h1.symm, h2.symm⟩))
  iexact Hcont

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
vacuous (`Specs/GoldenQuorumPin.typeEnv_pin_is_load_bearing`). -/
theorem wp_call_dynamic_enter₂ {fid : FuncId} {anchor concrete : Func}
    {recvBox recv v₁ w₀ w₁ dv₀ dv₁ : GoValue}
    {pid₀ pid₁ rid₀ rid₁ : String} {pty₀ pty₁ rty₀ rty₁ : Ty}
    {locs : List (TargetShape × List Expr)} {env k}
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
              (.frame locs env [Loc.base a₂, Loc.base a₃] [] k concrete.wrapper)) @ s ; E {{ Φ }})
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
      (.frame locs env [Loc.base a₂, Loc.base a₃] [] k concrete.wrapper))
    (hred := by
      intro σ₁ hfns hmeths htypes
      have hstep := Step.callArgsDoneEnter (vals := [recvBox]) (plans := locs)
        (env := env) (k := k) (by simpa using henter σ₁ hfns hmeths htypes)
      refine ⟨hstep, ?_⟩
      intro c' s' hst
      obtain ⟨h1, h2⟩ := step_det (by trivial) hstep hst
      exact ⟨h1.symm, h2.symm⟩))
  iexact Hcont

/-! ## The multi-operand call walk (quorum pilot phase 4)

Before this slice `Laws/Call` had the two ENTRY dispatch laws
(`wp_call_first_target`, `wp_call_first_arg`) and nothing else on the
operand walk, because the golden program's calls carry at most one
operand of each kind. A general Go call `r₀, r₁ = f(a₀, a₁)` walks the
target list, then the argument list, one machine step per operand
handoff. The three laws below are exactly those handoffs — generic over
the call form: function id, operand lists, values and continuations are
all law variables, and nothing about a program appears.

Comparison with Perennial (`deps/perennial`, `new/golang/defn/`): there
is no analogue, because GooseLang calls are curried applications whose
argument evaluation is `wp_bind`-composed out of the ordinary expression
rules — a call form with an explicit operand-plan continuation is
GoCore's (the CEK reshape's) shape, and multi-VALUE returns are handled
by tupling rather than by caller target locations. Ours needs the
handoff laws; theirs needs the (equally arity-bound) tuple projections. -/

/-- Shift to the next ARGUMENT operand (no address check — arguments are
plain values). -/
@[go_walk_law]
theorem wp_call_arg_next {fid : FuncId}
    {plans : List (TargetShape × List Expr)}
    {vals : List GoValue} {v : GoValue} {a : Expr} {rest : List Expr} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE a env (.callArgsK fid plans (vals ++ [v]) rest env k))
        @ s ; E {{ Φ }}) ⊢
      WP (Config.retV v (.callArgsK fid plans vals (a :: rest) env k))
        @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.callArgNext)

/-- **Frame entry, two arguments / two results, STATIC callee** — the
non-dispatching sibling of `wp_call_dynamic_enter₂` (`hnodisp`: the
callee is not an interface anchor, so `enterFrame` keeps the function it
found). This is the shape of a Go method called on a CONCRETE receiver
(`m.AckedIndex(id)` where `m`'s static type is the implementation type):
the receiver is the first parameter, the results are the two pinned
result cells. Arity is fixed at 2/2, exactly as in the
`wp_call_enter_arg1`/`ret1`/`cap1`/`dynamic_enter₂` family (widening
owed — see `wp_alloc_step₄`'s scope note); everything else — callee,
names, types, values — is a law variable, and the `∀ σ` premises all
carry the `σ.types` pin, without which they are false at any named type
(`Specs/GoldenQuorumPin.typeEnv_pin_is_load_bearing`). -/
theorem wp_call_enter₂ {fid : FuncId} {func : Func}
    {v₀ v₁ w₀ w₁ dv₀ dv₁ : GoValue}
    {pid₀ pid₁ rid₀ rid₁ : String} {pty₀ pty₁ rty₀ rty₁ : Ty}
    {locs : List (TargetShape × List Expr)} {env k}
    (hfind : findFunctionIn? (GoCoreGS.prog GF) fid = some func)
    (hargs : func.args = #[⟨pid₀, pty₀⟩, ⟨pid₁, pty₁⟩])
    (hres : func.results = #[⟨rid₀, rty₀⟩, ⟨rid₁, rty₁⟩])
    (hrid : (rid₁ == rid₀) = false)
    (hnodisp : ∀ σ : ExecState, σ.functions = GoCoreGS.prog GF →
      σ.methods = GoCoreGS.methods GF → σ.types = GoCoreGS.types GF →
      dynamicDispatch? σ func #[v₀, v₁] = .ok none)
    (hnorm₀ : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ pty₀ v₀ = .ok w₀)
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
        WP (Config.exec func.body
              [[(rid₁, Loc.base a₃), (rid₀, Loc.base a₂),
                (pid₁, Loc.base a₁), (pid₀, Loc.base a₀)]]
              (.frame locs env [Loc.base a₂, Loc.base a₃] [] k func.wrapper)) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV v₁ (.callArgsK fid locs [v₀] [] env k))
          @ s ; E {{ Φ }} := by
  have henter : ∀ σ : ExecState, σ.functions = GoCoreGS.prog GF →
      σ.methods = GoCoreGS.methods GF → σ.types = GoCoreGS.types GF →
      enterFrame σ fid [v₀, v₁]
        = .ok (func,
            [[(rid₁, Loc.base ⟨σ.nextAddr + 3⟩), (rid₀, Loc.base ⟨σ.nextAddr + 2⟩),
              (pid₁, Loc.base ⟨σ.nextAddr + 1⟩), (pid₀, Loc.base ⟨σ.nextAddr⟩)]],
            [Loc.base ⟨σ.nextAddr + 2⟩, Loc.base ⟨σ.nextAddr + 3⟩],
            allocMany σ [⟨some pty₀, w₀⟩, ⟨some pty₁, w₁⟩,
                         ⟨some rty₀, dv₀⟩, ⟨some rty₁, dv₁⟩]) := by
    intro σ hfns hmeths htypes
    have hbind := bindParams₂ (σ := σ) (p₀ := ⟨pid₀, pty₀⟩) (p₁ := ⟨pid₁, pty₁⟩)
      (v₀ := v₀) (v₁ := v₁) (w₀ := w₀) (w₁ := w₁)
      (hnorm₀ σ htypes) (hnorm₁ _ htypes)
    have hdecl := allocDecls₂
      (σ := allocMany σ [⟨some pty₀, w₀⟩, ⟨some pty₁, w₁⟩])
      (env := [[(pid₁, Loc.base ⟨σ.nextAddr + 1⟩), (pid₀, Loc.base ⟨σ.nextAddr⟩)]])
      (r₀ := ⟨rid₀, rty₀⟩) (r₁ := ⟨rid₁, rty₁⟩) (d₀ := dv₀) (d₁ := dv₁)
      (hdef₀ _ htypes) (hdef₁ _ htypes)
    simp only [allocMany] at hbind hdecl ⊢
    unfold enterFrame
    rw [hfns, hfind]
    simp [hargs, hres, hnodisp σ hfns hmeths htypes, hbind, hdecl,
      pinResultLocs, LocalEnv.declare, LocalEnv.lookup, Scope.lookup, hrid,
      Bind.bind, Except.bind]
    exact hfns
  iintro Hcont
  iapply (wp_alloc_step₄ (hnv := rfl)
    (kof := fun a₀ a₁ a₂ a₃ => Config.exec func.body
      [[(rid₁, Loc.base a₃), (rid₀, Loc.base a₂),
        (pid₁, Loc.base a₁), (pid₀, Loc.base a₀)]]
      (.frame locs env [Loc.base a₂, Loc.base a₃] [] k func.wrapper))
    (hred := by
      intro σ₁ hfns hmeths htypes
      have hstep := Step.callArgsDoneEnter (vals := [v₀]) (plans := locs)
        (env := env) (k := k) (by simpa using henter σ₁ hfns hmeths htypes)
      refine ⟨hstep, ?_⟩
      intro c' s' hst
      obtain ⟨h1, h2⟩ := step_det (by trivial) hstep hst
      exact ⟨h1.symm, h2.symm⟩))
  iexact Hcont

/-! ## The TWO-RESULT frame exit (quorum pilot phase 4)

`wp_frame_return_int`/`wp_frame_fall_int` cover the unary-result exit
(`loadMany [r]` / `storeMany [t]`). Go's multi-value return walks the
same single step over LISTS: `Step.frameReturn` reads every pinned result
location and stores into every caller target, in order. Two of each is
the arity the `(Index, bool)` comma-ok method forces; the general n-ary
form is owed (recorded, not silently target-fitted — it needs the
list-indexed store core, like `wp_alloc_step₄`'s widening).

Perennial comparison: multi-value returns there are a TUPLE value
returned by an ordinary GooseLang call, so no frame-exit law family
arises — the caller destructures with pure projections. Ours writes the
caller's cells inside the exit step, which is why the arity appears in
the law; the granularity ledger's frame-exit entry covers both cells
moving atomically. -/

/-- Two owned full-fraction cells sit at distinct addresses (the
disequality the second store's heap lookup needs; derived from ownership,
so no caller-side aliasing side-condition). -/
theorem pointsTo_addr_ne {a b : Addr} {c₁ c₂ : HeapCell} :
    (iprop(a.id ↦ c₁ ∗ b.id ↦ c₂) : IProp GF) ⊢ ⌜a.id ≠ b.id⌝ := by
  iintro ⟨H1, H2⟩
  iapply pointsTo_ne $$ H1 H2

/- TOMBSTONE (S1 audit-fix round, 2026-08-09; the no-inert-scaffolding
rule): `wp_read₂_store₂_step` (two-read/two-write step core) was
DELETED here. Its only front, the pre-spine `wp_frame_return₂`, was
restated when the frame exit's atomic `storeMany` was retired
(BUG-025: the exit READS the pinned results and the caller-target
writes are per-target `storeK` steps; since the BUG-052 order pin the
target OPERANDS also evaluate post-call at the exit) — so no step
performs the two-read/two-write shape any more. -/

theorem wp_frame_return₁ {x : String} {tenv : LocalEnv} {ta ra : Addr}
    {rcell tcell tcell' : HeapCell} {k} {wf : Bool}
    (hres : LocalEnv.lookup tenv x = some (.base ta))
    (hstore : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base ta) = some tcell →
      storeLoc σ (.base ta) rcell.value
        = .ok { σ with heap := Heap.set σ.heap (.base ta) tcell' }) :
    ra.id ↦ rcell ∗ ta.id ↦ tcell
      ∗ (ra.id ↦ rcell ∗ ta.id ↦ tcell' -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.returning (.frame [(.chain [], [.ref x])] tenv [.base ra] [] k wf))
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Ht, Hcont⟩
  -- Step 1 (BUG-052 order pin): read the result, enter the spine.
  iapply (wp_det_step_keep
    (P := iprop(ra.id ↦ rcell))
    (c₁ := Config.evalE (.ref x) tenv (.tgtOpK (.chain []) [] [] [] []
      .vals [] [rcell.value] (.seqn #[]) tenv k))
    (hnv := rfl)
    (hred := fun σ₁ _hfns _hmeths _htypes => by
      iintro ⟨Hσ, Hpt⟩
      ihave %Hmap : ⌜get? (heapToMap σ₁.heap) ra.id = some rcell⌝ $$ [Hσ Hpt]
      · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
        itrivial
      have hlook : Heap.lookup σ₁.heap (.base ra) = some rcell := by
        rw [get?_heapToMap] at Hmap; simpa using Hmap
      have hload : loadMany σ₁ [Loc.base ra] = .ok [rcell.value] := by
        simp [loadMany, loadLoc, hlook, Bind.bind, Except.bind]
      imodintro
      ipureintro
      refine ⟨Step.frameReturnTargets hload, ?_⟩
      intro c' s' hst
      obtain ⟨h1, h2⟩ := step_det (by trivial) (Step.frameReturnTargets hload) hst
      exact ⟨h1.symm, h2.symm⟩))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  iapply (wp_eval_ref hres)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  iapply (wp_tgtop_stores (r := .chain (.addr (.base ta)) [] []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  simp only [List.nil_append]
  iapply (wp_assign_store_loc (oldcell := tcell) (newcell := tcell')
    (hstore := hstore))
  isplitl [Ht]
  · iexact Ht
  iintro Ht
  iapply wp_stores_done_nil
  iapply Hcont $$ [$Hr $Ht]

/-- **Two-result frame exit**: `return` at a frame with TWO pinned result
locations and TWO caller targets — read both result cells, store both
into the caller's cells in order. The store facts are the machine's own
cell-conditioned computations (in the `wp_assign_store`/`hstore` style),
so the law is general in the cells' types: any pair of result cells and
any pair of target cells whose stores compute. Go's `(T, bool)` comma-ok
return is the instance the quorum pilot forces
(`wp_frame_return_ackedIndex`, `Specs/GoldenQuorumWP.lean`). -/
theorem wp_frame_return₂ {x₀ x₁ : String} {tenv : LocalEnv}
    {ta₀ ta₁ ra₀ ra₁ : Addr}
    {rcell₀ rcell₁ tcell₀ tcell₀' tcell₁ tcell₁' : HeapCell} {k} {wf : Bool}
    (hres₀ : LocalEnv.lookup tenv x₀ = some (.base ta₀))
    (hres₁ : LocalEnv.lookup tenv x₁ = some (.base ta₁))
    (hstore₀ : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base ta₀) = some tcell₀ →
      storeLoc σ (.base ta₀) rcell₀.value
        = .ok { σ with heap := Heap.set σ.heap (.base ta₀) tcell₀' })
    (hstore₁ : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base ta₁) = some tcell₁ →
      storeLoc σ (.base ta₁) rcell₁.value
        = .ok { σ with heap := Heap.set σ.heap (.base ta₁) tcell₁' }) :
    ra₀.id ↦ rcell₀ ∗ ra₁.id ↦ rcell₁ ∗ ta₀.id ↦ tcell₀ ∗ ta₁.id ↦ tcell₁
      ∗ (ra₀.id ↦ rcell₀ ∗ ra₁.id ↦ rcell₁ ∗ ta₀.id ↦ tcell₀' ∗ ta₁.id ↦ tcell₁'
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.returning
            (.frame [(.chain [], [.ref x₀]), (.chain [], [.ref x₁])] tenv
              [.base ra₀, .base ra₁] [] k wf))
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr0, Hr1, Ht0, Ht1, Hcont⟩
  -- Step 1 (BUG-052 order pin): read both results, enter the spine —
  -- target operands evaluate POST-CALL, stores left-to-right after.
  iapply (wp_det_step_keep
    (P := iprop(ra₀.id ↦ rcell₀ ∗ ra₁.id ↦ rcell₁))
    (c₁ := Config.evalE (.ref x₀) tenv (.tgtOpK (.chain []) [] [] []
      [(.chain [], [.ref x₁])] .vals [] [rcell₀.value, rcell₁.value]
      (.seqn #[]) tenv k))
    (hnv := rfl)
    (hred := fun σ₁ _hfns _hmeths _htypes => by
      iintro ⟨Hσ, Hpt0, Hpt1⟩
      ihave %Hmap0 : ⌜get? (heapToMap σ₁.heap) ra₀.id = some rcell₀⌝ $$ [Hσ Hpt0]
      · icases genHeap_valid $$ [$Hσ $Hpt0] with >%h
        itrivial
      ihave %Hmap1 : ⌜get? (heapToMap σ₁.heap) ra₁.id = some rcell₁⌝ $$ [Hσ Hpt1]
      · icases genHeap_valid $$ [$Hσ $Hpt1] with >%h
        itrivial
      have hlook0 : Heap.lookup σ₁.heap (.base ra₀) = some rcell₀ := by
        rw [get?_heapToMap] at Hmap0; simpa using Hmap0
      have hlook1 : Heap.lookup σ₁.heap (.base ra₁) = some rcell₁ := by
        rw [get?_heapToMap] at Hmap1; simpa using Hmap1
      have hload : loadMany σ₁ [Loc.base ra₀, Loc.base ra₁]
          = .ok [rcell₀.value, rcell₁.value] := by
        simp [loadMany, loadLoc, hlook0, hlook1, Bind.bind, Except.bind]
      imodintro
      ipureintro
      refine ⟨Step.frameReturnTargets hload, ?_⟩
      intro c' s' hst
      obtain ⟨h1, h2⟩ := step_det (by trivial) (Step.frameReturnTargets hload) hst
      exact ⟨h1.symm, h2.symm⟩))
  isplitl [Hr0 Hr1]
  · isplitl [Hr0]
    · iexact Hr0
    · iexact Hr1
  iintro ⟨Hr0, Hr1⟩
  iapply (wp_eval_ref hres₀)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  iapply (wp_tgtop_next (r := .chain (.addr (.base ta₀)) [] []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  iapply (wp_eval_ref hres₁)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  iapply (wp_tgtop_stores (r := .chain (.addr (.base ta₁)) [] []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  simp only [List.nil_append, List.cons_append]
  iapply (wp_assign_store_loc (oldcell := tcell₀) (newcell := tcell₀')
    (hstore := hstore₀))
  isplitl [Ht0]
  · iexact Ht0
  iintro Ht0
  iapply (wp_assign_store_loc (oldcell := tcell₁) (newcell := tcell₁')
    (hstore := hstore₁))
  isplitl [Ht1]
  · iexact Ht1
  iintro Ht1
  iapply wp_stores_done_nil
  iapply Hcont $$ [$Hr0 $Hr1 $Ht0 $Ht1]

end

end GoLean.Iris
