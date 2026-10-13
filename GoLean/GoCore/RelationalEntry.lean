import GoLean.GoCore.RelationalControl
import GoLean.GoCore.RelationalOutcomeSound
import GoLean.GoCore.SetupSound

/-!
# Local function activation and readback

The input store is arbitrary; this is not whole-program initialization.
Binding errors, result-allocation errors and result-location errors are
separate alternatives. A normally completed body can still fail readback.
The binding primitives are semantic memory operations, not stepper equations.
-/

namespace GoLean.GoCore.Relational

open Machine

structure Activation where
  locals : LocalEnv
  store : Store
  results : List Loc

/-- Local activation, with all failures of its three ordered phases. -/
inductive LocalEntry (ctx : ProgramCtx) (f : Func) (args : List GoValue) (s : Store) :
    Except Stop Activation → Prop where
  | ready {env frameEnv t u results} :
      bindParams ctx [] s f.args.toList args = .ok (env, t) →
      allocDecls ctx env t f.results.toList = .ok (frameEnv, u) →
      pinResultLocs frameEnv f.results.toList = .ok results →
      LocalEntry ctx f args s (.ok ⟨frameEnv, u, results⟩)
  | parametersFailed {e} : bindParams ctx [] s f.args.toList args = .error e →
      LocalEntry ctx f args s (.error e)
  | resultsFailed {env t e} :
      bindParams ctx [] s f.args.toList args = .ok (env, t) →
      allocDecls ctx env t f.results.toList = .error e →
      LocalEntry ctx f args s (.error e)
  | locationsFailed {env frameEnv t u e} :
      bindParams ctx [] s f.args.toList args = .ok (env, t) →
      allocDecls ctx env t f.results.toList = .ok (frameEnv, u) →
      pinResultLocs frameEnv f.results.toList = .error e →
      LocalEntry ctx f args s (.error e)

/-- A driver-style frame has no caller result targets. Its normal return
event has payload `[]`; final result readback is a separate operation. -/
def activationPoint (f : Func) (a : Activation) : State :=
  statement f.body a.locals ⟨.frame [] [] [] [] .stop f.id⟩ a.store

def Readback (ctx : ProgramCtx) (s : Store) (results : List Loc)
    (outcome : Except Stop (List GoValue)) : Prop := loadMany ctx s results = outcome

def LocalNormalRun (ctx : ProgramCtx) (f : Func) (args : List GoValue) (s : Store)
    (ls : List StepLabel) (t : Store) (values : Except Stop (List GoValue)) : Prop :=
  ∃ a, LocalEntry ctx f args s (.ok a) ∧
    Run ctx (activationPoint f a) ls (resumed .halt t) ∧ Readback ctx t a.results values

theorem LocalEntry.ready_iff {ctx : ProgramCtx} {f : Func} {args : List GoValue} {s : Store}
    {a : Activation} : LocalEntry ctx f args s (.ok a) ↔
    ∃ env t, bindParams ctx [] s f.args.toList args = .ok (env, t) ∧
      allocDecls ctx env t f.results.toList = .ok (a.locals, a.store) ∧
      pinResultLocs a.locals f.results.toList = .ok a.results := by
  constructor
  · intro h; cases h with | ready hb ha hp => exact ⟨_, _, hb, ha, hp⟩
  · rintro ⟨env, t, hb, ha, hp⟩
    cases a
    exact .ready hb ha hp

/-- The complete local-entry relation is a function, including its failures. -/
theorem LocalEntry.total (ctx : ProgramCtx) (f : Func) (args : List GoValue) (s : Store) :
    ∃ outcome, LocalEntry ctx f args s outcome := by
  cases hb : bindParams ctx [] s f.args.toList args with
  | error e => exact ⟨_, .parametersFailed hb⟩
  | ok p =>
    obtain ⟨env, t⟩ := p
    cases ha : allocDecls ctx env t f.results.toList with
    | error e => exact ⟨_, .resultsFailed hb ha⟩
    | ok p =>
      obtain ⟨frameEnv, u⟩ := p
      cases hp : pinResultLocs frameEnv f.results.toList with
      | error e => exact ⟨_, .locationsFailed hb ha hp⟩
      | ok results => exact ⟨_, .ready hb ha hp⟩

theorem LocalEntry.deterministic {ctx : ProgramCtx} {f : Func} {args : List GoValue}
    {s : Store} {a b : Except Stop Activation}
    (h : LocalEntry ctx f args s a) (k : LocalEntry ctx f args s b) : a = b := by
  cases h <;> cases k <;> simp_all

/-- Slot arithmetic is derived once for symbolic functions and stores.
Distinct identifiers are needed for lookup; not for mere allocation. -/
theorem LocalEntry.layout {ctx : ProgramCtx} {f : Func} {args : List GoValue}
    {s : Store} {a : Activation} (h : LocalEntry ctx f args s (.ok a))
    (distinct : namesDistinct ((f.args ++ f.results).toList.map (·.id)) = true) :
    a.store.heap.size = s.heap.size + f.args.size + f.results.size ∧
    (∀ i (hi : i < f.args.size), LocalEnv.lookup a.locals f.args[i].id = some (entrySlot s i)) ∧
    (∀ i (hi : i < f.results.size), LocalEnv.lookup a.locals f.results[i].id =
      some (entrySlot s (f.args.size + i))) ∧
    a.results = (List.range f.results.size).map (fun i => entrySlot s (f.args.size + i)) := by
  obtain ⟨env, t, hb, ha, hp⟩ := LocalEntry.ready_iff.mp h
  exact ⟨SetupSound.setup_heap_size_from hb ha,
    SetupSound.setup_lookup_arg_from hb ha distinct,
    SetupSound.setup_lookup_result_from hb ha distinct,
    SetupSound.setup_resultLocs_from hb ha distinct hp⟩

/-- Resolved declared-function entry. Dispatch and promotion are not silently
treated as a declared call; the non-interface-anchor premise is visible. -/
theorem LocalEntry.declared {ctx : ProgramCtx} {f : Func} {fid : FuncId} {args : List GoValue}
    {s : Store} {a : Activation} (h : LocalEntry ctx f args s (.ok a))
    (found : findFunctionIn? ctx.functions fid = some f)
    (anchor : ∀ m, methodInfoByFuncId? ctx f.id = some m → methodRecvInterfaceName? m = none)
    (arity : f.args.size = args.length) :
    enterFrame ctx s fid args = .ok (.run f a.locals a.results, a.store, []) := by
  obtain ⟨env, t, hb, ha, hp⟩ := LocalEntry.ready_iff.mp h
  rw [enterFrame_declared found anchor arity]
  simp [hb, ha, hp, Bind.bind, Except.bind, pure, Except.pure]

/-- Local normal-run correspondence. The result is still fallible readback;
the run's labels are not folded into this sequential driver's `Readout`. -/
theorem local_normal_iff {ctx : ProgramCtx} {f : Func} {args : List GoValue}
    {s t : Store} {values : Except Stop (List GoValue)} {fuel : Nat} :
    (∃ ls, ls.length ≤ fuel ∧ LocalNormalRun ctx f args s ls t values) ↔
    ∃ a ch tail, LocalEntry ctx f args s (.ok a) ∧
      runConfig ctx fuel a.store (activationPoint f a).control ch = .ok (t, tail) ∧
      Readback ctx t a.results values := by
  constructor
  · rintro ⟨ls, hn, a, he, hr, hv⟩
    obtain ⟨ch, tail, hh⟩ := normal_run_iff.mpr ⟨ls, hn, hr⟩
    exact ⟨a, ch, tail, he, by simpa [runConfig_eq_loop, activationPoint, statement] using hh, hv⟩
  · rintro ⟨a, ch, tail, he, hr, hv⟩
    have hr' : execStmtLoop ctx fuel (activationPoint f a).store
        (activationPoint f a).control ch = .ok (t, tail) := by
      simpa [runConfig_eq_loop, activationPoint, statement] using hr
    obtain ⟨ls, hn, hh⟩ := normal_run_iff.mp ⟨ch, tail, hr'⟩
    exact ⟨ls, hn, a, he, hh, hv⟩

end GoLean.GoCore.Relational
