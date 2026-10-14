import GoLean.GoCore.RelationalEntry

/-!
# Declared source calls and normal result delivery

The initial fragment has store-preserving, pick-free operands, bound-variable
caller destinations and no pending callee defers. Actual labels remain in the
run. Saved callers and normal exits own frame/target/signal representation here;
clients compose a separately proved body contract between these views.
-/
namespace GoLean.GoCore.Relational
open Machine

/-- A finite pick-free run, retaining every actual ordered label. -/
def PickFreeRun (ctx : ProgramCtx) (a b : State) : Prop :=
  ∃ ls, Run ctx a ls b ∧ ∀ l ∈ ls, l.picks = []

theorem PickFreeRun.refl (ctx : ProgramCtx) (a : State) : PickFreeRun ctx a a :=
  ⟨[], .refl, by simp⟩
theorem PickFreeRun.single {ctx : ProgramCtx} {a b : State} {l : StepLabel}
    (h : Transition ctx a l b) (hp : l.picks = []) : PickFreeRun ctx a b :=
  ⟨[l], .single h, by simpa using hp⟩
theorem PickFreeRun.pure {ctx : ProgramCtx} {a b : State}
    (h : Pure ctx a b) : PickFreeRun ctx a b := .single h.1 rfl

theorem PickFreeRun.trans {ctx : ProgramCtx} {a b c : State}
    (h : PickFreeRun ctx a b) (g : PickFreeRun ctx b c) : PickFreeRun ctx a c := by
  obtain ⟨ls, hr, hp⟩ := h
  obtain ⟨ms, gr, gp⟩ := g
  exact ⟨ls ++ ms, hr.append gr, fun l hl => (List.mem_append.mp hl).elim (hp l) (gp l)⟩

private theorem step {ctx : ProgramCtx} {c d : Config} {s t : Store} {l : StepLabel}
    (h : Step ctx c s d t l) (hp : l.picks = []) : PickFreeRun ctx ⟨c, s⟩ ⟨d, t⟩ :=
  PickFreeRun.single h hp

/-- Operand values established uniformly for any saved tail. -/
inductive OperandValues (ctx : ProgramCtx) (s : Store) (env : LocalEnv) :
    List Expr → List GoValue → Prop where
  | nil : OperandValues ctx s env [] []
  | cons : (∀ k, PickFreeRun ctx (expression e env k s) (returned v k s)) →
      OperandValues ctx s env es vs → OperandValues ctx s env (e :: es) (v :: vs)

/-- Ordered writes permit repeated destinations and interior locations. -/
inductive WriteValues (ctx : ProgramCtx) : List Loc → List GoValue → Store → Store → Prop where
  | nil : WriteValues ctx [] [] s s
  | cons {s t u : Store} {l : Loc} {v : GoValue} {ls : List Loc} {vs : List GoValue} : storeLoc ctx s l v = .ok t → WriteValues ctx ls vs t u →
      WriteValues ctx (l :: ls) (v :: vs) s u

/-- Bound source destinations, without target plans. -/
inductive BoundDestinations (env : LocalEnv) : List VarId → List Loc → Prop where
  | nil : BoundDestinations env [] []
  | cons {id : VarId} {l : Loc} {ids : List VarId} {ls : List Loc} : LocalEnv.lookup env id = some l → BoundDestinations env ids ls →
      BoundDestinations env (id :: ids) (l :: ls)

structure SavedCaller where
  destinations : List VarId
  locals : LocalEnv
  tail : Continuation

/-- Callee result cells belong to the activation, distinct from caller targets. -/
structure CallBoundary where
  caller : SavedCaller
  function : FuncId
  results : List Loc

def SavedCaller.boundary (caller : SavedCaller) (f : Func) (a : Activation) : CallBoundary :=
  ⟨caller, f.id, a.results⟩

def CallBoundary.continuation (b : CallBoundary) : Continuation :=
  ⟨.frame (b.caller.destinations.map fun id => (.chain [], [.ref id]))
    b.caller.locals b.results [] b.caller.tail.toMachine b.function⟩

def CallBoundary.body (b : CallBoundary) (f : Func) (a : Activation) : State :=
  statement f.body a.locals b.continuation a.store

inductive NormalExit where
  | fallthrough
  | returned

def exitPoint (mode : NormalExit) (k : Continuation) (s : Store) : State :=
  match mode with
  | .fallthrough => resumed k s
  | .returned => ⟨.signal .ret k.toMachine, s⟩

def CallBoundary.exit (b : CallBoundary) (mode : NormalExit) (s : Store) : State :=
  exitPoint mode b.continuation s

def SavedCaller.call (caller : SavedCaller) (fid : FuncId) (args : List Expr) (s : Store) : State :=
  statement (.call (caller.destinations.toArray.map Assignee.var) fid args.toArray)
    caller.locals caller.tail s

theorem reference (ctx : ProgramCtx) (s : Store) (env : LocalEnv) (k : Continuation)
    (id : VarId) (l : Loc) (h : LocalEnv.lookup env id = some l) :
    Pure ctx (expression (.ref id) env k s) (returned (.addr l) k s) :=
  ⟨Step.evalRef h, rfl⟩

theorem return_start (ctx : ProgramCtx) (s : Store) (env : LocalEnv) (k : Continuation) :
    Pure ctx (statement .returnStmt env k s) (exitPoint .returned k s) :=
  ⟨Step.signalStmt rfl, rfl⟩

theorem return_sequence (ctx : ProgramCtx) (s : Store) (env : LocalEnv)
    (k : Continuation) (rest : List Stmt) :
    Pure ctx (exitPoint .returned (sequence rest env k) s) (exitPoint .returned k s) :=
  ⟨Step.signal rfl, rfl⟩

private def plans (ids : List VarId) : List (TargetShape × List Expr) :=
  ids.map fun id => (.chain [], [.ref id])

private theorem plans_ok (ids : List VarId) :
    targetsPlan (ids.map Assignee.var) = some (plans ids) := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    simp [targetsPlan, plans, List.mapM_cons, targetPlan] at ih ⊢
    rw [ih]
    rfl

private theorem arguments_run {ctx : ProgramCtx} {s : Store} {env : LocalEnv}
    {es : List Expr} {vs : List GoValue} (h : OperandValues ctx s env es vs)
    (e : Expr) (v : GoValue)
    (hv : ∀ k, PickFreeRun ctx (expression e env k s) (returned v k s))
    (done : List GoValue) (fid : FuncId) (ps : List (TargetShape × List Expr))
    (k : Continuation) (f : Func) (a : Activation)
    (entry : enterFrame ctx s fid (done ++ v :: vs) = .ok (.run f a.locals a.results, a.store, [])) :
    PickFreeRun ctx (expression e env ⟨.callArgsK fid ps done es env k.toMachine⟩ s)
      (statement f.body a.locals ⟨.frame ps env a.results [] k.toMachine f.id⟩ a.store) := by
  induction h generalizing e v done with
  | nil =>
    exact (hv _).trans (.single (Step.callArgsDoneEnter (enterFramePick_ok (ch := []) entry) rfl) rfl)
  | @cons e' v' es vs he ht ih =>
    apply (hv _).trans
    apply (step Step.callArgNext rfl).trans
    apply ih e' v' he (done ++ [v])
    simpa [List.append_assoc] using entry

/-- Enter a resolved declared function after evaluating source operands.
Dispatch is explicit; no method-anchor behavior is silently included. -/
theorem SavedCaller.enter (caller : SavedCaller) {ctx : ProgramCtx} {s : Store}
    {es : List Expr} {vs : List GoValue} {fid : FuncId} {f : Func} {a : Activation}
    (operands : OperandValues ctx s caller.locals es vs)
    (found : findFunctionIn? ctx.functions fid = some f)
    (method : methodInfoByFuncId? ctx f.id = none) (arity : f.args.size = vs.length)
    (activation : LocalEntry ctx f vs s (.ok a)) :
    PickFreeRun ctx (caller.call fid es s) ((caller.boundary f a).body f a) := by
  have entry := activation.declared found (by simp [method]) arity
  cases operands with
  | nil =>
    exact .single (Step.callImmediate (by simpa [plans, SavedCaller.boundary] using plans_ok caller.destinations)
      (by simp) (enterFramePick_ok (ch := []) entry) rfl) rfl
  | @cons e v es vs he ht =>
    have start : PickFreeRun ctx (caller.call fid (e :: es) s)
        (expression e caller.locals ⟨.callArgsK fid (plans caller.destinations) [] es caller.locals caller.tail.toMachine⟩ s) :=
      step (Step.callStart (by simpa using plans_ok caller.destinations) (by simp)) rfl
    exact start.trans (arguments_run ht _ _ he [] fid (plans caller.destinations) caller.tail f a entry)

/-- Root-slot validity is about pinned callee results, not pointer arguments
or caller destinations. Every successful activation supplies it. -/
def ResultSlots (results : List Loc) : Prop := ∀ l ∈ results, ∃ n : Nat, l = .base ⟨n⟩

private def RootBindings (env : LocalEnv) : Prop :=
  ∀ id l, LocalEnv.lookup env id = some l → ∃ n : Nat, l = .base ⟨n⟩

private theorem root_declare {env : LocalEnv} (h : RootBindings env) (id : VarId) (n : Nat) :
    RootBindings (LocalEnv.declare env id (.base ⟨n⟩)) := by
  intro j l hj
  by_cases same : j = id
  · subst j
    rw [LocalEnv.lookup_declare_self] at hj
    exact ⟨n, (Option.some.inj hj).symm⟩
  · rw [LocalEnv.lookup_declare_ne _ same] at hj
    exact h j l hj

private theorem bind_roots {ctx : ProgramCtx} : ∀ (env : LocalEnv) (s : Store)
    (ps : List Param) (vs : List GoValue) {env' : LocalEnv} {s' : Store},
    bindParams ctx env s ps vs = .ok (env', s') → RootBindings env → RootBindings env'
  | _, _, [], [], _, _, h, roots => by
    simp only [bindParams, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact roots
  | _, _, [], _ :: _, _, _, h, _ => by simp [bindParams, stuck] at h
  | _, _, _ :: _, [], _, _, h, _ => by simp [bindParams, stuck] at h
  | env, s, p :: ps, v :: vs, _, _, h, roots => by
    simp only [bindParams, Bind.bind, Except.bind] at h
    cases hn : normalizeValueForTy ctx p.typ v with
    | error e => simp [hn] at h
    | ok v' =>
      simp only [hn] at h
      cases ha : Store.alloc ctx s v' p.typ with
      | error e => simp [ha] at h
      | ok pair =>
        obtain ⟨l, t⟩ := pair
        simp only [ha] at h
        apply bind_roots _ _ ps vs h
        rw [(Store.alloc_shape ha).1]
        exact root_declare roots _ _

private theorem alloc_roots {ctx : ProgramCtx} : ∀ (env : LocalEnv) (s : Store)
    (ps : List Param) {env' : LocalEnv} {s' : Store},
    allocDecls ctx env s ps = .ok (env', s') → RootBindings env → RootBindings env'
  | _, _, [], _, _, h, roots => by
    simp only [allocDecls, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact roots
  | env, s, p :: ps, _, _, h, roots => by
    simp only [allocDecls, Bind.bind, Except.bind] at h
    cases hn : defaultValue ctx p.typ with
    | error e => simp [hn] at h
    | ok v =>
      simp only [hn] at h
      cases ha : Store.alloc ctx s v p.typ with
      | error e => simp [ha] at h
      | ok pair =>
        obtain ⟨l, t⟩ := pair
        simp only [ha] at h
        apply alloc_roots _ _ ps h
        rw [(Store.alloc_shape ha).1]
        exact root_declare roots _ _

private theorem pin_roots {env : LocalEnv} (roots : RootBindings env) :
    ∀ (ps : List Param) {ls : List Loc}, pinResultLocs env ps = .ok ls → ResultSlots ls
  | [], _, h => by
    simp only [pinResultLocs, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [ResultSlots]
  | p :: ps, ls, h => by
    cases hl : LocalEnv.lookup env p.id with
    | none => simp [pinResultLocs, hl, stuck] at h
    | some l =>
      cases ht : pinResultLocs env ps with
      | error e => simp [pinResultLocs, hl, ht, Bind.bind, Except.bind] at h
      | ok rest =>
        have eq : l :: rest = ls := by
          simpa [pinResultLocs, hl, ht, Bind.bind, Except.bind, pure, Except.pure] using h
        subst ls
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact roots _ _ hl
        · exact pin_roots roots ps ht x hx

/-- Every successful activation pins root result slots. Unlike the detailed
layout law, this invariant needs no distinct-name or well-formedness premise. -/
theorem LocalEntry.resultSlots {ctx : ProgramCtx} {f : Func} {args : List GoValue}
    {s : Store} {a : Activation} (h : LocalEntry ctx f args s (.ok a)) : ResultSlots a.results := by
  obtain ⟨env, t, hb, ha, hp⟩ := LocalEntry.ready_iff.mp h
  have roots : RootBindings [] := by intros id l hl; simp [LocalEnv.lookup] at hl
  exact pin_roots (alloc_roots _ _ _ ha (bind_roots _ _ _ _ hb roots)) _ hp

/-- Driver readback agrees with traced frame reads at valid result slots.
The trace is produced here, not assumed by a client. -/
theorem Readback.traced {ctx : ProgramCtx} {s : Store} {results : List Loc}
    {vs : List GoValue} (valid : ResultSlots results) (h : Readback ctx s results (.ok vs)) :
    ∃ tr, loadResults ctx s results = .ok (vs, tr) := by
  induction results generalizing vs with
  | nil =>
    have : vs = [] := by simpa [Readback, loadMany] using h.symm
    subst vs
    exact ⟨[], rfl⟩
  | cons l ls ih =>
    obtain ⟨n, rfl⟩ := valid l (by simp)
    cases hv : loadLoc ctx s (.base ⟨n⟩) with
    | error e => simp [Readback, loadMany, hv, Bind.bind, Except.bind] at h
    | ok v =>
      cases hs : loadMany ctx s ls with
      | error e => simp [Readback, loadMany, hv, hs, Bind.bind, Except.bind] at h
      | ok values =>
        have eq : v :: values = vs := by simpa [Readback, loadMany, hv, hs, Bind.bind, Except.bind, pure, Except.pure] using h
        subst vs
        obtain ⟨tr, ht⟩ := ih (fun l hl => valid l (by simp [hl])) hs
        refine ⟨[.access .read (.data (Loc.base ⟨n⟩).canon)] ++ tr, ?_⟩
        simp [loadResults, Mem.loadBinding, loadRoot, hv, ht, Bind.bind, Except.bind, pure, Except.pure]

private def locationRef (l : Loc) : TargetRef := .chain (.addr l) [] []

private theorem store_reference {ctx : ProgramCtx} {s t : Store} {l : Loc} {v : GoValue}
    (h : storeLoc ctx s l v = .ok t) :
    storeTarget ctx s (locationRef l) v = .ok (t, [.access .write (.data l.canon)]) := by
  simp [locationRef, storeTarget, storeTarget.plan, resolveChain, valueAsLoc, Mem.store,
    h, Bind.bind, Except.bind, pure, Except.pure]

private theorem stores_run {ctx : ProgramCtx} {ls : List Loc} {vs : List GoValue}
    {s t : Store} (h : WriteValues ctx ls vs s t) (env : LocalEnv) (k : Continuation) :
    PickFreeRun ctx ⟨.next (.storeK (ls.map locationRef) vs (.seqn #[]) env k.toMachine), s⟩
      (resumed k t) := by
  induction h with
  | nil =>
    obtain ⟨labels, hr, hp, _⟩ := empty_sequence_run ctx env k _
    exact (step Step.storeDone rfl).trans ⟨labels, hr, hp⟩
  | @cons s t u l v ls vs hw _ ih =>
    exact (step (Step.storeStep (r := .ok (t, [.access .write (.data l.canon)]))
      (by rw [store_reference hw]; rfl) rfl) rfl).trans ih

private theorem targets_run {ctx : ProgramCtx} {env : LocalEnv} {ids : List VarId}
    {ls : List Loc} (h : BoundDestinations env ids ls) (id : VarId) (l : Loc)
    (hl : LocalEnv.lookup env id = some l) (refs : List TargetRef)
    (vs : List GoValue) (s : Store) (k : Continuation) :
    PickFreeRun ctx
      (expression (.ref id) env ⟨.tgtOpK (.chain []) [] [] refs (plans ids) .vals [] vs (.seqn #[]) env k.toMachine⟩ s)
      ⟨.next (.storeK (refs ++ (l :: ls).map locationRef) vs (.seqn #[]) env k.toMachine), s⟩ := by
  induction h generalizing id l refs with
  | nil =>
    exact (PickFreeRun.pure (reference ctx s env _ id l hl)).trans
      (step (Step.tgtOpStores rfl) rfl)
  | @cons id' l' ids ls hl' _ ih =>
    apply (PickFreeRun.pure (reference ctx s env _ id l hl)).trans
    apply (step (Step.tgtOpNext rfl) rfl).trans
    simpa [List.append_assoc, expression, plans, locationRef] using ih id' l' hl' (refs ++ [locationRef l])

/-- Deliver all results before resuming the saved caller. Reads precede
ordered writes; destination aliases are permitted. Both normal exit modes
share this law. No pending callee defers are represented by this boundary. -/
theorem CallBoundary.deliver (b : CallBoundary) (mode : NormalExit)
    {ctx : ProgramCtx} {s t : Store} {locs : List Loc} {vs : List GoValue}
    (count : b.caller.destinations.length = b.results.length)
    (valid : ResultSlots b.results)
    (bound : BoundDestinations b.caller.locals b.caller.destinations locs)
    (read : Readback ctx s b.results (.ok vs)) (writes : WriteValues ctx locs vs s t) :
    PickFreeRun ctx (b.exit mode s) (resumed b.caller.tail t) := by
  rcases b with ⟨⟨ids, env, k⟩, fid, results⟩
  dsimp only at count valid bound read ⊢
  cases bound with
  | nil =>
    have er : results = [] := by simpa using count.symm
    subst results
    have ev : vs = [] := by simpa [Readback, loadMany] using read.symm
    subst vs
    cases writes
    cases mode
    · exact step Step.frameFall rfl
    · exact step Step.frameReturn rfl
  | @cons id loc ids locs hl ht =>
    obtain ⟨tr, hr⟩ := read.traced valid
    have rest := (targets_run (ctx := ctx) ht id loc hl [] vs s k).trans (stores_run writes env k)
    cases mode
    · exact (step (Step.frameFallTargets hr) rfl).trans rest
    · exact (step (Step.frameReturnTargets hr) rfl).trans rest

/-- A source assignment to a bound variable, with semantic read/write premises. -/
theorem assign_variable (ctx : ProgramCtx) (s t : Store) (env : LocalEnv)
    (k : Continuation) (dst src : VarId) (target source : Loc) (v : GoValue)
    (hd : LocalEnv.lookup env dst = some target)
    (hs : LocalEnv.lookup env src = some source)
    (read : loadRoot ctx s source = .ok v) (write : storeLoc ctx s target v = .ok t) :
    PickFreeRun ctx (statement (.assign (.var dst) (.var src)) env k s) (resumed k t) := by
  let tk : Continuation := ⟨.tgtOpK (.chain []) [] [] [] [] .vals [.var src] [] (.seqn #[]) env k.toMachine⟩
  let vk : Continuation := ⟨.rhsK .vals [locationRef target] [] [] (.seqn #[]) env k.toMachine⟩
  have start : PickFreeRun ctx (statement (.assign (.var dst) (.var src)) env k s)
      (expression (.ref dst) env tk s) := step (Step.assignFirst rfl) rfl
  have rhs : PickFreeRun ctx (returned (.addr target) tk s) (expression (.var src) env vk s) :=
    step (Step.tgtOpRhs rfl) rfl
  obtain ⟨tr, hr⟩ := read_variable ctx s env vk src source v hs read
  have values : PickFreeRun ctx (returned v vk s)
      ⟨.next (.storeK [locationRef target] [v] (.seqn #[]) env k.toMachine), s⟩ :=
    step (Step.rhsStores rfl rfl) rfl
  exact start.trans ((PickFreeRun.pure (reference ctx s env tk dst target hd)).trans
    (rhs.trans ((PickFreeRun.single hr rfl).trans
      (values.trans (stores_run (.cons write .nil) env k)))))

/-- Compose a source call with an independently proved callee contract and
result writes. Result-slot validity is derived from activation, never an
extra client assumption. All control plumbing stays in the semantic views. -/
theorem SavedCaller.invoke (caller : SavedCaller) {ctx : ProgramCtx} {s u t : Store}
    {es : List Expr} {args values : List GoValue} {fid : FuncId} {f : Func} {a : Activation}
    {locs : List Loc} (mode : NormalExit)
    (operands : OperandValues ctx s caller.locals es args)
    (found : findFunctionIn? ctx.functions fid = some f)
    (method : methodInfoByFuncId? ctx f.id = none) (arity : f.args.size = args.length)
    (activation : LocalEntry ctx f args s (.ok a))
    (body : PickFreeRun ctx ((caller.boundary f a).body f a) ((caller.boundary f a).exit mode u))
    (count : caller.destinations.length = a.results.length)
    (bound : BoundDestinations caller.locals caller.destinations locs)
    (read : Readback ctx u a.results (.ok values)) (writes : WriteValues ctx locs values u t) :
    PickFreeRun ctx (caller.call fid es s) (resumed caller.tail t) :=
  (caller.enter operands found method arity activation).trans
    (body.trans ((caller.boundary f a).deliver mode count activation.resultSlots bound read writes))

end GoLean.GoCore.Relational
