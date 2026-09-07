import GoLean.GoCore.RecoveryValueBasic

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem call_args_advances {p : Program} {world s Γ env f fid plans before q after done pending k v}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (hf : findFunctionIn? p.funcs fid = some f)
    (arity : f.args.toList = before ++ q :: after)
    (hd : ParamsValues world before done) (ha : Arguments Γ pending after)
    (ht : PlansTyped Γ plans f.results.toList) (hk : ReturnCont world p.funcs k)
    (hv : Delivered world (.typed q.typ) v) :
    Advances world p.funcs s (.retV v (.callArgsK fid plans done pending env k)) := by
  cases hv with
  | typed hv =>
    have hdone := hd.append (.cons hv .nil)
    cases ha with
    | nil =>
      have args : ParamsValues world f.args.toList (done ++ [v]) := arity ▸ hdone
      intro ch
      obtain ⟨next, env', roots, t, run, ext, hw, control⟩ :=
        call_entry_control hp hc heap hf args he ht hk ch
      exact ⟨next, _, t, by simp only [stepFn, run]; simp [deliverS, hw,
        Bind.bind, Except.bind, Pure.pure, Except.pure], ext, control⟩
    | @cons _ _ q' qs' harg hargs =>
      have arity' : f.args.toList = (before ++ [q]) ++ q' :: qs' := by
        simpa only [List.append_assoc, List.singleton_append] using arity
      exact advances_same heap (.eval he (.typed harg)
        (.callArgs he hf arity' hdone hargs ht hk)) (fun _ => rfl)

theorem call_callee_advances {p : Program} {world s Γ env f fid caps ps args plans k v}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (hf : findFunctionIn? p.funcs fid = some f) (arity : f.args.toList = caps ++ ps)
    (ha : Arguments Γ args ps) (ht : PlansTyped Γ plans f.results.toList)
    (hk : ReturnCont world p.funcs k) (hv : Delivered world (.closure fid caps) v) :
    Advances world p.funcs s (.retV v (.callValCalleeK plans args env k)) := by
  cases hv with
  | @closure _ _ capValues hcaps =>
    cases ha with
    | nil =>
      have args : ParamsValues world f.args.toList capValues := by simpa [arity] using hcaps
      intro ch
      obtain ⟨next, env', roots, t, run, ext, hw, control⟩ :=
        call_entry_control hp hc heap hf args he ht hk ch
      exact ⟨next, _, t, by simp only [stepFn, run]; simp [deliverS, hw,
        Bind.bind, Except.bind, Pure.pure, Except.pure], ext, control⟩
    | cons harg hargs =>
      exact advances_same heap (.eval he (.typed harg)
        (.callValueArgs (before := []) he hf arity hcaps .nil hargs ht hk)) (fun _ => rfl)

theorem call_value_args_advances {p : Program}
    {world s Γ env f fid caps capValues before q after plans done pending k v}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (hf : findFunctionIn? p.funcs fid = some f)
    (arity : f.args.toList = caps ++ (before ++ q :: after))
    (hcap : ParamsValues world caps capValues) (hd : ParamsValues world before done)
    (ha : Arguments Γ pending after) (ht : PlansTyped Γ plans f.results.toList)
    (hk : ReturnCont world p.funcs k) (hv : Delivered world (.typed q.typ) v) :
    Advances world p.funcs s
      (.retV v (.callValArgsK (.funcVal fid capValues) plans done pending env k)) := by
  cases hv with
  | typed hv =>
    have hdone := hd.append (.cons hv .nil)
    cases ha with
    | nil =>
      have args : ParamsValues world f.args.toList (capValues ++ done ++ [v]) := by
        simpa only [arity, List.append_assoc] using hcap.append hdone
      intro ch
      obtain ⟨next, env', roots, t, run, ext, hw, control⟩ :=
        call_entry_control hp hc heap hf args he ht hk ch
      exact ⟨next, _, t, by simp only [stepFn, run]; simp [deliverS, hw,
        Bind.bind, Except.bind, Pure.pure, Except.pure], ext, control⟩
    | @cons _ _ q' qs' harg hargs =>
      have arity' : f.args.toList = caps ++ ((before ++ [q]) ++ q' :: qs') := by
        simpa only [List.append_assoc, List.singleton_append] using arity
      exact advances_same heap (.eval he (.typed harg)
        (.callValueArgs he hf arity' hcap hdone hargs ht hk)) (fun _ => rfl)

theorem defer_callee_advances {world fs s Γ env f fid caps ps args k v}
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (hf : findFunctionIn? fs fid = some f) (arity : f.args.toList = caps ++ ps)
    (ha : Arguments Γ args ps) (hk : ReturnCont world fs k)
    (hv : Delivered world (.closure fid caps) v) :
    Advances world fs s (.retV v (.deferCalleeK args env k)) := by
  cases hv with
  | @closure _ _ values hcaps =>
    cases ha with
    | nil =>
      have args : ParamsValues world f.args.toList values := by simpa [arity] using hcaps
      have pending : PendingCall world fs (.funcVal fid values) [] :=
        ⟨fid, values, f, rfl, hf, by simpa using args⟩
      obtain ⟨next, run, control⟩ := hk.pushDefer (d := (.funcVal fid values, [])) pending
      exact advances_same heap (.next (.stmt control))
        (fun _ => by simp [stepFn, deferrableCallee, run])
    | cons harg hargs =>
      exact advances_same heap (.eval he (.typed harg)
        (.deferArgs (before := []) he hf arity hcaps .nil hargs hk)) (fun _ => rfl)

theorem defer_args_advances {world fs s Γ env f fid caps capValues before q after done pending k v}
    (heap : HeapTyped world s) (he : EnvTyped world Γ env)
    (hf : findFunctionIn? fs fid = some f)
    (arity : f.args.toList = caps ++ (before ++ q :: after))
    (hcap : ParamsValues world caps capValues) (hd : ParamsValues world before done)
    (ha : Arguments Γ pending after) (hk : ReturnCont world fs k)
    (hv : Delivered world (.typed q.typ) v) :
    Advances world fs s (.retV v (.deferArgsK (.funcVal fid capValues) done pending env k)) := by
  cases hv with
  | typed hv =>
    have hdone := hd.append (.cons hv .nil)
    cases ha with
    | nil =>
      have args : ParamsValues world f.args.toList (capValues ++ (done ++ [v])) :=
        arity ▸ hcap.append hdone
      have hpending : PendingCall world fs (.funcVal fid capValues) (done ++ [v]) :=
        ⟨fid, capValues, f, rfl, hf, args⟩
      obtain ⟨next, run, control⟩ := hk.pushDefer
        (d := (.funcVal fid capValues, done ++ [v])) hpending
      exact advances_same heap (.next (.stmt control)) (fun _ => by simp [stepFn, run])
    | @cons _ _ q' qs' harg hargs =>
      have arity' : f.args.toList = caps ++ ((before ++ [q]) ++ q' :: qs') := by
        simpa only [List.append_assoc, List.singleton_append] using arity
      exact advances_same heap (.eval he (.typed harg)
        (.deferArgs he hf arity' hcap hdone hargs hk)) (fun _ => rfl)

theorem value_advances {p : Program} {world s kind k v}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (hk : ValueCont world p.funcs kind k)
    (hv : Delivered world kind v) : Advances world p.funcs s (.retV v k) := by
  induction hk generalizing v with
  | coerce h _ ih => exact ih (hv.coerce h)
  | strict he ho hd ht hk _ => exact strict_advances heap he ho hd ht hk hv
  | and he ht hk _ => exact and_advances heap he ht hk hv
  | or he ht hk _ => exact or_advances heap he ht hk hv
  | bool hk _ => exact bool_advances heap hk hv
  | branch he ht hf nt nf hk => exact branch_advances heap he ht hf nt nf hk hv
  | target he ht hr ht' source hk => exact target_advances heap he ht hr ht' source hk hv
  | rhs he hr hd ht hk => exact rhs_advances heap he hr hd ht hk hv
  | callArgs he hf arity hd ha ht hk =>
    exact call_args_advances hp hc heap he hf arity hd ha ht hk hv
  | callCallee he hf arity ha ht hk =>
    exact call_callee_advances hp hc heap he hf arity ha ht hk hv
  | callValueArgs he hf arity hcap hd ha ht hk =>
    exact call_value_args_advances hp hc heap he hf arity hcap hd ha ht hk hv
  | deferCallee he hf arity ha hk => exact defer_callee_advances heap he hf arity ha hk hv
  | deferArgs he hf arity hcap hd ha hk =>
    exact defer_args_advances heap he hf arity hcap hd ha hk hv
  | panic hk => exact panic_advances heap hk hv

end GoLean.GoCore.RecoveryRuntime
