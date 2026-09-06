import GoLean.GoCore.RecoveryControlMono

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem ChainTyped.single (bytes : GoString) (recovered : Bool) :
    ChainTyped [⟨.interface .string (.string bytes), recovered⟩] := by
  constructor
  · simp
  · intro entry he
    simp only [List.mem_singleton] at he
    subst entry
    exact ⟨bytes, rfl⟩

theorem ChainTyped.append {left right} (hl : ChainTyped left) (hr : ChainTyped right) :
    ChainTyped (left ++ right) := by
  refine ⟨fun he => hl.1 (List.append_eq_nil_iff.mp he).1, ?_⟩
  intro entry he
  rcases List.mem_append.mp he with he | he
  · exact hl.2 entry he
  · exact hr.2 entry he

theorem markNewest_typed (chain : List PanicEntry)
    (typed : ∀ entry ∈ chain, ∃ bytes, entry.value = .interface .string (.string bytes))
    {v next} (run : markNewestRecovered chain = some (v, next)) :
    (∃ bytes, v = .interface .string (.string bytes)) ∧ ChainTyped next := by
  induction chain generalizing v next with
  | nil => simp [markNewestRecovered] at run
  | cons entry rest ih =>
    cases rest with
    | nil =>
      simp only [markNewestRecovered] at run
      split at run
      · contradiction
      · simp only [Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        obtain ⟨bytes, hv⟩ := typed entry (by simp)
        refine ⟨⟨bytes, hv⟩, by simp, ?_⟩
        intro e he
        simp only [List.mem_singleton] at he
        subst e
        exact ⟨bytes, hv⟩
    | cons first rest =>
      simp only [markNewestRecovered] at run
      cases result : markNewestRecovered (first :: rest) with
      | none => simp [result] at run
      | some resultValue =>
        obtain ⟨out, tail⟩ := resultValue
        simp only [result, Option.map_some, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        obtain ⟨hv, _, ht⟩ := ih (fun e he => typed e (by simp [he])) result
        refine ⟨hv, by simp, ?_⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact typed e (by simp)
        · exact ht e he

theorem ReturnCont.recoverThrough_none {world fs k} (h : ReturnCont world fs k) :
    recoverThroughWrappers k = none := by
  induction h using ReturnCont.rec (motive_2 := fun _ _ => True) with
  | seq he hs _ ih =>
    unfold recoverThroughWrappers at ih ⊢
    rw [Cont.rebuild_descend (by rfl)]
    simp [Cont.tail, ih]
  | frame he hp hr hd _ _ _ _ =>
    unfold recoverThroughWrappers
    rw [Cont.rebuild_act (by rfl)]
  | stop => trivial
  | stmt => trivial
  | resume => trivial

theorem ExitCont.recoverThrough {world fs k} (h : ExitCont world fs k) :
    recoverThroughWrappers k = none ∨
      ∃ v k', recoverThroughWrappers k = some (v, k') ∧
        Delivered world .boxed v ∧ ExitCont world fs k' := by
  cases h with
  | stop =>
    left
    unfold recoverThroughWrappers
    rw [Cont.rebuild_stop]
  | stmt h => exact .inl h.recoverThrough_none
  | @resume chain k hc hk =>
    cases hm : markNewestRecovered chain with
    | none =>
      left
      unfold recoverThroughWrappers
      rw [Cont.rebuild_act (by rfl)]
      simp [hm]
    | some result =>
      obtain ⟨v, next⟩ := result
      obtain ⟨⟨bytes, rfl⟩, ht⟩ := markNewest_typed chain hc.2 hm
      right
      refine ⟨_, .panicResumeK next k, ?_, .boxed bytes, .resume ht hk⟩
      unfold recoverThroughWrappers
      rw [Cont.rebuild_act (by rfl)]
      simp [hm]

/-- Name the option-valued walk inside the shipped `recoverResult`; the
equation below is definitional and keeps this helper tied to that function. -/
def recoverWalk (k : Cont) : Option (GoValue × Cont) :=
  Cont.rebuild Cont.recoverTransparent
    (fun k => match k with
      | .frame t te r ds k' false =>
          some (match recoverThroughWrappers k' with
            | some (v, k'') => (v, .frame t te r ds k'' false)
            | none => (.nil, .frame t te r ds k' false))
      | k => some (.nil, k)) k

theorem recoverResult_eq_walk (k : Cont) :
    recoverResult k = (recoverWalk k).getD (.nil, k) := rfl

theorem recoverWalk_descend {k tail : Cont} (hd : k.recoverTransparent = true)
    (ht : k.tail = some tail) :
    recoverWalk k = (recoverWalk tail).map (fun (v, next) => (v, k.withTail next)) := by
  unfold recoverWalk
  rw [Cont.rebuild_descend hd, ht]

private theorem recoverWalk_lift {world k tail} {P Q : Cont → Prop}
    (hd : k.recoverTransparent = true) (ht : k.tail = some tail)
    (ih : ∃ v next, recoverWalk tail = some (v, next) ∧
      Delivered world (.value .payload) v ∧ P next)
    (lift : ∀ next, P next → Q (k.withTail next)) :
    ∃ v next, recoverWalk k = some (v, next) ∧
      Delivered world (.value .payload) v ∧ Q next := by
  obtain ⟨v, next, run, hv, hp⟩ := ih
  exact ⟨v, k.withTail next, by simp [recoverWalk_descend hd ht, run], hv, lift next hp⟩

theorem ReturnCont.recoverWalk {world fs k} (h : ReturnCont world fs k) :
    ∃ v next, recoverWalk k = some (v, next) ∧
      Delivered world (.value .payload) v ∧ ReturnCont world fs next := by
  induction h using ReturnCont.rec (motive_2 := fun _ _ => True) with
  | seq he hs _ ih =>
    exact recoverWalk_lift rfl rfl ih (fun _ hk => .seq he hs hk)
  | @frame Γ plans ps tenv results ds k he hp hr hd hk wb _ _ =>
    rcases hk.recoverThrough with hnone | ⟨v, next, run, hv, hn⟩
    · refine ⟨.nil, .frame plans tenv results ds k false, ?_, .value .nil,
        .frame he hp hr hd hk wb⟩
      unfold GoLean.GoCore.RecoveryRuntime.recoverWalk
      rw [Cont.rebuild_act (by rfl)]
      simp [hnone]
    · refine ⟨v, .frame plans tenv results ds next false, ?_, hv.coerce .boxPayload,
        .frame he hp hr hd hn ?_⟩
      · unfold GoLean.GoCore.RecoveryRuntime.recoverWalk
        rw [Cont.rebuild_act (by rfl)]
        simp [run]
      · intro hplans
        have impossible := (wb hplans).recoverThrough_none
        rw [impossible] at run
        contradiction
  | stop => trivial
  | stmt => trivial
  | resume => trivial

theorem ValueCont.recoverWalk {world fs kind k} (h : ValueCont world fs kind k) :
    ∃ v next, recoverWalk k = some (v, next) ∧
      Delivered world (.value .payload) v ∧ ValueCont world fs kind next := by
  induction h with
  | coerce hi _ ih =>
    obtain ⟨v, next, run, hv, hk⟩ := ih
    exact ⟨v, next, run, hv, .coerce hi hk⟩
  | strict he ho hd hp _ ih =>
    exact recoverWalk_lift rfl rfl ih (fun _ hk => .strict he ho hd hp hk)
  | and he hr _ ih => exact recoverWalk_lift rfl rfl ih (fun _ hk => .and he hr hk)
  | or he hr _ ih => exact recoverWalk_lift rfl rfl ih (fun _ hk => .or he hr hk)
  | bool _ ih => exact recoverWalk_lift rfl rfl ih (fun _ hk => .bool hk)
  | branch he ht hf nt nf hk =>
    exact recoverWalk_lift rfl rfl hk.recoverWalk (fun _ hk => .branch he ht hf nt nf hk)
  | target he ht hr hp hs hk =>
    exact recoverWalk_lift rfl rfl hk.recoverWalk (fun _ hk => .target he ht hr hp hs hk)
  | rhs he hr hd hp hk =>
    exact recoverWalk_lift rfl rfl hk.recoverWalk (fun _ hk => .rhs he hr hd hp hk)
  | callArgs he hf ha hd hp ht hk =>
    exact recoverWalk_lift rfl rfl hk.recoverWalk (fun _ hk => .callArgs he hf ha hd hp ht hk)
  | callCallee he hf ha hp ht hk =>
    exact recoverWalk_lift rfl rfl hk.recoverWalk (fun _ hk => .callCallee he hf ha hp ht hk)
  | callValueArgs he hf ha hc hd hp ht hk =>
    exact recoverWalk_lift rfl rfl hk.recoverWalk
      (fun _ hk => .callValueArgs he hf ha hc hd hp ht hk)
  | deferCallee he hf ha hp hk =>
    exact recoverWalk_lift rfl rfl hk.recoverWalk (fun _ hk => .deferCallee he hf ha hp hk)
  | deferArgs he hf ha hc hd hp hk =>
    exact recoverWalk_lift rfl rfl hk.recoverWalk (fun _ hk => .deferArgs he hf ha hc hd hp hk)
  | panic hk => exact recoverWalk_lift rfl rfl hk.recoverWalk (fun _ hk => .panic hk)

/-- Actual recovery never loses the pending expression's expected type or
saved scopes. The returned payload is nil or one of the typed chain values. -/
theorem ValueCont.recover {world fs kind k} (h : ValueCont world fs kind k) :
    ∃ v next, recoverResult k = (v, next) ∧
      Delivered world (.value .payload) v ∧ ValueCont world fs kind next := by
  obtain ⟨v, next, run, hv, hk⟩ := h.recoverWalk
  exact ⟨v, next, by simp [recoverResult_eq_walk, run], hv, hk⟩

/-- An ordinary caller frame blocks recovery even when a panic is suspended
farther below it. This is an equation for the actual recover function. -/
theorem recover_indirect {world fs k} (hk : ReturnCont world fs k)
    (targets : List (TargetShape × List Expr)) (env : LocalEnv)
    (results : List Loc) (ds : List (GoValue × List GoValue)) :
    recoverResult (.frame targets env results ds k false) =
      (.nil, .frame targets env results ds k false) := by
  unfold recoverResult
  rw [Cont.rebuild_act (by rfl)]
  simp [hk.recoverThrough_none]

/-- Direct recovery changes only the newest suspended entry's recovered
flag; the payload and rebuilt call frame are exactly those of the machine. -/
theorem recover_direct {chain next v} (hm : markNewestRecovered chain = some (v, next))
    (targets : List (TargetShape × List Expr)) (env : LocalEnv)
    (results : List Loc) (ds : List (GoValue × List GoValue)) (k : Cont) :
    recoverResult (.frame targets env results ds (.panicResumeK chain k) false) =
      (v, .frame targets env results ds (.panicResumeK next k) false) := by
  unfold recoverResult
  rw [Cont.rebuild_act (by rfl)]
  dsimp only
  unfold recoverThroughWrappers
  rw [Cont.rebuild_act (by rfl)]
  simp [hm]

theorem pushDefer_seq (d : GoValue × List GoValue) (ss : List Stmt)
    (env : LocalEnv) (k : Cont) :
    pushDefer d (.seq ss env k) = (pushDefer d k).map (fun next => .seq ss env next) := by
  unfold pushDefer
  rw [Cont.rebuild_descend (by rfl)]
  simp only [Cont.tail, Option.map_map]
  rfl

/-- Registration modifies only the nearest real frame and prepends the
fully evaluated invocation, preserving LIFO order without executing it. -/
theorem ReturnCont.pushDefer {world fs k d} (hk : ReturnCont world fs k)
    (hd : PendingCall world fs d.1 d.2) :
    ∃ next, pushDefer d k = some next ∧ ReturnCont world fs next := by
  induction hk using ReturnCont.rec (motive_2 := fun _ _ => True) with
  | seq he hs _ ih =>
    obtain ⟨next, run, hk⟩ := ih
    exact ⟨_, by simp [pushDefer_seq, run], .seq he hs hk⟩
  | @frame Γ plans ps env results ds k he hp hr hds hk wb _ _ =>
    refine ⟨.frame plans env results (d :: ds) k false, ?_, .frame he hp hr ?_ hk wb⟩
    · unfold Machine.pushDefer
      rw [Cont.rebuild_act (by rfl)]
      rfl
    · intro d' hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hd
      · exact hds d' hmem
  | stop => trivial
  | stmt => trivial
  | resume => trivial

end GoLean.GoCore.RecoveryRuntime
