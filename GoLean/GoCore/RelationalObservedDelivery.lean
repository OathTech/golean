import GoLean.GoCore.RelationalObservedPhases

/-! Snapshot callee results before ordered caller writes. All intermediate
stores and source guards are exposed. Repeated and interior destinations are
allowed; no result-read fact is required after the first write. -/
namespace GoLean.GoCore.Relational.Observed
open Machine

private def locationRef (l : Loc) : TargetRef := .chain (.addr l) [] []
private def plans (ids : List VarId) : List (TargetShape × List Expr) :=
  ids.map fun id => (.chain [], [.ref id])

private theorem stores_path (ctx : ProgramCtx) (ls : List Loc) (vs : List GoValue)
    (count : ls.length = vs.length) (env : LocalEnv) (k : Continuation) :
    OrderedWrites ctx ls vs (.next (.storeK (ls.map locationRef) vs (.seqn #[]) env k.toMachine))
      (.next k.toMachine) := by
  induction ls generalizing vs with
  | nil =>
    have : vs = [] := by simpa using count.symm
    subst vs
    exact .nil ((StorePath.pure (fun _ => ⟨Step.storeDone, rfl⟩)
      ⟨(by intro h; cases h), rfl⟩ (by intros; rfl)).trans (empty_sequence_path ctx env k))
  | cons l ls ih =>
    cases vs with
    | nil => simp at count
    | cons v vs =>
      refine .cons .refl ⟨⟨⟨(by intro h; cases h), rfl⟩, ?_⟩, by intros; rfl⟩ (ih vs (by simpa using count))
      intro s t hw
      have store : storeTarget ctx s (locationRef l) v =
          .ok (t, [.access .write (.data l.canon)]) := by
        simp [locationRef, storeTarget, storeTarget.plan, resolveChain, valueAsLoc, Mem.store,
          hw, Bind.bind, Except.bind, pure, Except.pure]
      exact ⟨_, Step.storeStep (r := .ok (t, [.access .write (.data l.canon)]))
        (by rw [store]; rfl) rfl, rfl⟩

private theorem targets_path {ctx : ProgramCtx} {env : LocalEnv} {ids : List VarId}
    {ls : List Loc} (h : BoundDestinations env ids ls) (id : VarId) (l : Loc)
    (hl : LocalEnv.lookup env id = some l) (refs : List TargetRef)
    (vs : List GoValue) (k : Continuation) :
    StorePath ctx (fun _ => True)
      (.evalE (.ref id) env (.tgtOpK (.chain []) [] [] refs (plans ids) .vals [] vs (.seqn #[]) env k.toMachine))
      (.next (.storeK (refs ++ (l :: ls).map locationRef) vs (.seqn #[]) env k.toMachine)) := by
  induction h generalizing id l refs with
  | nil =>
    apply (StorePath.pure (fun s => reference ctx s env _ id l hl)
      ⟨(by intro h; cases h), rfl⟩ (by intros; rfl)).trans
    exact StorePath.pure (fun _ => ⟨Step.tgtOpStores rfl, rfl⟩) ⟨(by intro h; cases h), rfl⟩ (by intros; rfl)
  | @cons id' l' ids ls hl' _ ih =>
    apply (StorePath.pure (fun s => reference ctx s env _ id l hl)
      ⟨(by intro h; cases h), rfl⟩ (by intros; rfl)).trans
    apply (StorePath.pure (fun _ => ⟨Step.tgtOpNext rfl, rfl⟩)
      ⟨(by intro h; cases h), rfl⟩ (by intros; rfl)).trans
    simpa [StorePath, List.append_assoc, plans, locationRef] using ih id' l' hl' (refs ++ [locationRef l])

/-- Snapshot the actual normal return before any destination evaluation or
write. Cleanup carries only True; aliases never require stale readback facts. -/
theorem CallBoundary.delivery_phases (b : CallBoundary) (mode : NormalExit)
    (ctx : ProgramCtx) (locs : List Loc) (vs : List GoValue)
    (count : b.caller.destinations.length = b.results.length)
    (values : vs.length = b.results.length) (valid : ResultSlots b.results)
    (bound : BoundDestinations b.caller.locals b.caller.destinations locs) :
    ∃ after before,
      StepAdmission (b.exit mode ⟨#[]⟩).control ∧
      (∀ s, Readback ctx s b.results (.ok vs) → ∃ l,
        Boundary.Returns ctx (b.exit mode s) ⟨after,s⟩ l ⟨b.function,vs,s⟩ ∧ l.picks = []) ∧
      StorePath ctx (fun _ => True) after before ∧
      OrderedWrites ctx locs vs before (.next b.caller.tail.toMachine) := by
  rcases b with ⟨⟨ids, env, k⟩, fid, results⟩
  dsimp only at count values valid bound ⊢
  have boundCount : ids.length = locs.length := by
    clear count
    induction bound with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  cases bound with
  | nil =>
    have er : results = [] := by simpa using count.symm
    subst results
    have ev : vs = [] := by simpa using values
    subst vs
    refine ⟨.next k.toMachine, .next k.toMachine, ?_, ?_, .refl, .nil .refl⟩
    · cases mode <;> exact ⟨(by intro h; cases h), rfl⟩
    · intro s _
      cases mode
      · exact ⟨_, Boundary.Returns.intro (mode := .falling) .discarded, rfl⟩
      · exact ⟨_, Boundary.Returns.intro (mode := .explicit) .discarded, rfl⟩
  | @cons id loc ids locs hl ht =>
    refine ⟨.evalE (.ref id) env
      (.tgtOpK (.chain []) [] [] [] (plans ids) .vals [] vs (.seqn #[]) env k.toMachine),
      .next (.storeK ((loc :: locs).map locationRef) vs (.seqn #[]) env k.toMachine), ?_, ?_,
      targets_path (ctx := ctx) ht id loc hl [] vs k,
      stores_path ctx _ vs (by simp only [List.length_cons] at boundCount count ⊢; omega) env k⟩
    · cases mode <;> exact ⟨(by intro h; cases h), rfl⟩
    · intro s hs
      obtain ⟨tr, hr⟩ := hs.traced valid
      cases mode
      · exact ⟨_, Boundary.Returns.intro (mode := .falling) (.targets hr), rfl⟩
      · exact ⟨_, Boundary.Returns.intro (mode := .explicit) (.targets hr), rfl⟩

end GoLean.GoCore.Relational.Observed
