import GoLean.GoCore.PoolStructure
import GoLean.GoCore.PoolErrorFacts
import GoLean.GoCore.PoolReplayFacts

/-!
# Proofs for the frozen pool/registry statements

[AGENT Codex, pool grind] 2026-10-05. The milestone boundaries and frozen surface are
specified in `docs/2026-10-04_pool-relation-grind-brief.md`.
-/

namespace GoLean.GoCore.PoolSound

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Semantics GoLean.Semantics.Pool
open GoLean.GoCore.PoolStatement
open GoLean.GoCore.ExecutionStatement (replays replay_coverage)
open GoLean.GoCore.PoolReplayFacts

private theorem raceAccess_error {r : RaceState} {who : Nat} {kind : AccessKind}
    {key : ShadowKey} {e : Stop} (h : r.accessKey who kind key = .error e) :
    e = .raceDetected := by
  dsimp [RaceState.accessKey] at h
  split at h
  · cases h; rfl
  · cases h

private theorem raceEvent_error {r : RaceState} {who : Nat} {ev : MemEvent}
    {e : Stop} (h : r.event who ev = .error e) : e = .raceDetected := by
  induction ev generalizing who with
  | access kind key => exact raceAccess_error h
  | hb a => cases h
  | attributed other ev ih => exact ih h

private theorem raceEvents_error {r : RaceState} {who : Nat} {tr : AccessTrace}
    {e : Stop} (h : r.events who tr = .error e) : e = .raceDetected := by
  induction tr generalizing r with
  | nil => cases h
  | cons ev rest ih =>
      simp only [RaceState.events] at h
      cases he : r.event who ev with
      | error e' =>
          rw [he] at h
          change Except.error e' = Except.error e at h
          cases h
          exact raceEvent_error he
      | ok r' =>
          rw [he] at h
          exact ih h

theorem raceUpdate_error : raceUpdate_error_stmt := by
  intro ev m' r e h
  unfold raceUpdate at h
  split at h
  · cases h
  · exact raceEvents_error h



private theorem stepThreadInto_strict {ctx : ProgramCtx} {m : MultiConfig} {i : Nat}
    {ch : Choices} (hs : schedPick ctx m i) :
    ErrP Stop.Strict (stepThreadInto ctx m i ch) := by
  unfold stepThreadInto
  exact ErrP.bind (PoolErrorFacts.stepThread_strict hs) (fun _ => ErrP.pure)

private theorem strict_pool_error {e : Stop} (h : e.Strict) :
    (∃ r : Refusal, e = .refusal r) ∨ (∃ msg : String, e = .fatal msg) ∨ e = .deadlock := by
  rcases e with (_ | _ | _) | (_ | _ | _ | _) | _ <;>
    first | exact .inl ⟨_, rfl⟩ | exact .inr (.inl ⟨_, rfl⟩) | exact h.elim

theorem stepMulti_error_cases : stepMulti_error_cases_stmt := by
  intro ctx m ch e h
  unfold stepMulti at h
  cases hcur : m.threads[m.cur]? with
  | none =>
      rw [hcur] at h
      cases h
      exact .inl ⟨_, rfl⟩
  | some t =>
      rw [hcur] at h
      by_cases hb : t.atBoundary = true
      · simp only [hb, reduceIte] at h
        cases hrs : schedSlots ctx m.shared m.threads m.cur t.boundarySite with
        | nil =>
            rw [hrs] at h
            cases h
            exact .inr (.inr rfl)
        | cons r0 rest =>
            rw [hrs] at h
            dsimp only at h
            rcases hcons : Choices.consumeAtE t.boundarySite (r0 :: rest).length ch
              with ⟨pick, ch₁, ps⟩
            rw [hcons] at h
            cases hget : (r0 :: rest)[pick]? with
            | none =>
                rw [hget] at h
                cases h
                exact .inl ⟨_, rfl⟩
            | some i =>
                rw [hget] at h
                have hmem : i ∈ runnableIdxs ctx m.shared m.threads := by
                  refine schedSlots_mem hcur ?_
                  rw [hrs]
                  exact List.mem_of_getElem? hget
                have hi := stepThreadInto_strict (ch := ch₁) (schedPick_of_boundary hcur hb hmem)
                exact strict_pool_error (ErrP.bind hi (fun _ => ErrP.pure) e h)
      · simp only [Bool.not_eq_true] at hb
        simp only [hb, Bool.false_eq_true, reduceIte] at h
        exact strict_pool_error (stepThreadInto_strict (schedPick_cur hcur hb) e h)

theorem schedSlot_iff : schedSlot_iff_stmt := by
  intro ctx m i
  unfold schedPick SchedSlot
  cases hcur : m.threads[m.cur]? with
  | none => simp
  | some t =>
      by_cases hb : t.atBoundary = true
      · simp only [if_pos hb]
        constructor
        · intro hi
          exact List.mem_iff_getElem?.mp (mem_schedSlots_of_runnable hi)
        · rintro ⟨slot, hslot⟩
          exact schedSlots_mem hcur (List.mem_of_getElem? hslot)
      · simp [hb]

-- Shared case-tree simp sets follow MultiSound; some entries apply in only one arm.
set_option linter.unusedSimpArgs false in
private theorem stepThreadInto_labelled {ctx : ProgramCtx} {m : MultiConfig} {i slot : Nat} {ch ch' : Choices}
    {m' : MultiConfig} {ev : StepEvent} (hsched : SchedSlot ctx m i slot)
    (h : stepThreadInto ctx m i ch = .ok (m', ch', ev)) : StepML ctx m m' { ev with label := { ev.label with picks := schedRecord ctx m slot ++ ev.picks } } := by
  unfold stepThreadInto at h
  simp only [Bind.bind, Except.bind] at h
  cases hst : stepThread ctx m.shared m.threads i ch with
  | error e => rw [hst] at h; cases h
  | ok r =>
    obtain ⟨ts, s', chX, evX⟩ := r
    rw [hst] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    unfold stepThread at hst
    cases hti : m.threads[i]? with
    | none => rw [hti] at hst; cases hst
    | some t =>
      rw [hti] at hst
      cases t with
      | aborted msg => simp [throw, throwThe, MonadExceptOf.throw] at hst
      | running c b =>
      cases b with
      | some site =>
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
        simpa only [StepEvent.picks, List.append_nil] using StepML.strip hsched hti
      | none =>
      by_cases hbl : isBlockedConfig c = true
      · -- WAKE
        simp only [hbl, reduceIte, Bind.bind, Except.bind] at hst
        cases hres : resumeThread ctx m.shared c with
        | error e => rw [hres] at hst; cases hst
        | ok r₂ =>
          obtain ⟨c', s₂, tr₂⟩ := r₂
          rw [hres] at hst
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
          simpa only [StepEvent.picks, List.append_nil] using StepML.wake hsched hti hbl hres
      · simp only [Bool.not_eq_true] at hbl
        simp only [hbl, Bool.false_eq_true, reduceIte] at hst
        cases hab : c.abort? with
        | some p =>
          obtain ⟨first, rest⟩ := p
          rw [hab] at hst
          simp only [Bind.bind, Except.bind] at hst
          have hpick : (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1
              < repanicCollapseWidth first rest := by
            have := @Choices.consumeAtE_fst_snd .repanicCollapse (repanicCollapseWidth first rest) ch
            have hlt := Choices.consumeAt_fst_lt (site := .repanicCollapse) (ch := ch)
              (bound := repanicCollapseWidth first rest)
              (by unfold repanicCollapseWidth; split <;> omega)
            rw [← this] at hlt
            exact hlt
          cases hmsg : abortMsg ctx first rest
              (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1 with
          | error e => rw [hmsg] at hst; cases hst
          | ok msg =>
            rw [hmsg] at hst
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
            simpa only [StepEvent.picks, Choices.consumeAtE_eq] using
              StepML.abort hsched hti hab hpick hmsg
        | none =>
        rw [hab] at hst
        cases hsp : spawnPlan c with
        | some p =>
          obtain ⟨cv, args, k⟩ := p
          rw [hsp] at hst
          simp only [Bind.bind, Except.bind] at hst
          cases hspawn : spawnStep ctx m.shared cv args k ch with
          | error e => rw [hspawn] at hst; cases hst
          | ok r₂ =>
            obtain ⟨parent', child, s₂, ch₂, tr₂⟩ := r₂
            rw [hspawn] at hst
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
            exact StepML.spawn hsched hti hsp hspawn
        | none =>
          rw [hsp] at hst
          simp only [Bind.bind, Except.bind] at hst
          cases hac : arrivalCases ctx m.shared m.threads i c with
          | error e => rw [arrivalPlan_of_error hac] at hst; cases hst
          | ok analysis =>
            cases analysis with
            | cellPath =>
              rw [arrivalPlan_of_cellPath hac] at hst
              simp only [Bind.bind, Except.bind] at hst
              cases hselp : selectApplyPlan c with
              | none =>
                rw [hselp] at hst
                dsimp only at hst
                cases hstep : stepFn ctx m.shared c ch with
                | error e => rw [hstep] at hst; cases hst
                | ok r₂ =>
                  obtain ⟨c', s₂, ch₂, tr₂⟩ := r₂
                  rw [hstep] at hst
                  dsimp only at hst
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq,
                    Thread.afterStepWith_boundaryFacts] at hst
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
                  exact StepML.thread hsched hti hbl hsp hac hselp (stepFn_sound hstep)
              | some p =>
                obtain ⟨v, clauses, default?, done, env, k'⟩ := p
                obtain rfl := selectApplyPlan_shape hselp
                rw [hselp] at hst
                dsimp only at hst
                cases happly : applySelect ctx m.shared clauses default?
                    ((v :: done).reverse) env k' ch with
                | ok r₂ =>
                  obtain ⟨c', s₂, ch₂, cl?⟩ := r₂
                  rw [happly] at hst
                  simp only [toResult_ok, Bind.bind, Except.bind, pure_eq_ok,
                    Except.ok.injEq, Prod.mk.injEq, Thread.afterStepWith_boundaryFacts] at hst
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
                  exact StepML.selectApply hsched hti hselp hac happly
                | error e =>
                  rw [happly] at hst
                  cases_stop e <;>
                    simp only [toResult_panic, toResult_refusal, toResult_fatal, toResult_deadlock,
                      toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind, pure_eq_ok,
                      deliver_panic, List.nil_append, Except.ok.injEq, Prod.mk.injEq,
                      reduceCtorEq, Thread.afterStepWith_boundaryFacts] at hst
                  case panic msg =>
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
                  simpa only [StepEvent.picks, List.append_nil] using
                    StepML.selectApplyPanic hsched hti hselp hac happly
            | single bc cs =>
              rw [arrivalPlan_of_single hac] at hst
              simp only [Bind.bind, Except.bind] at hst
              cases cs with
              | nil => cases hst
              | cons cand rest =>
                  simp only [Bind.bind, Except.bind] at hst
                  rcases hcons : Choices.consumeAtE .l4Waiter
                      (cand :: rest).length ch with ⟨idx, ch₃, ps₃⟩
                  rw [hcons] at hst
                  cases hget : (cand :: rest)[idx]? with
                  | none => rw [hget] at hst; cases hst
                  | some cand' =>
                    rw [hget] at hst
                    simp only [Bind.bind, Except.bind] at hst
                    cases hap : applyPairing ctx m.shared m.threads i bc cand' with
                    | error e => rw [hap] at hst; cases hst
                    | ok r₃ =>
                      obtain ⟨ts', s₃, tr₃⟩ := r₃
                      rw [hap] at hst
                      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
                      obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
                      obtain ⟨hlt, hidxeq⟩ := List.getElem?_eq_some_iff.mp hget
                      have hps := (Choices.consumeAtE_inv hcons).1
                      simpa only [StepEvent.picks, hps, hidxeq, List.nil_append] using
                        StepML.pair hsched hti hbl hsp hac (idx := idx) hlt
                          (by rw [hidxeq]; exact hap)
            | multi os =>
              rcases hcons : ch.consume os.length with ⟨sel, chL⟩
              rw [arrivalPlan_of_multi hac hcons] at hst
              cases hget : os[sel]? with
              | none => rw [hget] at hst; cases hst
              | some o =>
                rw [hget] at hst
                cases o with
                | pair bc cs =>
                  simp only [Bind.bind, Except.bind] at hst
                  cases cs with
                  | nil => cases hst
                  | cons cand rest =>
                      simp only [Bind.bind, Except.bind] at hst
                      rcases hconsL : Choices.consumeAtE .l4Waiter
                          (cand :: rest).length chL with ⟨idx, ch₃, ps₃⟩
                      rw [hconsL] at hst
                      cases hgetL : (cand :: rest)[idx]? with
                      | none => rw [hgetL] at hst; cases hst
                      | some cand' =>
                        rw [hgetL] at hst
                        simp only [Bind.bind, Except.bind] at hst
                        cases hap : applyPairing ctx m.shared m.threads i bc cand' with
                        | error e => rw [hap] at hst; cases hst
                        | ok r₃ =>
                          obtain ⟨ts', s₃, tr₃⟩ := r₃
                          rw [hap] at hst
                          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
                          obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
                          obtain ⟨hlt, hidxeq⟩ := List.getElem?_eq_some_iff.mp hgetL
                          have hps := (Choices.consumeAtE_inv hconsL).1
                          have hlen : ¬ os.length ≤ 1 := Nat.not_le_of_lt (arrivalCases_multi_length hac)
                          simpa only [StepEvent.picks, hps, hidxeq, PickRecord.ofPick, if_neg hlen] using
                            StepML.pickPair hsched hti hbl hsp hac hget (idx := idx) hlt
                              (by rw [hidxeq]; exact hap)
                | commit evs cl envc kc =>
                  simp only [Bind.bind, Except.bind] at hst
                  cases hcom : commitClause ctx m.shared envc kc cl with
                  | error e => rw [hcom] at hst; cases hst
                  | ok r₃ =>
                    obtain ⟨c₃, s₃, tr₃⟩ := r₃
                    rw [hcom] at hst
                    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hst
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
                    have hlen : ¬ os.length ≤ 1 := Nat.not_le_of_lt (arrivalCases_multi_length hac)
                    simpa only [StepEvent.picks, PickRecord.ofPick, if_neg hlen,
                      Thread.afterStepWith_boundaryFacts] using
                      StepML.pickCommit hsched hti hbl hsp hac hget hcom


theorem stepML_sound : stepML_sound_stmt := by
  intro ctx m m' ch ch' ev h
  unfold stepMulti at h
  cases hcur : m.threads[m.cur]? with
  | none => rw [hcur] at h; cases h
  | some t =>
    rw [hcur] at h
    by_cases hb : t.atBoundary = true
    · simp only [hb, reduceIte] at h
      cases hrs : schedSlots ctx m.shared m.threads m.cur t.boundarySite with
      | nil => rw [hrs] at h; cases h
      | cons r0 rest =>
        rw [hrs] at h
        dsimp only at h
        rcases hcons : Choices.consumeAtE t.boundarySite
            (r0 :: rest).length ch
          with ⟨pick, ch₁, ps⟩
        rw [hcons] at h
        cases hget : (r0 :: rest)[pick]? with
        | none => rw [hget] at h; cases h
        | some i =>
          rw [hget] at h
          simp only [Bind.bind, Except.bind] at h
          cases hinto : stepThreadInto ctx m i ch₁ with
          | error e => rw [hinto] at h; cases h
          | ok r =>
            obtain ⟨m₂, ch₂, evI⟩ := r
            rw [hinto] at h
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have hslot : SchedSlot ctx m i pick := by
              simp only [SchedSlot, hcur, hb, reduceIte, hrs]
              exact hget
            have hps := (Choices.consumeAtE_inv hcons).1
            simpa only [schedRecord, hcur, hb, reduceIte, hrs, hps] using
              stepThreadInto_labelled hslot hinto
    · simp only [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, reduceIte] at h
      have hslot : SchedSlot ctx m m.cur 0 := by simp [SchedSlot, hcur, hb]
      simpa only [schedRecord, hcur, hb, Bool.false_eq_true, reduceIte, List.nil_append] using
        stepThreadInto_labelled hslot h


private theorem consult_realize (site : ChoiceSite) {bound pick : Nat}
    (hp : pick < bound) (rest : Choices) :
    ∃ ch, Choices.consumeAtE site bound ch = (pick, rest, PickRecord.ofPick site bound pick) := by
  by_cases hb : bound ≤ 1
  · have h0 : pick = 0 := by omega
    subst pick
    exact ⟨rest, by simp [Choices.consumeAtE_le_one hb, PickRecord.ofPick, hb]⟩
  · refine ⟨pick :: rest, ?_⟩
    rw [Choices.consumeAtE_eq, Choices.consumeAt_of_lt (by omega)]
    simp [Choices.consume, Nat.max_eq_right (by omega : 1 ≤ bound), Nat.mod_eq_of_lt hp]

private theorem stepMulti_of_slot {ctx : ProgramCtx} {m : MultiConfig} {i slot : Nat}
    {chI chI' : Choices} {ts : Array Thread} {s' : Store} {evI : StepEvent}
    (hs : SchedSlot ctx m i slot)
    (hi : stepThread ctx m.shared m.threads i chI = .ok (ts, s', chI', evI)) :
    ∃ ch ch', stepMulti ctx m ch = .ok (⟨ts, s', i⟩, ch',
      { evI with label := { evI.label with picks := schedRecord ctx m slot ++ evI.picks } }) := by
  unfold SchedSlot at hs
  cases hcur : m.threads[m.cur]? with
  | none => simp [hcur] at hs
  | some t =>
      rw [hcur] at hs
      by_cases hb : t.atBoundary = true
      · simp only [hb, reduceIte] at hs
        have hlt := (List.getElem?_eq_some_iff.mp hs).1
        obtain ⟨ch, hch⟩ := consult_realize t.boundarySite hlt chI
        refine ⟨ch, chI', ?_⟩
        unfold stepMulti
        rw [hcur]
        simp only [hb, reduceIte]
        cases hrs : schedSlots ctx m.shared m.threads m.cur t.boundarySite with
        | nil => simp [hrs] at hs
        | cons a as =>
            rw [hrs] at hch hs
            simp only [hch, hs, Bind.bind, Except.bind]
            unfold stepThreadInto
            rw [hi]
            simp only [schedRecord, hcur, hb, reduceIte, hrs]
            rfl
      · simp only [hb] at hs
        obtain ⟨rfl, rfl⟩ := hs
        refine ⟨chI, chI', ?_⟩
        simp only [stepMulti, hcur, hb, stepThreadInto, hi, schedRecord]
        rfl

set_option linter.unusedSimpArgs false in
theorem stepML_complete : stepML_complete_stmt := by
  intro ctx m m' ev h
  cases h with
  | strip hs hi =>
      simpa only [StepEvent.picks, List.append_nil] using stepMulti_of_slot hs
        (show stepThread ctx _ _ _ [] = .ok (_, _, [], ⟨_, .opDoneStrip, ⟨[], [], []⟩⟩) from by
          unfold stepThread; rw [hi]; rfl)
  | abort hs hi hab hp hmsg =>
      rename_i i slot c first rest pick msg
      obtain ⟨ch, hch⟩ := consult_realize .repanicCollapse hp []
      exact stepMulti_of_slot hs (show stepThread ctx _ _ _ ch = .ok (_, _, [],
        ⟨i, .aborted, ⟨[], PickRecord.ofPick .repanicCollapse _ pick, []⟩⟩) from by
          unfold stepThread
          rw [hi]
          simp only [isBlockedConfig_of_abort hab, Bool.false_eq_true, reduceIte, hab, hch,
            hmsg, Bind.bind, Except.bind]
          rfl)
  | spawn hs hi hsp hspawn =>
      rename_i i slot c cv args k parent child s' ch ch' ps tr
      have hb : isBlockedConfig c = false := by
        match c, hsp with
        | .retV _ (.goCalleeK [] _ _), _ => rfl
        | .retV _ (.goArgsK _ _ [] _ _), _ => rfl
      have hab : c.abort? = none := by
        match c, hsp with
        | .retV _ (.goCalleeK [] _ _), _ => rfl
        | .retV _ (.goArgsK _ _ [] _ _), _ => rfl
      exact stepMulti_of_slot hs (show stepThread ctx _ _ _ ch = .ok (_, _, ch',
        ⟨i, .spawned m.threads.size, ⟨.hb (.spawn m.threads.size) :: tr.map (.attributed m.threads.size), ps, []⟩⟩) from by
          unfold stepThread
          rw [hi]
          simp only [hb, Bool.false_eq_true, reduceIte, hab, hsp, Bind.bind, Except.bind, hspawn]
          rfl)
  | thread hs hi hb hsp hac hsel hstep =>
      rename_i i slot c c' s' l
      obtain ⟨ch, ch', hfn⟩ := step_complete hstep
      have hab : c.abort? = none := abort?_none_of_stepE (StepE.lift (n := m.threads.size) hstep)
      exact stepMulti_of_slot hs (show stepThread ctx _ _ _ ch = .ok (_, _, ch', ⟨i, .privateStep, l⟩) from by
        unfold stepThread
        rw [hi]
        simp only [hb, Bool.false_eq_true, reduceIte, hab, hsp, Bind.bind, Except.bind]
        rw [arrivalPlan_of_cellPath hac]
        simp only [Bind.bind, Except.bind, hsel]
        rw [hfn]
        rfl)
  | selectApply hs hi hsel hac happly =>
      rename_i i slot c v clauses default done env k ch ch' c' s' ps cl tr
      obtain rfl := selectApplyPlan_shape hsel
      exact stepMulti_of_slot hs (show stepThread ctx _ _ _ ch = .ok (_, _, ch',
        ⟨i, selectAction cl, ⟨tr, ps, []⟩⟩) from by
          unfold stepThread
          rw [hi]
          simp only [isBlockedConfig, Config.abort?, spawnPlan, Bool.false_eq_true, reduceIte]
          rw [arrivalPlan_of_cellPath hac]
          simp only [Bind.bind, Except.bind, hsel]
          rw [happly]
          rfl)
  | selectApplyPanic hs hi hsel hac happly =>
      rename_i i slot c v clauses default done env k ch msg
      obtain rfl := selectApplyPlan_shape hsel
      simpa only [StepEvent.picks, List.append_nil] using stepMulti_of_slot hs
        (show stepThread ctx _ _ _ ch = .ok (_, _, ch, ⟨i, .selectPass, ⟨[], [], []⟩⟩) from by
          unfold stepThread
          rw [hi]
          simp only [isBlockedConfig, Config.abort?, spawnPlan, Bool.false_eq_true, reduceIte]
          rw [arrivalPlan_of_cellPath hac]
          simp only [Bind.bind, Except.bind, hsel]
          rw [happly]
          rfl)
  | wake hs hi hb hres =>
      simpa only [StepEvent.picks, List.append_nil] using stepMulti_of_slot hs
        (show stepThread ctx _ _ _ [] = .ok (_, _, [], ⟨_, .woke, ⟨_, [], []⟩⟩) from by
          unfold stepThread; rw [hi]; simp only [hb, reduceIte, hres, Bind.bind, Except.bind]; rfl)

  | pair hs hi hb hsp hac hidx hap =>
      rename_i i slot c bc s' cs idx ts tr
      have hab : c.abort? = none := by
        cases hab : c.abort? with
        | none => rfl
        | some p =>
            obtain ⟨first, rest⟩ := p
            match c, hab, hac with
            | .panicking (_ :: _) .stop, _, hac => cases hac
      obtain ⟨ch, hch⟩ := consult_realize .l4Waiter hidx []
      exact stepMulti_of_slot hs (show stepThread ctx _ _ _ ch = .ok (ts, s', [],
        ⟨i, .paired cs[idx].2.partnerIdx, ⟨tr, PickRecord.ofPick .l4Waiter cs.length idx, []⟩⟩) from by
          unfold stepThread
          rw [hi]
          simp only [hb, Bool.false_eq_true, reduceIte, hab, hsp, Bind.bind, Except.bind]
          rw [arrivalPlan_of_single hac]
          cases cs with
          | nil => simp at hidx
          | cons a as =>
              simp only [Bind.bind, Except.bind]
              rw [hch, List.getElem?_eq_getElem hidx]
              simp only [Bind.bind, Except.bind]
              rw [hap]
              rfl)
  | pickPair hs hi hb hsp hac hget hidx hap =>
      rename_i i slot c bc s' os sel cs idx ts tr
      have hab : c.abort? = none := by
        cases hab : c.abort? with
        | none => rfl
        | some p =>
            obtain ⟨first, rest⟩ := p
            match c, hab, hac with
            | .panicking (_ :: _) .stop, _, hac => cases hac
      obtain ⟨chW, hW⟩ := consult_realize .l4Waiter hidx []
      obtain ⟨ch, hch⟩ := consult_realize .l2Arrival (List.getElem?_eq_some_iff.mp hget).1 chW
      exact stepMulti_of_slot hs (show stepThread ctx _ _ _ ch = .ok (ts, s', [],
        ⟨i, .paired cs[idx].2.partnerIdx, ⟨tr,
          PickRecord.ofPick .l2Arrival os.length sel ++ PickRecord.ofPick .l4Waiter cs.length idx, []⟩⟩) from by
          unfold stepThread
          rw [hi]
          simp only [hb, Bool.false_eq_true, reduceIte, hab, hsp, Bind.bind, Except.bind]
          have ha : arrivalPlan ctx m.shared m.threads i c ch =
              .ok (some (.pair bc cs), chW, PickRecord.ofPick .l2Arrival os.length sel) := by
            unfold arrivalPlan
            rw [hac]
            simp only [Bind.bind, Except.bind]
            rw [hch, hget]
            rfl
          rw [ha]
          cases cs with
          | nil => simp at hidx
          | cons a as =>
              simp only [Bind.bind, Except.bind]
              rw [hW, List.getElem?_eq_getElem hidx]
              simp only [Bind.bind, Except.bind]
              rw [hap]
              rfl)
  | pickCommit hs hi hb hsp hac hget hcom =>
      rename_i i slot c evs cl env k os sel c' s' tr
      have hab : c.abort? = none := by
        cases hab : c.abort? with
        | none => rfl
        | some p =>
            obtain ⟨first, rest⟩ := p
            match c, hab, hac with
            | .panicking (_ :: _) .stop, _, hac => cases hac
      obtain ⟨ch, hch⟩ := consult_realize .l2Arrival (List.getElem?_eq_some_iff.mp hget).1 []
      exact stepMulti_of_slot hs (show stepThread ctx _ _ _ ch = .ok (_, s', [],
        ⟨i, .selectCommit cl, ⟨selectPoll evs ++ tr, PickRecord.ofPick .l2Arrival os.length sel, []⟩⟩) from by
          unfold stepThread
          rw [hi]
          simp only [hb, Bool.false_eq_true, reduceIte, hab, hsp, Bind.bind, Except.bind]
          have ha : arrivalPlan ctx m.shared m.threads i c ch =
              .ok (some (.commit evs cl env k), [], PickRecord.ofPick .l2Arrival os.length sel) := by
            unfold arrivalPlan
            rw [hac]
            simp only [Bind.bind, Except.bind]
            rw [hch, hget]
            rfl
          rw [ha]
          simp only [Bind.bind, Except.bind, hcom]
          rfl)

theorem stepML_erase : stepML_erase_stmt := by
  intro ctx m m' ev h
  obtain ⟨ch, ch', he⟩ := stepML_complete ctx m m' ev h
  exact stepMulti_sound he

theorem stepM_lift : stepM_lift_stmt := by
  intro ctx m m' tr h
  obtain ⟨ch, ch', ev, he, ht⟩ := stepM_complete h
  exact ⟨ev, stepML_sound ctx m m' ch ch' ev he, ht⟩

theorem stepsML_erase : stepsML_erase_stmt := by
  intro ctx m mf evs h
  induction h with
  | refl _ => exact PoolSteps.refl
  | head hs _ ih => exact PoolSteps.head (stepML_erase ctx _ _ _ hs) ih

private theorem stepMulti_at_slot {ctx : ProgramCtx} {m : MultiConfig} {i slot : Nat}
    {ch chI chI' : Choices} {ts : Array Thread} {s' : Store} {evI : StepEvent}
    (hs : SchedSlot ctx m i slot)
    (hr : replays (schedRecord ctx m slot) ch chI)
    (hi : stepThread ctx m.shared m.threads i chI = .ok (ts, s', chI', evI)) :
    stepMulti ctx m ch = .ok (⟨ts, s', i⟩, chI',
      { evI with label := { evI.label with picks := schedRecord ctx m slot ++ evI.picks } }) := by
  unfold SchedSlot at hs
  cases hcur : m.threads[m.cur]? with
  | none => simp [hcur] at hs
  | some t =>
      rw [hcur] at hs
      by_cases hb : t.atBoundary = true
      · simp only [hb, reduceIte] at hs
        have hlt := (List.getElem?_eq_some_iff.mp hs).1
        have hrec : replays (PickRecord.ofPick t.boundarySite
            (schedSlots ctx m.shared m.threads m.cur t.boundarySite).length slot) ch chI := by
          simpa only [schedRecord, hcur, hb, reduceIte] using hr
        have hch := consult_of_replays hlt hrec
        unfold stepMulti
        rw [hcur]
        simp only [hb, reduceIte]
        cases hrs : schedSlots ctx m.shared m.threads m.cur t.boundarySite with
        | nil => simp [hrs] at hs
        | cons a as =>
            rw [hrs] at hch hs
            simp only [hch, hs, Bind.bind, Except.bind]
            unfold stepThreadInto
            rw [hi]
            simp only [schedRecord, hcur, hb, reduceIte, hrs]
            rfl
      · simp only [hb] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have he : chI = ch := by simpa only [schedRecord, hcur, hb, Bool.false_eq_true, reduceIte, replays] using hr
        subst chI
        simp only [stepMulti, hcur, hb, stepThreadInto, hi, schedRecord]
        rfl


set_option linter.unusedSimpArgs false in
private theorem stepML_replay {ctx : ProgramCtx} {m m' : MultiConfig} {ev : StepEvent}
    (h : StepML ctx m m' ev) {other rest : Choices} (hr : replays ev.picks other rest) :
    stepMulti ctx m other = .ok (m', rest, ev) := by
  cases h with
  | strip hs hi =>
      have hsched := hr
      simpa only [StepEvent.picks, List.append_nil] using stepMulti_at_slot hs hsched
        (show stepThread ctx _ _ _ rest = .ok (_, _, rest, ⟨_, .opDoneStrip, ⟨[], [], []⟩⟩) from by
          unfold stepThread; rw [hi]; rfl)
  | abort hs hi hab hp hmsg =>
      rename_i i slot c first chain pick msg
      obtain ⟨mid, hsched, hr⟩ := replays_append.mp hr
      have hch := consult_of_replays hp hr
      exact stepMulti_at_slot hs hsched (show stepThread ctx _ _ _ mid = .ok (_, _, rest,
        ⟨i, .aborted, ⟨[], PickRecord.ofPick .repanicCollapse _ pick, []⟩⟩) from by
          unfold stepThread
          rw [hi]
          simp only [isBlockedConfig_of_abort hab, Bool.false_eq_true, reduceIte, hab, hch,
            hmsg, Bind.bind, Except.bind]
          rfl)
  | spawn hs hi hsp hspawn =>
      rename_i i slot c cv args k parent child s' ch ch' ps tr
      obtain ⟨mid, hsched, hr⟩ := replays_append.mp hr
      have hspawn := spawnStep_replay hspawn hr
      have hb : isBlockedConfig c = false := by
        match c, hsp with
        | .retV _ (.goCalleeK [] _ _), _ => rfl
        | .retV _ (.goArgsK _ _ [] _ _), _ => rfl
      have hab : c.abort? = none := by
        match c, hsp with
        | .retV _ (.goCalleeK [] _ _), _ => rfl
        | .retV _ (.goArgsK _ _ [] _ _), _ => rfl
      exact stepMulti_at_slot hs hsched (show stepThread ctx _ _ _ mid = .ok (_, _, rest,
        ⟨i, .spawned m.threads.size, ⟨.hb (.spawn m.threads.size) :: tr.map (.attributed m.threads.size), ps, []⟩⟩) from by
          unfold stepThread
          rw [hi]
          simp only [hb, Bool.false_eq_true, reduceIte, hab, hsp, Bind.bind, Except.bind, hspawn]
          rfl)
  | thread hs hi hb hsp hac hsel hstep =>
      rename_i i slot c c' s' l
      obtain ⟨mid, hsched, hr⟩ := replays_append.mp hr
      obtain ⟨ch, ch', hfn⟩ := step_complete hstep
      have hfn := replay_coverage ctx _ _ _ _ ch ch' _ hfn mid rest hr
      have hab : c.abort? = none := abort?_none_of_stepE (StepE.lift (n := m.threads.size) hstep)
      exact stepMulti_at_slot hs hsched (show stepThread ctx _ _ _ mid = .ok (_, _, rest, ⟨i, .privateStep, l⟩) from by
        unfold stepThread
        rw [hi]
        simp only [hb, Bool.false_eq_true, reduceIte, hab, hsp, Bind.bind, Except.bind]
        rw [arrivalPlan_of_cellPath hac]
        simp only [Bind.bind, Except.bind, hsel]
        rw [hfn]
        rfl)
  | selectApply hs hi hsel hac happly =>
      rename_i i slot c v clauses default done env k ch ch' c' s' ps cl tr
      obtain ⟨mid, hsched, hr⟩ := replays_append.mp hr
      have happly := applySelect_replay happly hr
      obtain rfl := selectApplyPlan_shape hsel
      exact stepMulti_at_slot hs hsched (show stepThread ctx _ _ _ mid = .ok (_, _, rest,
        ⟨i, selectAction cl, ⟨tr, ps, []⟩⟩) from by
          unfold stepThread
          rw [hi]
          simp only [isBlockedConfig, Config.abort?, spawnPlan, Bool.false_eq_true, reduceIte]
          rw [arrivalPlan_of_cellPath hac]
          simp only [Bind.bind, Except.bind, hsel]
          rw [happly]
          rfl)
  | selectApplyPanic hs hi hsel hac happly =>
      rename_i i slot c v clauses default done env k ch msg
      have hsched := hr
      have happly := applySelect_panic_replay happly rest
      obtain rfl := selectApplyPlan_shape hsel
      simpa only [StepEvent.picks, List.append_nil] using stepMulti_at_slot hs hsched
        (show stepThread ctx _ _ _ rest = .ok (_, _, rest, ⟨i, .selectPass, ⟨[], [], []⟩⟩) from by
          unfold stepThread
          rw [hi]
          simp only [isBlockedConfig, Config.abort?, spawnPlan, Bool.false_eq_true, reduceIte]
          rw [arrivalPlan_of_cellPath hac]
          simp only [Bind.bind, Except.bind, hsel]
          rw [happly]
          rfl)
  | wake hs hi hb hres =>
      have hsched := hr
      simpa only [StepEvent.picks, List.append_nil] using stepMulti_at_slot hs hsched
        (show stepThread ctx _ _ _ rest = .ok (_, _, rest, ⟨_, .woke, ⟨_, [], []⟩⟩) from by
          unfold stepThread; rw [hi]; simp only [hb, reduceIte, hres, Bind.bind, Except.bind]; rfl)

  | pair hs hi hb hsp hac hidx hap =>
      rename_i i slot c bc s' cs idx ts tr
      have hab : c.abort? = none := by
        cases hab : c.abort? with
        | none => rfl
        | some p =>
            obtain ⟨first, rest⟩ := p
            match c, hab, hac with
            | .panicking (_ :: _) .stop, _, hac => cases hac
      obtain ⟨mid, hsched, hr⟩ := replays_append.mp hr
      have hch := consult_of_replays hidx hr
      exact stepMulti_at_slot hs hsched (show stepThread ctx _ _ _ mid = .ok (ts, s', rest,
        ⟨i, .paired cs[idx].2.partnerIdx, ⟨tr, PickRecord.ofPick .l4Waiter cs.length idx, []⟩⟩) from by
          unfold stepThread
          rw [hi]
          simp only [hb, Bool.false_eq_true, reduceIte, hab, hsp, Bind.bind, Except.bind]
          rw [arrivalPlan_of_single hac]
          cases cs with
          | nil => simp at hidx
          | cons a as =>
              simp only [Bind.bind, Except.bind]
              rw [hch, List.getElem?_eq_getElem hidx]
              simp only [Bind.bind, Except.bind]
              rw [hap]
              rfl)
  | pickPair hs hi hb hsp hac hget hidx hap =>
      rename_i i slot c bc s' os sel cs idx ts tr
      have hab : c.abort? = none := by
        cases hab : c.abort? with
        | none => rfl
        | some p =>
            obtain ⟨first, rest⟩ := p
            match c, hab, hac with
            | .panicking (_ :: _) .stop, _, hac => cases hac
      obtain ⟨mid, hsched, hr⟩ := replays_append.mp hr
      obtain ⟨chW, hL, hR⟩ := replays_append.mp hr
      have hW := consult_of_replays hidx hR
      have hch := consult_of_replays (List.getElem?_eq_some_iff.mp hget).1 hL
      exact stepMulti_at_slot hs hsched (show stepThread ctx _ _ _ mid = .ok (ts, s', rest,
        ⟨i, .paired cs[idx].2.partnerIdx, ⟨tr,
          PickRecord.ofPick .l2Arrival os.length sel ++ PickRecord.ofPick .l4Waiter cs.length idx, []⟩⟩) from by
          unfold stepThread
          rw [hi]
          simp only [hb, Bool.false_eq_true, reduceIte, hab, hsp, Bind.bind, Except.bind]
          have ha : arrivalPlan ctx m.shared m.threads i c mid =
              .ok (some (.pair bc cs), chW, PickRecord.ofPick .l2Arrival os.length sel) := by
            unfold arrivalPlan
            rw [hac]
            simp only [Bind.bind, Except.bind]
            rw [hch, hget]
            rfl
          rw [ha]
          cases cs with
          | nil => simp at hidx
          | cons a as =>
              simp only [Bind.bind, Except.bind]
              rw [hW, List.getElem?_eq_getElem hidx]
              simp only [Bind.bind, Except.bind]
              rw [hap]
              rfl)
  | pickCommit hs hi hb hsp hac hget hcom =>
      rename_i i slot c evs cl env k os sel c' s' tr
      have hab : c.abort? = none := by
        cases hab : c.abort? with
        | none => rfl
        | some p =>
            obtain ⟨first, rest⟩ := p
            match c, hab, hac with
            | .panicking (_ :: _) .stop, _, hac => cases hac
      obtain ⟨mid, hsched, hr⟩ := replays_append.mp hr
      have hch := consult_of_replays (List.getElem?_eq_some_iff.mp hget).1 hr
      exact stepMulti_at_slot hs hsched (show stepThread ctx _ _ _ mid = .ok (_, s', rest,
        ⟨i, .selectCommit cl, ⟨selectPoll evs ++ tr, PickRecord.ofPick .l2Arrival os.length sel, []⟩⟩) from by
          unfold stepThread
          rw [hi]
          simp only [hb, Bool.false_eq_true, reduceIte, hab, hsp, Bind.bind, Except.bind]
          have ha : arrivalPlan ctx m.shared m.threads i c mid =
              .ok (some (.commit evs cl env k), rest, PickRecord.ofPick .l2Arrival os.length sel) := by
            unfold arrivalPlan
            rw [hac]
            simp only [Bind.bind, Except.bind]
            rw [hch, hget]
            rfl
          rw [ha]
          simp only [Bind.bind, Except.bind, hcom]
          rfl)

theorem stepMulti_replay : stepMulti_replay_stmt := by
  intro ctx m m' ch ch' ev h other rest hr
  exact stepML_replay (stepML_sound ctx m m' ch ch' ev h) hr

/-! ## M2 — attribution, boundaries, and the pool deadlock -/

private theorem stepML_slot {ctx : ProgramCtx} {m m' : MultiConfig} {ev : StepEvent}
    (h : StepML ctx m m' ev) :
    ∃ slot, SchedSlot ctx m ev.who slot ∧ m'.cur = ev.who ∧
      ∃ tail, ev.picks = schedRecord ctx m slot ++ tail := by
  cases h <;> first
    | exact ⟨_, ‹SchedSlot _ _ _ _›, rfl, _, rfl⟩
    | exact ⟨_, ‹SchedSlot _ _ _ _›, rfl, [], (List.append_nil _).symm⟩

theorem stepML_sched : stepML_sched_stmt := by
  intro ctx m m' ev h
  obtain ⟨slot, hs, hc, _⟩ := stepML_slot h
  exact ⟨(schedSlot_iff ctx m ev.who).mpr ⟨slot, hs⟩, hc⟩

theorem stepML_who_runnable : stepML_who_runnable_stmt := by
  intro ctx m m' ev h
  exact schedPick_le_fine (stepML_sched ctx m m' ev h).1

theorem stepML_switch_boundary : stepML_switch_boundary_stmt := by
  intro ctx m m' ev h hne
  have hs := (stepML_sched ctx m m' ev h).1
  unfold schedPick at hs
  cases ht : m.threads[m.cur]? with
  | none => simp [ht] at hs
  | some t =>
    rw [ht] at hs
    by_cases hb : t.atBoundary = true
    · exact ⟨t, rfl, hb⟩
    · simp [hb] at hs
      exact (hne hs).elim

theorem stepML_sched_record : stepML_sched_record_stmt := by
  intro ctx m m' ev site menu h hm hn
  obtain ⟨slot, hs, _, tail, hp⟩ := stepML_slot h
  unfold MultiConfig.schedMenu? at hm
  cases ht : m.threads[m.cur]? with
  | none => simp [ht] at hm
  | some t =>
    rw [ht] at hm
    dsimp only at hm
    by_cases hb : t.atBoundary = true
    · simp only [if_pos hb, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      refine ⟨slot, ?_, ?_⟩
      · simpa [SchedSlot, ht, hb] using hs
      · rw [hp]
        simp [schedRecord, ht, hb, PickRecord.ofPick, Nat.not_le.mpr hn]
    · simp [hb] at hm

theorem asleep_silent : asleep_silent_stmt := by
  intro ctx m hn m' ev h
  have hw := stepML_who_runnable ctx m m' ev h
  simp [hn] at hw

theorem mainOutcome_not_deadlock : mainOutcome_not_deadlock_stmt := by
  intro ctx m s hm hd
  have := hd.2.2.1
  simp [hm] at this

theorem singleton_deadlock : singleton_deadlock_stmt := by
  intro ctx s c hb
  rcases hb with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ |
    ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
    simp [PoolDeadlock, MultiConfig.panicMsg?, MultiConfig.mainOutcome?,
      runnableIdxs, threadRunnable, Config.isTerminal, isBlockedConfig]

set_option linter.unusedSimpArgs false in
theorem stepML_frame : stepML_frame_stmt := by
  intro ctx m m' ev h
  cases h
  all_goals try obtain ⟨ti, tj, rfl⟩ :=
    PoolStructure.applyPairing_shape ‹applyPairing _ _ _ _ _ _ = _›
  all_goals refine ⟨by simp, ?_⟩
  all_goals intro j hj hne
  all_goals apply Classical.byContradiction
  all_goals intro hn
  all_goals simp only [not_or] at hn
  all_goals obtain ⟨hf, hp⟩ := hn
  all_goals apply hf
  all_goals simp_all [Array.getElem?_push, Array.getElem?_setIfInBounds,
    Ne.symm hne, Nat.ne_of_lt hj]

set_option linter.unusedSimpArgs false in
theorem stepML_paired_trace : stepML_paired_trace_stmt := by
  intro ctx m m' ev j h hj
  cases h <;> simp only [StepEvent.action, StepAction.noConfusion, selectAction] at hj
  all_goals first
    | contradiction
    | (cases hj
       exact PoolStructure.applyPairing_trace ‹applyPairing _ _ _ _ _ _ = _›)
    | (split at hj <;> cases hj)

set_option linter.unusedSimpArgs false in
theorem stepML_spawn : stepML_spawn_stmt := by
  intro ctx m m' ev h
  cases h
  all_goals try obtain ⟨ti, tj, rfl⟩ :=
    PoolStructure.applyPairing_shape ‹applyPairing _ _ _ _ _ _ = _›
  all_goals simp [selectAction, StepEvent.trace]
  all_goals intro n; split <;> simp

theorem stepMulti_deadlock_elim : stepMulti_deadlock_elim_stmt := by
  intro ctx m ch ch₁ rec hc h
  have hr : runnableIdxs ctx m.shared m.threads ≠ [] := by cases hc <;> assumption
  unfold stepMulti at h
  cases hcur : m.threads[m.cur]? with
  | none => rw [hcur] at h; cases h
  | some t =>
    rw [hcur] at h
    by_cases hb : t.atBoundary = true
    · simp only [hb, reduceIte] at h
      cases hrs : schedSlots ctx m.shared m.threads m.cur t.boundarySite with
      | nil =>
        obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hr
        have hm := mem_schedSlots_of_runnable (cur := m.cur) (site := t.boundarySite) hi
        simp [hrs] at hm
      | cons r0 rest =>
        rw [hrs] at h
        dsimp only at h
        rcases hcons : Choices.consumeAtE t.boundarySite (r0 :: rest).length ch₁
          with ⟨pick, ch₂, ps⟩
        rw [hcons] at h
        cases hget : (r0 :: rest)[pick]? with
        | none => rw [hget] at h; cases h
        | some i =>
          rw [hget] at h
          have hm : i ∈ runnableIdxs ctx m.shared m.threads := by
            apply schedSlots_mem hcur
            rw [hrs]
            exact List.mem_of_getElem? hget
          have he := stepThreadInto_strict (ch := ch₂) (schedPick_of_boundary hcur hb hm)
          exact ErrP.bind he (fun _ => ErrP.pure) _ h
    · simp only [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, reduceIte] at h
      exact stepThreadInto_strict (schedPick_cur hcur hb) _ h

end GoLean.GoCore.PoolSound
