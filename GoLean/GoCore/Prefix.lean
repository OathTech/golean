import GoLean.GoCore.ExecutionStatement
import GoLean.GoCore.PrefixFacts
import GoLean.GoCore.StepErrors

/-!
# The execution bridges — PROOFS of packet A's statements (window charter row 2b)

[AGENT packet B worker] 2026-09-28, under the window charter (rev. 2) and the execution-model
ruling of 2026-09-27; brief `docs/codex-briefs/2026-09-24_packet-B-bridges.md`, refreshed by the
[AGENT] coordinator (input: `core/step-label-0928` @ `61bdc65d`). Every `<name>_stmt` of
`ExecutionStatement.lean` is discharged here as `theorem <name> : <name>_stmt`, the statement
UNCHANGED. Handoff: `docs/2026-09-28_packet-b-handoff.md`.
-/

namespace GoLean.GoCore.ExecutionStatement

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Semantics

/-! ## Small facts about the zero-cost forms -/

/-- `stepFn` never succeeds at a zero-cost configuration (it refuses at `.next .stop`
and raises the deadlock at the four blocked forms). -/
theorem stepFn_zeroCost_not_ok {ctx : ProgramCtx} {s : Store} {c : Config} {ch : Choices}
    {c' : Config} {s' : Store} {ch' : Choices} {l : StepLabel}
    (h : stepFn ctx s c ch = .ok (c', s', ch', l)) : ¬ ZeroCost c := by
  rintro (rfl | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) <;>
    simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h

/-- The zero-cost classification is decidable by shape. -/
theorem zeroCost_cases (c : Config) :
    c = .next .stop ∨ Blocked c ∨ ¬ ZeroCost c := by
  unfold ZeroCost Blocked
  cases c with
  | next k => cases k <;> simp
  | blockedSend ch v k => exact .inr (.inl (.inl ⟨_, _, _, rfl⟩))
  | blockedRecv ch t e env k => exact .inr (.inl (.inr (.inl ⟨_, _, _, _, _, rfl⟩)))
  | blockedSelect cl env k => exact .inr (.inl (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))
  | blockedSync op loc env k => exact .inr (.inl (.inr (.inr (.inr ⟨_, _, _, _, rfl⟩))))
  | _ => simp

/-- `execStmtLoop` at a non-zero-cost configuration: fuel-out at 0, one `stepFn` call
then the loop at `fuel + 1`. -/
theorem execStmtLoop_nonZero {ctx : ProgramCtx} {fuel : Nat} {s : Store} {c : Config}
    {ch : Choices} (hz : ¬ ZeroCost c) :
    execStmtLoop ctx fuel s c ch =
      (match fuel with
       | 0 => .error .fuelOut
       | f + 1 => (stepFn ctx s c ch).bind fun r => execStmtLoop ctx f r.2.1 r.1 r.2.2.1) := by
  rw [execStmtLoop_unfold]
  unfold ZeroCost Blocked at hz
  split
  · exact absurd (.inl rfl) hz
  · exact absurd (.inr (.inl ⟨_, _, _, rfl⟩)) hz
  · exact absurd (.inr (.inr (.inl ⟨_, _, _, _, _, rfl⟩))) hz
  · exact absurd (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) hz
  · exact absurd (.inr (.inr (.inr (.inr ⟨_, _, _, _, rfl⟩)))) hz
  · cases fuel with
    | zero => rfl
    | succ f =>
      simp only [Bind.bind]

/-- `execStmtLoop` at a blocked configuration is the deadlock at every fuel. -/
theorem execStmtLoop_blocked {ctx : ProgramCtx} {fuel : Nat} {s : Store} {c : Config}
    {ch : Choices} (hb : Blocked c) : execStmtLoop ctx fuel s c ch = .error (.terminal .deadlock) := by
  rcases hb with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
    (rw [execStmtLoop_unfold]; rfl)

/-! ## The `Prefix` algebra (deliverable 2) -/

theorem prefix_refl : prefix_refl_stmt := fun _ _ _ _ => .done

theorem prefix_comp : prefix_comp_stmt := by
  intro ctx n m s s₁ sf c c₁ cf ch ch₁ chf ls ls' h₁ h₂
  induction h₁ with
  | done => simpa using h₂
  | step hs _ ih =>
    rw [Nat.add_right_comm]
    exact .step hs (ih h₂)

theorem prefix_split : prefix_split_stmt := by
  intro ctx n m
  induction n with
  | zero =>
    intro s sf c cf ch chf ls h
    exact ⟨[], ls, s, c, ch, rfl, .done, by simpa using h⟩
  | succ n ih =>
    intro s sf c cf ch chf ls h
    rw [Nat.add_right_comm] at h
    cases h with
    | step hs hp =>
      obtain ⟨ls₁, ls₂, s₁, c₁, ch₁, rfl, h₁, h₂⟩ := ih _ _ _ _ _ _ _ hp
      exact ⟨_ :: ls₁, ls₂, s₁, c₁, ch₁, rfl, .step hs h₁, h₂⟩

theorem prefix_erase_trace : prefix_erase_trace_stmt := by
  intro ctx n s sf c cf ch chf ls h
  induction h with
  | done => exact .done
  | step hs _ ih => exact .step hs ih

theorem prefix_erase_steps : prefix_erase_steps_stmt := fun ctx n s sf c cf ch chf ls h =>
  (prefix_erase_trace ctx n s sf c cf ch chf ls h).erase

/-- A counted `Trace` carries its labels: the reverse erasure. -/
theorem prefix_of_trace {ctx : ProgramCtx} {n : Nat} {s sf : Store} {c cf : Config}
    {ch chf : Choices} (h : Trace ctx n s c ch sf cf chf) :
    ∃ ls, Prefix ctx n s c ch ls sf cf chf := by
  induction h with
  | done => exact ⟨[], .done⟩
  | step hs _ ih =>
    obtain ⟨ls, hp⟩ := ih
    exact ⟨_, .step hs hp⟩

theorem prefix_iter : prefix_iter_stmt := by
  intro ctx n s sf c cf ch chf
  rw [iter_iff_trace]
  exact ⟨prefix_of_trace, fun ⟨ls, hp⟩ => prefix_erase_trace ctx n s sf c cf ch chf ls hp⟩

/-- The loop runs a prefix exactly: `n` steps of fuel carry the loop to the prefix's
endpoint (every configuration a prefix passes THROUGH is non-zero-cost, since `stepFn`
succeeds there). -/
theorem Prefix.run_eq {ctx : ProgramCtx} {n fuel : Nat} {s sf : Store} {c cf : Config}
    {ch chf : Choices} {ls : List StepLabel} (h : Prefix ctx n s c ch ls sf cf chf) :
    execStmtLoop ctx (n + fuel) s c ch = execStmtLoop ctx fuel sf cf chf := by
  induction h with
  | done => simp
  | step hs _ ih =>
    rw [Nat.add_right_comm, execStmtLoop_step hs]
    exact ih

/-! ## The abort arm of `stepFn` (deliverable 3) -/

theorem abort?_some {c : Config} {first : PanicEntry} {rest : List PanicEntry}
    (h : c.abort? = some (first, rest)) : c = .panicking (first :: rest) .stop := by
  unfold Config.abort? at h
  split at h
  · cases h; rfl
  · cases h

/-- `stepFn` at an abort: the consult, then the renderer; a render is the panic terminal,
a renderer error is passed through. -/
theorem stepFn_abort {ctx : ProgramCtx} {s : Store} {first : PanicEntry}
    {rest : List PanicEntry} {ch : Choices} :
    stepFn ctx s (.panicking (first :: rest) .stop) ch =
      (match abortMsg ctx first rest
          (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1 with
       | .ok t => .error (.terminal (.panic t))
       | .error e => .error e) := by
  have hp : (abortConsult first rest ch).1
      = (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1 := by
    rw [abortConsult, ← Choices.consumeAtE_fst_snd]
  simp only [stepFn, hp]
  cases abortMsg ctx first rest
      (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch).1 <;> rfl

/-- The renderer's only error is a refusal. -/
theorem abortMsg_error {ctx : ProgramCtx} {first : PanicEntry} {rest : List PanicEntry}
    {pick : Nat} {e : Stop} (h : abortMsg ctx first rest pick = .error e) :
    ∃ r, e = .refusal r := by
  unfold abortMsg at h
  split at h
  · cases h
  · simp only [throw, throwThe, MonadExceptOf.throw, Except.error.injEq] at h
    exact ⟨_, h.symm⟩

theorem finish_refused_step : finish_refused_step_stmt := by
  intro ctx s c ch first rest r hab
  have hc := abort?_some hab
  subst hc
  rw [stepFn_abort]
  constructor
  · rintro ⟨rec, ch'', hf⟩
    cases hf with
    | abortRefused hab' hcon hmsg =>
      simp only [Config.abort?, Option.some.injEq, Prod.mk.injEq] at hab'
      obtain ⟨rfl, rfl⟩ := hab'
      rw [hcon]
      simp only [hmsg]
  · intro h
    rcases hx : Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch with
      ⟨p, ch'', rec⟩
    rw [hx] at h
    simp only at h
    split at h
    · cases h
    · rename_i e he
      cases h
      exact ⟨rec, ch'', .abortRefused rfl hx he⟩

/-- Where the `aborted` finish's `stepFn` side comes from: the abort configuration's panic
terminal. -/
theorem finish_aborted_stepFn {ctx : ProgramCtx} {s : Store} {c : Config} {ch : Choices}
    {rec : List PickRecord} {t : String} {s' : Store} {ch'' : Choices} {cost : Nat}
    (h : Finish ctx s c ch rec (.aborted t s' ch'') cost) :
    cost = 1 ∧ s' = s ∧ c.abort?.isSome ∧ stepFn ctx s c ch = .error (.terminal (.panic t)) := by
  cases h with
  | aborted hab hcon hmsg =>
    have hc := abort?_some hab
    subst hc
    refine ⟨rfl, rfl, by simp [Config.abort?], ?_⟩
    rw [stepFn_abort, hcon]
    simp only [hmsg]

/-- The `aborted` finish from the executable's panic terminal at an abort configuration. -/
theorem finish_aborted_of_stepFn {ctx : ProgramCtx} {s : Store} {c : Config} {ch : Choices}
    {first : PanicEntry} {rest : List PanicEntry} {t : String}
    (hab : c.abort? = some (first, rest)) (h : stepFn ctx s c ch = .error (.terminal (.panic t))) :
    ∃ rec ch'', Finish ctx s c ch rec (.aborted t s ch'') 1 := by
  have hc := abort?_some hab
  subst hc
  rw [stepFn_abort] at h
  rcases hx : Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch with
    ⟨p, ch'', rec⟩
  rw [hx] at h
  simp only at h
  split at h
  · rename_i t' ht
    simp only [Except.error.injEq, Stop.terminal.injEq, Terminal.panic.injEq] at h
    subst h
    exact ⟨rec, ch'', .aborted rfl hx ht⟩
  · rename_i e he
    obtain ⟨r, rfl⟩ := abortMsg_error he
    cases h

theorem abortLeftover_eq {ctx : ProgramCtx} {s : Store} {c : Config} {ch : Choices}
    {rec : List PickRecord} {t : String} {ch'' : Choices}
    (h : Finish ctx s c ch rec (.aborted t s ch'') 1) : abortLeftover c ch = ch'' := by
  cases h with
  | aborted hab hcon _ =>
    simp only [abortLeftover, hab, abortConsult]
    rw [← Choices.consumeAtE_fst_snd, hcon]

theorem abortLeftover_eq_refused {ctx : ProgramCtx} {s : Store} {c : Config} {ch : Choices}
    {rec : List PickRecord} {r : Refusal} {ch'' : Choices}
    (h : Finish ctx s c ch rec (.refused r s ch'') 1) : abortLeftover c ch = ch'' := by
  cases h with
  | abortRefused hab hcon _ =>
    simp only [abortLeftover, hab, abortConsult]
    rw [← Choices.consumeAtE_fst_snd, hcon]

/-- Two tapes whose `repanicCollapse` consults emit the SAME records draw the same pick. -/
theorem consumeAtE_pick_of_records {site : ChoiceSite} {b : Nat} {ch ch₂ : Choices}
    (h : (Choices.consumeAtE site b ch).2.2 = (Choices.consumeAtE site b ch₂).2.2) :
    (Choices.consumeAtE site b ch).1 = (Choices.consumeAtE site b ch₂).1 := by
  by_cases hb : b ≤ 1
  · rw [Choices.consumeAtE_le_one hb, Choices.consumeAtE_le_one hb]
  · rw [Choices.consumeAtE_of_lt (by omega), Choices.consumeAtE_of_lt (by omega)] at h ⊢
    simp only [List.cons.injEq, PickRecord.mk.injEq] at h
    exact h.1.2.2

theorem finish_replay : finish_replay_stmt := by
  intro ctx s c ch ch₂ first rest rec hab hrec
  constructor
  · intro t ch'' hf
    cases hf with
    | aborted hab' hcon hmsg =>
      rw [hab] at hab'
      simp only [Option.some.injEq, Prod.mk.injEq] at hab'
      obtain ⟨rfl, rfl⟩ := hab'
      have hp := consumeAtE_pick_of_records (ch := ch) (ch₂ := ch₂) (by rw [hcon, hrec])
      rw [hcon] at hp
      simp only at hp
      refine .aborted (pick := (Choices.consumeAtE .repanicCollapse
        (repanicCollapseWidth first rest) ch₂).1) hab (by rw [← hrec]) ?_
      rw [← hp]; exact hmsg
  · intro r ch'' hf
    cases hf with
    | abortRefused hab' hcon hmsg =>
      rw [hab] at hab'
      simp only [Option.some.injEq, Prod.mk.injEq] at hab'
      obtain ⟨rfl, rfl⟩ := hab'
      have hp := consumeAtE_pick_of_records (ch := ch) (ch₂ := ch₂) (by rw [hcon, hrec])
      rw [hcon] at hp
      simp only at hp
      refine .abortRefused (pick := (Choices.consumeAtE .repanicCollapse
        (repanicCollapseWidth first rest) ch₂).1) hab (by rw [← hrec]) ?_
      rw [← hp]; exact hmsg

/-! ## The boundary controls, as theorems (deliverable 4's controls, general form) -/

theorem boundary_abort_one : boundary_abort_one_stmt := by
  intro ctx s c ch first rest t hab hmsg
  have hc := abort?_some hab
  subst hc
  rw [execStmtLoop_nonZero (by simp [ZeroCost, Blocked])]
  simp only [stepFn_abort, hmsg, Except.bind]

theorem boundary_blocked_zero : boundary_blocked_zero_stmt := fun _ _ _ _ hb =>
  execStmtLoop_blocked hb

theorem boundary_refused_one : boundary_refused_one_stmt := by
  intro ctx s c ch first rest r hab hmsg
  have hc := abort?_some hab
  subst hc
  rw [execStmtLoop_nonZero (by simp [ZeroCost, Blocked])]
  simp only [stepFn_abort, hmsg, Except.bind]

theorem boundary_refused_zero : boundary_refused_zero_stmt := by
  intro ctx s c ch first rest r hab _
  have hc := abort?_some hab
  subst hc
  rw [execStmtLoop_nonZero (by simp [ZeroCost, Blocked])]

/-! ## Replay coverage (deliverable 5) — premise-free -/

/-- **Consultation coverage, by record**: the answer to the reshape lane's flag. The
`appendTargetLocal` premise is NOT needed: the premise-free consumption theorem
(`stepFn_consumption_some'`) and the record sweeps (`stepFn_picks_none`/`_some`) close it for
every configuration. -/
theorem replay_coverage : replay_coverage_stmt := by
  intro ctx s s' c c' ch ch' l h ch₂ ch₂' hr
  cases hsc : seqConsumption ctx s c with
  | none =>
    have hp : l.picks = [] := stepFn_picks_none (ch₀ := ch) hsc _ h
    obtain ⟨-, hall⟩ := stepFn_consumption_none hsc h
    rw [hp] at hr
    simp only [replays] at hr
    rw [hr]
    exact hall ch₂
  | some p =>
    obtain ⟨site, b⟩ := p
    have hp : l.picks = PickRecord.ofPick site b (Choices.consumeAt site b ch).1 :=
      stepFn_picks_some (ch₀ := ch) hsc _ h
    obtain ⟨-, hall⟩ := stepFn_consumption_some' hsc h
    by_cases hb : b ≤ 1
    · rw [hp, PickRecord.ofPick, if_pos hb] at hr
      simp only [replays] at hr
      rw [hr]
      have h₂ := hall ch₂ (by rw [Choices.consumeAt_le_one hb, Choices.consumeAt_le_one hb])
      rwa [Choices.consumeAt_le_one hb] at h₂
    · rw [hp, PickRecord.ofPick, if_neg hb] at hr
      simp only [replays] at hr
      obtain ⟨mid, hmid, hmid'⟩ := hr
      rw [hmid']
      have hc : Choices.consumeAt site b ch₂ = ((Choices.consumeAt site b ch).1, mid) := by
        rw [← Choices.consumeAtE_fst_snd, hmid]
      have h₂ := hall ch₂ (by rw [hc])
      rwa [hc] at h₂

/-! ## What `stepFn` raises, per configuration class -/

theorem blockedB_of_not_zeroCost {c : Config} (hz : ¬ ZeroCost c) : c.blockedB = false := by
  cases c <;> simp_all [Config.blockedB, ZeroCost, Blocked]

/-- The error of a `stepFn` call at a non-zero-cost configuration: at an abort, the panic
terminal or the renderer's refusal; everywhere else a refusal or `fatal` — **no stray
panic** (audit F1, machine-checked: `stepFn_strict`), no deadlock, no race, no fuel-out. -/
theorem stepFn_error_cases {ctx : ProgramCtx} {s : Store} {c : Config} {ch : Choices} {e : Stop}
    (hz : ¬ ZeroCost c) (h : stepFn ctx s c ch = .error e) :
    (c.abort?.isSome ∧ ((∃ t, e = .terminal (.panic t)) ∨ ∃ r, e = .refusal r)) ∨
    (c.abort? = none ∧ ((∃ r, e = .refusal r) ∨ ∃ m, e = .terminal (.fatal m))) := by
  cases hab : c.abort? with
  | some p =>
    obtain ⟨first, rest⟩ := p
    left
    refine ⟨rfl, ?_⟩
    have hc := abort?_some hab
    subst hc
    rw [stepFn_abort] at h
    split at h
    · cases h; exact .inl ⟨_, rfl⟩
    · rename_i e' he'
      cases h
      exact .inr (abortMsg_error he')
  | none =>
    right
    refine ⟨rfl, ?_⟩
    have hs := stepFn_strict (ctx := ctx) (σ := s) (ch := ch) hab (blockedB_of_not_zeroCost hz) e h
    rcases e with (_ | _ | _) | (_ | _ | _ | _) | _ <;>
      first | exact .inl ⟨_, rfl⟩ | exact .inr ⟨_, rfl⟩ | exact hs.elim

/-- **No stray panic** (the coordinator's first lemma): away from an abort, `stepFn` never
raises the Go panic terminal. -/
theorem stepFn_no_stray_panic {ctx : ProgramCtx} {s : Store} {c : Config} {ch : Choices}
    {t : String} (hab : c.abort? = none) : stepFn ctx s c ch ≠ .error (.terminal (.panic t)) := by
  intro h
  rcases zeroCost_cases c with rfl | hb | hz
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · rcases hb with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
      simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · rcases stepFn_error_cases hz h with ⟨hs, _⟩ | ⟨_, ⟨r, hr⟩ | ⟨m, hm⟩⟩
    · rw [hab] at hs; cases hs
    · cases hr
    · cases hm

theorem finish_abort_step : finish_abort_step_stmt := by
  intro ctx s c ch t
  constructor
  · rintro ⟨rec, ch'', hf⟩
    exact (finish_aborted_stepFn hf).2.2.2
  · intro h
    cases hab : c.abort? with
    | none => exact absurd h (stepFn_no_stray_panic hab)
    | some p => exact finish_aborted_of_stepFn hab h

/-! ## The fuel bridges (deliverable 4) -/

/-- Every error of the loop, located: the prefix to its endpoint and what happened there. -/
theorem execStmtLoop_error {ctx : ProgramCtx} :
    ∀ {fuel : Nat} {s : Store} {c : Config} {ch : Choices} {e : Stop},
      execStmtLoop ctx fuel s c ch = .error e →
      ∃ n ls sf cf chf, Prefix ctx n s c ch ls sf cf chf ∧ n ≤ fuel ∧
        ((Blocked cf ∧ e = .terminal .deadlock) ∨
         (n = fuel ∧ ¬ ZeroCost cf ∧ e = .fuelOut) ∨
         (n + 1 ≤ fuel ∧ ¬ ZeroCost cf ∧ stepFn ctx sf cf chf = .error e)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s c ch e h
    rcases zeroCost_cases c with rfl | hb | hz
    · rw [execStmtLoop_unfold] at h; cases h
    · rw [execStmtLoop_blocked hb] at h; cases h
      exact ⟨0, [], s, c, ch, .done, Nat.le_refl _, .inl ⟨hb, rfl⟩⟩
    · rw [execStmtLoop_nonZero hz] at h; cases h
      exact ⟨0, [], s, c, ch, .done, Nat.le_refl _, .inr (.inl ⟨rfl, hz, rfl⟩)⟩
  | succ f ih =>
    intro s c ch e h
    rcases zeroCost_cases c with rfl | hb | hz
    · rw [execStmtLoop_unfold] at h; cases h
    · rw [execStmtLoop_blocked hb] at h; cases h
      exact ⟨0, [], s, c, ch, .done, Nat.zero_le _, .inl ⟨hb, rfl⟩⟩
    · rw [execStmtLoop_nonZero hz] at h
      simp only at h
      cases hs : stepFn ctx s c ch with
      | error e' =>
        rw [hs] at h; cases h
        exact ⟨0, [], s, c, ch, .done, Nat.zero_le _, .inr (.inr ⟨by omega, hz, hs⟩)⟩
      | ok r =>
        obtain ⟨c₁, s₁, ch₁, l⟩ := r
        rw [hs] at h
        obtain ⟨n, ls, sf, cf, chf, hp, hn, hcase⟩ := ih h
        refine ⟨n + 1, l :: ls, sf, cf, chf, .step hs hp, by omega, ?_⟩
        rcases hcase with hc | ⟨rfl, hc⟩ | ⟨hn', hc⟩
        · exact .inl hc
        · exact .inr (.inl ⟨rfl, hc⟩)
        · exact .inr (.inr ⟨by omega, hc⟩)

/-- The loop past a prefix. -/
theorem Prefix.run_le {ctx : ProgramCtx} {n fuel : Nat} {s sf : Store} {c cf : Config}
    {ch chf : Choices} {ls : List StepLabel} (h : Prefix ctx n s c ch ls sf cf chf)
    (hn : n ≤ fuel) :
    execStmtLoop ctx fuel s c ch = execStmtLoop ctx (fuel - n) sf cf chf := by
  have := h.run_eq (fuel := fuel - n)
  rwa [show n + (fuel - n) = fuel by omega] at this

theorem run_ok_iff : run_ok_iff_stmt := by
  intro ctx fuel s sf c ch chf
  rw [GoLean.Semantics.run_ok_iff]
  constructor
  · rintro ⟨n, hn, ht⟩
    exact ⟨n, hn, prefix_of_trace ht⟩
  · rintro ⟨n, hn, ls, hp⟩
    exact ⟨n, hn, prefix_erase_trace ctx n s sf c _ ch chf ls hp⟩

theorem run_panic_iff : run_panic_iff_stmt := by
  intro ctx fuel s c ch t
  constructor
  · intro h
    obtain ⟨n, ls, sf, cf, chf, hp, hn, hcase⟩ := execStmtLoop_error h
    rcases hcase with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨hn', hz, hs⟩
    · cases he
    · cases he
    · cases hab : cf.abort? with
      | none => exact absurd hs (stepFn_no_stray_panic hab)
      | some p =>
        obtain ⟨rec, ch'', hf⟩ := finish_aborted_of_stepFn hab hs
        exact ⟨n, ls, sf, cf, chf, ch'', rec, hn', hp, hf⟩
  · rintro ⟨n, ls, sf, cf, chf, ch'', rec, hn, hp, hf⟩
    obtain ⟨-, -, hab, hs⟩ := finish_aborted_stepFn hf
    rw [hp.run_le (by omega)]
    have hz : ¬ ZeroCost cf := by
      obtain ⟨p, hp'⟩ := Option.isSome_iff_exists.mp hab
      rw [abort?_some hp']; simp [ZeroCost, Blocked]
    rw [execStmtLoop_nonZero hz]
    obtain ⟨k, hk⟩ : ∃ k, fuel - n = k + 1 := ⟨fuel - n - 1, by omega⟩
    rw [hk]
    simp only [hs, Except.bind]

theorem run_deadlock_iff : run_deadlock_iff_stmt := by
  intro ctx fuel s c ch
  constructor
  · intro h
    obtain ⟨n, ls, sf, cf, chf, hp, hn, hcase⟩ := execStmtLoop_error h
    rcases hcase with ⟨hb, _⟩ | ⟨_, _, he⟩ | ⟨_, hz, hs⟩
    · exact ⟨n, hn, ls, sf, cf, chf, hp, .blocked hb⟩
    · cases he
    · rcases stepFn_error_cases hz hs with ⟨_, ⟨_, he⟩ | ⟨_, he⟩⟩ | ⟨_, ⟨_, he⟩ | ⟨_, he⟩⟩ <;>
        cases he
  · rintro ⟨n, hn, ls, sf, cf, chf, hp, hf⟩
    cases hf with
    | blocked hb => rw [hp.run_le hn]; exact execStmtLoop_blocked hb

theorem run_fuelOut_iff : run_fuelOut_iff_stmt := by
  intro ctx fuel s c ch
  constructor
  · intro h
    obtain ⟨n, ls, sf, cf, chf, hp, hn, hcase⟩ := execStmtLoop_error h
    rcases hcase with ⟨_, he⟩ | ⟨rfl, hz, _⟩ | ⟨_, hz, hs⟩
    · cases he
    · exact ⟨ls, sf, cf, chf, hp, hz⟩
    · rcases stepFn_error_cases hz hs with ⟨_, ⟨_, he⟩ | ⟨_, he⟩⟩ | ⟨_, ⟨_, he⟩ | ⟨_, he⟩⟩ <;>
        cases he
  · rintro ⟨ls, sf, cf, chf, hp, hz⟩
    rw [hp.run_le (Nat.le_refl _), Nat.sub_self, execStmtLoop_nonZero hz]

/-! ## The classification (deliverable 6) -/

/-- The classification, with the refusal case's endpoint known to be non-zero-cost. -/
theorem classification_strong (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config)
    (ch : Choices) :
    ClassOk ctx fuel s c ch ∨ ClassTerminal ctx fuel s c ch ∨ ClassFuelOut ctx fuel s c ch ∨
      ∃ r, execStmtLoop ctx fuel s c ch = .error (.refusal r) ∧
        ∃ (n : Nat) (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
          n + 1 ≤ fuel ∧ Prefix ctx n s c ch ls sf cf chf ∧ ¬ ZeroCost cf ∧
            stepFn ctx sf cf chf = .error (.refusal r) := by
  cases hr : execStmtLoop ctx fuel s c ch with
  | ok p =>
    obtain ⟨sf, chf⟩ := p
    exact .inl ⟨sf, chf, hr, (run_ok_iff ctx fuel s sf c ch chf).mp hr⟩
  | error e =>
    obtain ⟨n, ls, sf, cf, chf, hp, hn, hcase⟩ := execStmtLoop_error hr
    rcases hcase with ⟨hb, rfl⟩ | ⟨rfl, hz, rfl⟩ | ⟨hn', hz, hs⟩
    · exact .inr (.inl ⟨.deadlock, hr, n, ls, sf, cf, chf, [], .deadlock sf chf, 0,
        by omega, hp, .blocked hb, rfl⟩)
    · exact .inr (.inr (.inl ⟨hr, ls, sf, cf, chf, hp, hz⟩))
    · rcases stepFn_error_cases hz hs with ⟨hab, ⟨t, rfl⟩ | ⟨r, rfl⟩⟩ | ⟨_, ⟨r, rfl⟩ | ⟨m, rfl⟩⟩
      · obtain ⟨p, hp'⟩ := Option.isSome_iff_exists.mp hab
        obtain ⟨rec, ch'', hf⟩ := finish_aborted_of_stepFn hp' hs
        exact .inr (.inl ⟨.panic t, hr, n, ls, sf, cf, chf, rec, _, 1, hn', hp, hf, rfl⟩)
      · exact .inr (.inr (.inr ⟨r, rfl, n, ls, sf, cf, chf, hn', hp, hz, hs⟩))
      · exact .inr (.inr (.inr ⟨r, rfl, n, ls, sf, cf, chf, hn', hp, hz, hs⟩))
      · exact .inr (.inl ⟨.fatal m, hr, n, ls, sf, cf, chf, [], .fatal m sf chf, 1, hn', hp,
          .fatal hs, rfl⟩)

theorem classification : classification_stmt := by
  intro ctx fuel s c ch
  rcases classification_strong ctx fuel s c ch with h | h | h | ⟨r, hr, n, ls, sf, cf, chf, hn, hp, _, hs⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr ⟨r, hr, n, ls, sf, cf, chf, hn, hp, .inl hs⟩))

/-- Under the domain premises the refusal case is empty. (`StateWf` is not needed: the
refusal-freedom premise alone excludes the fourth case.) -/
theorem classification_wf : classification_wf_stmt := by
  intro ctx fuel s c ch _ hnr
  rcases classification_strong ctx fuel s c ch with h | h | h | ⟨r, _, n, ls, sf, cf, chf, _, hp, hz, hs⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)
  · exact absurd hs ((hnr n ch ls sf cf chf hp).1 hz r)

/-- Every successful step is taken under a tape whose residual is ANY given tape: the step's
consultation (if it pops) is replayed by prefixing its pick. -/
theorem stepFn_any_residual {ctx : ProgramCtx} {s s' : Store} {c c' : Config} {ch₀ ch₀' : Choices}
    {l : StepLabel} (h : stepFn ctx s c ch₀ = .ok (c', s', ch₀', l)) (ch : Choices) :
    ∃ ch₁, stepFn ctx s c ch₁ = .ok (c', s', ch, l) := by
  cases hsc : seqConsumption ctx s c with
  | none => exact ⟨ch, (stepFn_consumption_none hsc h).2 ch⟩
  | some p =>
    obtain ⟨site, b⟩ := p
    obtain ⟨-, hall⟩ := stepFn_consumption_some' hsc h
    by_cases hb : b ≤ 1
    · refine ⟨ch, ?_⟩
      have h₂ := hall ch (by rw [Choices.consumeAt_le_one hb, Choices.consumeAt_le_one hb])
      rwa [Choices.consumeAt_le_one hb] at h₂
    · have hlt : (Choices.consumeAt site b ch₀).1 < b := Choices.consumeAt_fst_lt (by omega)
      have hc : Choices.consumeAt site b ((Choices.consumeAt site b ch₀).1 :: ch)
          = ((Choices.consumeAt site b ch₀).1, ch) := by
        rw [Choices.consumeAt_of_lt (by omega)]
        simp only [Choices.consume, show max 1 b = b by omega, Nat.mod_eq_of_lt hlt]
      refine ⟨(Choices.consumeAt site b ch₀).1 :: ch, ?_⟩
      have h₂ := hall _ (by rw [hc])
      rwa [hc] at h₂

/-- `NoRefusal`'s one-step preservation: the domain premise survives every successful step
(no `StateWf` needed — the prefix from the successor is a prefix from the predecessor, one
step longer, under the tape `stepFn_any_residual` supplies). -/
theorem noRefusal_step {ctx : ProgramCtx} {s s' : Store} {c c' : Config} {ch₀ ch₀' : Choices}
    {l : StepLabel} (hnr : NoRefusal ctx s c) (h : stepFn ctx s c ch₀ = .ok (c', s', ch₀', l)) :
    NoRefusal ctx s' c' := by
  intro n ch ls sf cf chf hp
  obtain ⟨ch₁, h₁⟩ := stepFn_any_residual h ch
  exact hnr (n + 1) ch₁ (l :: ls) sf cf chf (.step h₁ hp)

/-! ## Silent projection, the single-goroutine embedding, the program seam -/

theorem silent_projection : silent_projection_stmt := StepLabel.fold_silent

theorem single_embedding : single_embedding_stmt := fun _ _ _ _ _ _ _ hr htr =>
  execProgLoop_single hr htr

theorem program_bridge : program_bridge_stmt := by
  intro fuel p name args ch pctx c₀ s₀ locs ch₁ h
  unfold runProgramPoolOutM
  rw [h]
  rfl

/-! ## Boundary CONTROLS (deliverable 4; `#eval`-checked before each `rfl`) -/

section Controls

/-- A payload the abort renderer refuses: a string whose first line is not valid UTF-8. -/
def controlBadEntry : PanicEntry := ⟨.interface .string (.string ⟨#[0xff]⟩), false⟩

-- an abort: fuel-out at 0, the panic terminal at 1
example (s : Store) (ch : Choices) :
    execStmtLoop (ProgramCtx.ofTables #[] #[]) 0 s (.panicking [panicEntry "review"] .stop) ch
      = .error .fuelOut := rfl
example (s : Store) :
    execStmtLoop (ProgramCtx.ofTables #[] #[]) 1 s (.panicking [panicEntry "review"] .stop) []
      = .error (.terminal (.panic "review")) := by with_unfolding_all rfl
-- normal completion at 0
example (s : Store) (ch : Choices) :
    execStmtLoop (ProgramCtx.ofTables #[] #[]) 0 s (.next .stop) ch = .ok (s, ch) := rfl
-- a blocked form at 0: the deadlock
example (s : Store) (ch : Choices) :
    execStmtLoop (ProgramCtx.ofTables #[] #[]) 0 s (.blockedSelect [] [] .stop) ch
      = .error (.terminal .deadlock) := rfl
-- a renderer refusal: the refusal at 1, fuel-out at 0
example : ∃ r, execStmtLoop (ProgramCtx.ofTables #[] #[]) 1 {} (.panicking [controlBadEntry] .stop) []
    = .error (.refusal r) := ⟨_, by with_unfolding_all rfl⟩
example (s : Store) (ch : Choices) :
    execStmtLoop (ProgramCtx.ofTables #[] #[]) 0 s (.panicking [controlBadEntry] .stop) ch
      = .error .fuelOut := rfl

end Controls

end GoLean.GoCore.ExecutionStatement
