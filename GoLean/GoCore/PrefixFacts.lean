import GoLean.GoCore.MachineSound

/-!
# Supporting sweeps for the execution bridges (window charter row 2b)

[AGENT packet B worker] 2026-09-28. Two families of facts about the executable step that the
bridges of `Prefix.lean` need and that no existing module states:

* **The step's pick records** (`stepFn_picks_none` / `stepFn_picks_some`): the records a
  successful step emits are exactly the records of the consultation `seqConsumption` names —
  none when it names none, the one `PickRecord.ofPick` of the tape's pick otherwise. With the
  consumption theorems this is replay BY RECORD (`replay_coverage`).
* (The premise-free copy `stepFn_consumption_some'` that lived here — the `some` half of
  `MachineSound.stepFn_consumption_some` without its unread `c.appendTargetLocal` premise — was
  FOLDED BACK by packet D, 2026-10-03 (packet B audit F3): `stepFn_consumption_some` itself is now
  premise-free; BridgeSet row 62 re-targets it.)

The sweeps are driven by the combinator predicate `OkP` (a property of every `.ok` result of
an `Except` computation) and the tactic `okp`, which descends `bind`/`map`/`pure`/`if`/`match`
and the two delivery helpers.
-/

namespace GoLean.GoCore.Machine

open GoLean

variable {ctx : ProgramCtx}

/-! ## `OkP`: a property of every successful result -/

/-- Every `.ok` result of `x` satisfies `P`. -/
def OkP {ε α : Type} (P : α → Prop) (x : Except ε α) : Prop := ∀ a, x = .ok a → P a

theorem OkP.pure {ε α : Type} {P : α → Prop} {a : α} (h : P a) : OkP P (pure a : Except ε α) :=
  fun _ he => by cases he; exact h
theorem OkP.ok {ε α : Type} {P : α → Prop} {a : α} (h : P a) : OkP P (.ok a : Except ε α) :=
  fun _ he => by cases he; exact h
theorem OkP.error {ε α : Type} {P : α → Prop} {e : ε} : OkP P (.error e : Except ε α) :=
  fun _ he => by cases he
theorem OkP.throw {ε α : Type} {P : α → Prop} {e : ε} : OkP P (throw e : Except ε α) :=
  fun _ he => by cases he
theorem OkP.bind {ε α β : Type} {P : β → Prop} {x : Except ε α} {f : α → Except ε β}
    (hf : ∀ a, OkP P (f a)) : OkP P (x >>= f) := by
  intro b h
  cases x with
  | error e => cases h
  | ok a => exact hf a b h
theorem OkP.bind_map {ε α β γ : Type} {P : γ → Prop} {x : Except ε α} {g : α → β}
    {f : β → Except ε γ} (hf : ∀ a, OkP P (f (g a))) : OkP P (Except.map g x >>= f) := by
  intro b h
  cases x with
  | error e => cases h
  | ok a => exact hf a b h
theorem OkP.bind_eq {ε α β : Type} {P : β → Prop} {x : Except ε α} {f : α → Except ε β}
    (hf : ∀ a, x = .ok a → OkP P (f a)) : OkP P (x >>= f) := by
  intro b h
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact hf a hx b h
theorem OkP.map {ε α β : Type} {P : β → Prop} {x : Except ε α} {g : α → β}
    (hf : ∀ a, P (g a)) : OkP P (g <$> x) := by
  intro b h
  cases x with
  | error e => cases h
  | ok a => cases h; exact hf a
theorem OkP.exmap {ε α β : Type} {P : β → Prop} {x : Except ε α} {g : α → β}
    (hf : ∀ a, P (g a)) : OkP P (Except.map g x) := by
  intro b h
  cases x with
  | error e => cases h
  | ok a => cases h; exact hf a
theorem OkP.ite {ε α : Type} {P : α → Prop} {c : Prop} [Decidable c] {a b : Except ε α}
    (ha : OkP P a) (hb : OkP P b) : OkP P (if c then a else b) := by
  split <;> assumption

/-- Descend a do-pipeline for an `OkP` goal. -/
macro "okp" : tactic => `(tactic| repeat' (first
  | exact OkP.error
  | exact OkP.throw
  | refine OkP.bind_eq (fun _ _ => ?_)
  | refine OkP.map (fun _ => ?_)
  | refine OkP.pure ?_
  | refine OkP.ok ?_
  | rfl
  | (unfold deliverS)
  | (unfold deliverV)
  | split
  | (dsimp (config := { zetaDelta := true }) only)))

/-- Normalize concrete binds and deliveries, then descend. -/
macro "okp_norm" : tactic => `(tactic| (
  simp only [Except.map, toResult_ok, toResult_panic, toResult_refusal, toResult_fatal,
    toResult_deadlock, toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind,
    deliverV_ok, deliverV_panic, deliverS_ok, deliverS_panic, pure_eq_ok]
  okp))

/-! ## The step's pick records -/

/-- The records the step at `(σ, c)` under tape `ch` emits, read off `seqConsumption`. -/
def seqPicks (ctx : ProgramCtx) (σ : Store) (c : Config) (ch : Choices) : List PickRecord :=
  match seqConsumption ctx σ c with
  | none => []
  | some (site, b) => PickRecord.ofPick site b (Choices.consumeAt site b ch).1

/-- An entry whose consult is `none` keeps no record, on either path. -/
theorem entry_ps_nil {σ : Store} {fid : FuncId} {args : List GoValue} {ch ch' : Choices}
    {r : Result (Commit (Entry × Store × AccessTrace))}
    {ps : List PickRecord} (hsc : entryConsult? ctx σ fid args = none)
    (hx : enterFramePickV ctx σ fid args ch = .ok (r, ch', ps)) : ps = [] := by
  rcases enterFramePickV_cases hx with ⟨_, _, _, _, rfl⟩ | ⟨msg, _, hplan, _, rfl⟩
  · rfl
  · rcases entryConsult?_none hsc with hnv | hnp
    · simp [nilValueMethodWidth_of_isSome_false hnv, PickRecord.ofPick]
    · exact absurd (by simp [enterFrame, hplan, Bind.bind, Except.bind]) (hnp msg)

/-- A bound-below-2 record-emitting consultation keeps no record. -/
theorem consumeAtE_ps_nil {site : ChoiceSite} {b : Nat} {ch ch' : Choices} {p : Nat}
    {ps : List PickRecord} (hb : ¬ 2 ≤ b) (h : Choices.consumeAtE site b ch = (p, ch', ps)) :
    ps = [] := by
  rw [Choices.consumeAtE_le_one (by omega)] at h
  cases h; rfl

/-- An entry whose consult is `some` took the panic path, keeping the consultation's record. -/
theorem entry_some_panic {σ : Store} {fid : FuncId} {args : List GoValue} {ch ch' : Choices}
    {r : Result (Commit (Entry × Store × AccessTrace))}
    {ps : List PickRecord} {site : ChoiceSite} {b : Nat}
    (hsc : entryConsult? ctx σ fid args = some (site, b))
    (hx : enterFramePickV ctx σ fid args ch = .ok (r, ch', ps)) :
    ∃ msg, r = .panic msg ∧ ps = PickRecord.ofPick site b (Choices.consumeAt site b ch).1 := by
  obtain ⟨rfl, rfl, _, msg, hpanic⟩ := entryConsult?_some hsc
  rcases enterFramePickV_cases hx with ⟨c, _, hplan, _, _⟩ | ⟨msg', hr, _, _, hps⟩
  · exfalso
    have henter : enterFrame ctx σ fid args = c σ := by
      simp [enterFrame, hplan, Bind.bind, Except.bind]
    rw [henter] at hpanic
    exact enterFrame_commit_noPanic σ fid args c hplan σ msg hpanic
  · exact ⟨_, hr, hps⟩

/-- A spilling append's consult pops (its width is at least 2). -/
theorem appendSpill?_gt_one {σ : Store} {elem : Ty} {vs : List GoValue} {w : Nat}
    (h : appendSpill? ctx σ elem vs = some w) : 1 < w := by
  unfold appendSpill? at h
  repeat' split at h
  all_goals first
    | cases h
    | (simp at h; done)
    | (simp at h; obtain ⟨-, -, rfl⟩ := h; exact one_lt_appendSpillWidth _ _)


/-- The entry arms of the `some` records sweep. -/
macro "picks_entry_some " hsc:ident : tactic =>
  `(tactic| (
    simp_all only [seqConsumption, Config.applyPos, entryCallSite?]
    okp
    all_goals
      obtain ⟨_, hr, hps⟩ := entry_some_panic $hsc:ident (by assumption)
      first | exact hps | (cases hr <;> exact hps) | (exfalso; simp_all; done)))

/-- The entry arms of the `none` records sweep. -/
macro "picks_entry_none " hsc:ident : tactic =>
  `(tactic| (
    simp_all only [seqConsumption, Config.applyPos, entryCallSite?]
    okp
    all_goals exact entry_ps_nil $hsc:ident (by assumption)))

/-- The `.stop` arm's records (unit 6b): with the projection `none` — a settled chain (which
throws) or a non-colliding phase step (bound 1) — no record is emitted. -/
theorem stepPanicStop_picks_none {σ : Store} {first : PanicEntry} {rest : List PanicEntry}
    {ch₀ : Choices}
    (hsc : seqConsumption ctx σ (.panicking (first :: rest) .stop) = none) :
    OkP (fun r : Config × Store × Choices × StepLabel => r.2.2.2.picks = [])
      (stepPanicStop ctx σ first rest ch₀) := by
  intro r hr
  unfold stepPanicStop at hr
  split at hr
  · simp only [bind_eq_ok] at hr
    obtain ⟨msg, -, hr⟩ := hr
    simp [throw, throwThe, MonadExceptOf.throw] at hr
  · rename_i older entry newer hsplit
    simp only [seqConsumption, hsplit] at hsc
    have hcol : preprintCollide older entry = false := by
      cases hc : preprintCollide older entry
      · rfl
      · simp [hc] at hsc
    have hw : preprintWidth older entry = 1 := by simp [preprintWidth, hcol]
    rw [hw, Choices.consumeAtE_le_one (Nat.le_refl 1)] at hr
    simp only [pure_eq_ok, Except.ok.injEq] at hr
    subst hr
    rfl

/-- … and with the projection `some`: the phase's collision draw records the
`repanicCollapse` pick at bound 2 (a settled chain throws). -/
theorem stepPanicStop_picks_some {σ : Store} {first : PanicEntry} {rest : List PanicEntry}
    {ch₀ : Choices} {site : ChoiceSite} {b : Nat}
    (hsc : seqConsumption ctx σ (.panicking (first :: rest) .stop) = some (site, b)) :
    OkP (fun r : Config × Store × Choices × StepLabel =>
        r.2.2.2.picks = PickRecord.ofPick site b (Choices.consumeAt site b ch₀).1)
      (stepPanicStop ctx σ first rest ch₀) := by
  intro r hr
  unfold stepPanicStop at hr
  split at hr
  · simp only [bind_eq_ok] at hr
    obtain ⟨msg, -, hr⟩ := hr
    simp [throw, throwThe, MonadExceptOf.throw] at hr
  · rename_i older entry newer hsplit
    simp only [seqConsumption, hsplit] at hsc
    have hcol : preprintCollide older entry = true := by
      cases hc : preprintCollide older entry
      · simp [hc] at hsc
      · rfl
    simp only [hcol, ite_true, Option.some.injEq, Prod.mk.injEq] at hsc
    obtain ⟨rfl, rfl⟩ := hsc
    have hw : preprintWidth older entry = 2 := by simp [preprintWidth, hcol]
    rw [hw] at hr
    rcases hx : Choices.consumeAtE .repanicCollapse 2 ch₀ with ⟨pick, ch', ps⟩
    rw [hx] at hr
    simp only [pure_eq_ok, Except.ok.injEq] at hr
    subst hr
    obtain ⟨hps, hc⟩ := Choices.consumeAtE_inv hx
    simp only [hc]
    exact hps

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
/-- **No record without a consultation**: a step whose projection is `none` emits no pick
record. -/
theorem stepFn_picks_none {σ : Store} {c : Config} {ch₀ : Choices}
    (hsc : seqConsumption ctx σ c = none) :
    OkP (fun r : Config × Store × Choices × StepLabel => r.2.2.2.picks = [])
      (stepFn ctx σ c ch₀) := by
  fun_cases stepFn ctx σ c ch₀
  all_goals (try (okp; done))
  case case6 => simp [seqConsumption] at hsc
  case case7 =>
    -- The `.stop` arm (unit 6b): the abort throws; the phase step at a
    -- non-colliding entry pops nothing (bound 1).
    exact stepPanicStop_picks_none hsc
  case case137 => unfold stepRetOther; okp
  case case152 => unfold stepNextOther; okp
  case case2 => picks_entry_none hsc
  case case32 => picks_entry_none hsc
  case case91 => picks_entry_none hsc
  case case95 => picks_entry_none hsc
  case case101 => picks_entry_none hsc
  case case63 => unfold stepUnseqEnter; okp
  case case135 => unfold stepUnseqValue; okp
  case case142 =>
    unfold stepFrameExit; okp
    all_goals
      simp only [seqConsumption, Config.applyPos, entryCallSite?] at hsc
      exact entry_ps_nil hsc (by assumption)
  case case154 =>
    unfold stepFrameExit; okp
    all_goals
      simp only [seqConsumption, Config.applyPos, entryCallSite?] at hsc
      exact entry_ps_nil hsc (by assumption)
  case case151 =>
    unfold stepUnseqNext; okp
    all_goals
      simp only [seqConsumption] at hsc
      split at hsc
      · cases hsc
      · exact consumeAtE_ps_nil ‹_› (by assumption)
  case case94 =>
    simp only [seqConsumption, Config.applyPos] at hsc
    obtain ⟨r, hr⟩ := applyStmtOp_plan_of_stmtConsult?_none (nt := ‹Nat›) hsc
    rw [hr]
    cases r with
    | error e => cases_stop e <;> okp_norm
    | ok c =>
      simp only [Except.map, toResult_ok, Bind.bind, Except.bind, deliverV_ok, runCommit_withStream]
      intro a ha
      cases hrc : runCommit c σ <;> simp_all [Functor.map, Except.map]
      all_goals (subst_vars; rfl)
  case case116 =>
    rename_i v clauses default? done env k'
    cases hcore : applySelectCore ctx σ clauses default? ((v :: done).reverse) env k' with
    | error e =>
      rw [applySelect_error_stream hcore]
      cases_stop e <;> okp_norm
    | ok o =>
      cases o with
      | done c₁ s₁ cl? tr₁ =>
        rw [applySelect_done_stream hcore]
        okp_norm
      | picks poll commits =>
        simp only [seqConsumption, Config.applyPos, selectConsult?] at hsc
        rw [hcore] at hsc
        cases hsc
  case case131 =>
    rename_i v op done env k'
    simp only [seqConsumption, Config.applyPos, syncConsult?, Option.map_eq_none_iff] at hsc
    cases hop : op.tryTargets? with
    | none =>
      cases hap : applySyncOp ctx σ ch₀ op ((v :: done).reverse) env k' with
      | error e => cases_stop e <;> okp_norm
      | ok p =>
        obtain ⟨c₂, σ₂, ch₂, ps₂, tr₂⟩ := p
        obtain ⟨rfl, rfl, -⟩ := applySyncOp_core_ok hop hap
        okp_norm
    | some targets =>
      cases done with
      | cons hd tl =>
        unfold applySyncOp
        rw [hop]
        rcases hrev : (v :: hd :: tl).reverse with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · have := congrArg List.length hrev; simp at this
        · have := congrArg List.length hrev; simp at this
        · simp only [stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
          okp_norm
      | nil =>
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append] at hsc ⊢
        unfold tryLockConsult? at hsc
        rw [hop] at hsc
        (try dsimp only at hsc)
        cases hl : valueAsLoc v with
        | error e =>
          have hap : applySyncOp ctx σ ch₀ op [v] env k' = .error e := by
            simp [applySyncOp, hop, hl, Bind.bind, Except.bind, Except.map]
          rw [hap]; cases_stop e <;> okp_norm
        | ok loc =>
          rw [hl] at hsc
          (try dsimp only at hsc)
          cases hcell : syncCell ctx σ loc with
          | error e =>
            have hap : applySyncOp ctx σ ch₀ op [v] env k' = .error e := by
              simp [applySyncOp, hop, hl, hcell, Bind.bind, Except.bind, Except.map]
            rw [hap]; cases_stop e <;> okp_norm
          | ok pre =>
            rw [hcell] at hsc
            (try dsimp only at hsc)
            have hw : tryLockWidth op pre ≤ 1 := by
              by_cases hle : tryLockWidth op pre ≤ 1
              · exact hle
              · simp [hle] at hsc
            rw [applySyncOp_try_nopop hop hl hcell hw ch₀]
            cases applyTryLock ctx σ op loc pre false targets env k' with
            | error e => cases_stop e <;> okp_norm
            | ok p => okp_norm
  case case147 =>
    rename_i kv vv kt vt body base produced start env k'
    simp only [seqConsumption, mapIterConsult?] at hsc
    cases hcands : mapIterCandidates ctx σ kt vt base produced with
    | error e => simp only [Bind.bind, Except.bind]; exact OkP.error
    | ok pc =>
      obtain ⟨cands, trc⟩ := pc
      rw [hcands] at hsc
      (try dsimp only at hsc)
      simp only [Bind.bind, Except.bind]
      by_cases hemp : cands.isEmpty
      · rw [if_pos hemp]; okp
      · rw [if_neg hemp] at hsc ⊢
        have hw : ¬ 2 ≤ cands.size + (if mapIterMandatoryRemains cands start = true then 0 else 1) := by
          intro h2; simp [show ¬ (cands.size + (if mapIterMandatoryRemains cands start = true then 0 else 1) ≤ 1) by omega] at hsc
        (try dsimp only)
        rw [Choices.consumeAtE_le_one (by omega)]
        okp

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
/-- **The record IS the consultation's**: a step whose projection is `some (site, b)` emits
exactly the records of the tape's pick at that site and bound. -/
theorem stepFn_picks_some {σ : Store} {c : Config} {ch₀ : Choices} {site : ChoiceSite} {b : Nat}
    (hsc : seqConsumption ctx σ c = some (site, b)) :
    OkP (fun r : Config × Store × Choices × StepLabel =>
        r.2.2.2.picks = PickRecord.ofPick site b (Choices.consumeAt site b ch₀).1)
      (stepFn ctx σ c ch₀) := by
  fun_cases stepFn ctx σ c ch₀
  all_goals first
    | (simp [seqConsumption, Config.applyPos, entryCallSite?] at hsc; done)
    | (simp_all [seqConsumption, Config.applyPos, entryCallSite?]; done)
    | (okp; done)
    | skip
  case case153 =>
    simp [seqConsumption, Config.applyPos, entryCallSite?_of_signalStep ‹_›] at hsc
  case case2 => picks_entry_some hsc
  case case32 => picks_entry_some hsc
  case case91 => picks_entry_some hsc
  case case95 => picks_entry_some hsc
  case case101 => picks_entry_some hsc
  case case142 =>
    unfold stepFrameExit; okp
    all_goals first
      | (simp [seqConsumption, Config.applyPos, entryCallSite?] at hsc; done)
      | (simp only [seqConsumption, Config.applyPos, entryCallSite?] at hsc
         obtain ⟨_, hr, hps⟩ := entry_some_panic hsc (by assumption)
         first | exact hps | (cases hr <;> exact hps) | (exfalso; simp_all; done))
  case case154 =>
    unfold stepFrameExit; okp
    all_goals first
      | (simp [seqConsumption, Config.applyPos, entryCallSite?] at hsc; done)
      | (simp only [seqConsumption, Config.applyPos, entryCallSite?] at hsc
         obtain ⟨_, hr, hps⟩ := entry_some_panic hsc (by assumption)
         first | exact hps | (cases hr <;> exact hps) | (exfalso; simp_all; done))
  case case6 =>
    simp only [seqConsumption, Option.some.injEq, Prod.mk.injEq] at hsc
    obtain ⟨rfl, rfl⟩ := hsc
    okp
    all_goals (obtain ⟨hps, hc⟩ := Choices.consumeAtE_inv (by assumption); rw [hc]; exact hps)
  case case7 =>
    -- The `.stop` arm (unit 6b): the abort throws; the phase's collision
    -- draw records the `repanicCollapse` pick at bound 2.
    exact stepPanicStop_picks_some hsc
  case case94 =>
    rename_i v op nt done env k'
    simp only [seqConsumption, Config.applyPos] at hsc
    -- the two consuming wide ops: the spilling append, and (unit 5b) the `[0, n)` draw
    rcases stmtConsult?_some hsc with ⟨elem, rfl, rfl, hw⟩ | ⟨rfl, rfl, hw⟩
    · obtain ⟨g, hg, hnp⟩ := applyStmtOp_plan_appendSlice_spill (nt := nt) hw
      have h1 := appendSpill?_gt_one hw
      rw [hg]
      cases hgv : g (Choices.consumeAt .appendSpill b ch₀).1 with
      | error e =>
        cases_stop e
        all_goals first
          | (okp_norm; done)
          | exact absurd hgv (hnp _ _)
      | ok c =>
        simp only [Except.map, toResult_ok, Bind.bind, Except.bind, deliverV_ok, runCommit_withStream]
        intro a ha
        cases hrc : runCommit c σ <;> simp_all [Functor.map, Except.map]
        all_goals (subst_vars; simp [PickRecord.ofPick, show ¬ b ≤ 1 by omega])
    · obtain ⟨g, hg, hnp⟩ := applyStmtOp_plan_randIntn_draw (nt := nt) hw
      have h1 := intnBound?_gt_one hw
      rw [hg]
      cases hgv : g (Choices.consumeAt .intn b ch₀).1 with
      | error e =>
        cases_stop e
        all_goals first
          | (okp_norm; done)
          | exact absurd hgv (hnp _ _)
      | ok c =>
        simp only [Except.map, toResult_ok, Bind.bind, Except.bind, deliverV_ok, runCommit_withStream]
        intro a ha
        cases hrc : runCommit c σ <;> simp_all [Functor.map, Except.map]
        all_goals (subst_vars; simp [PickRecord.ofPick, show ¬ b ≤ 1 by omega])
  case case116 =>
    rename_i v clauses default? done env k'
    simp only [seqConsumption, Config.applyPos, selectConsult?] at hsc
    cases hcore : applySelectCore ctx σ clauses default? ((v :: done).reverse) env k' with
    | error e => rw [hcore] at hsc; cases hsc
    | ok o =>
      cases o with
      | done c₁ s₁ cl? tr₁ => rw [hcore] at hsc; cases hsc
      | picks poll commits =>
        rw [hcore] at hsc
        simp only [Option.some.injEq, Prod.mk.injEq] at hsc
        obtain ⟨rfl, rfl⟩ := hsc
        rw [applySelect_picks_stream hcore]
        cases commits[(Choices.consumeAt .l2Entry commits.length ch₀).1]? with
        | none => okp_norm
        | some p =>
          obtain ⟨cl, r⟩ := p
          cases r <;> okp_norm
  case case131 =>
    rename_i v op done env k'
    simp only [seqConsumption, Config.applyPos, syncConsult?, Option.map_eq_some_iff,
      Prod.mk.injEq] at hsc
    obtain ⟨w, hw, rfl, rfl⟩ := hsc
    unfold tryLockConsult? at hw
    cases hop : op.tryTargets? with
    | none => rw [hop] at hw; cases hw
    | some targets =>
      rw [hop] at hw
      cases done with
      | cons hd tl =>
        exfalso
        rcases hrev : (v :: hd :: tl).reverse with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · have := congrArg List.length hrev; simp at this
        · have := congrArg List.length hrev; simp at this
        · rw [hrev] at hw; cases hw
      | nil =>
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append] at hw ⊢
        (try dsimp only at hw)
        cases hl : valueAsLoc v with
        | error e => rw [hl] at hw; cases hw
        | ok loc =>
          rw [hl] at hw
          (try dsimp only at hw)
          cases hcell : syncCell ctx σ loc with
          | error e => rw [hcell] at hw; cases hw
          | ok pre =>
            rw [hcell] at hw
            (try dsimp only at hw)
            split at hw
            · cases hw
            · simp only [Option.some.injEq] at hw
              subst hw
              rw [applySyncOp_try_stream hop hl hcell]
              cases hat : applyTryLock ctx σ op loc pre
                  ((Choices.consumeAt .tryLock (tryLockWidth op pre) ch₀).1 == 1) targets env k' with
              | error e =>
                cases_stop e
                all_goals first
                  | (okp_norm; done)
                  | exact absurd hat (applyTryLock_noPanic hcell _ _ _ _ _ _)
              | ok p => okp_norm
  case case147 =>
    rename_i kv vv kt vt body base produced start env k'
    simp only [seqConsumption, mapIterConsult?] at hsc
    cases hcands : mapIterCandidates ctx σ kt vt base produced with
    | error e => rw [hcands] at hsc; cases hsc
    | ok pc =>
      obtain ⟨cands, trc⟩ := pc
      rw [hcands] at hsc
      (try dsimp only at hsc)
      simp only [Bind.bind, Except.bind]
      by_cases hemp : cands.isEmpty
      · simp [hemp] at hsc
      · rw [if_neg hemp] at hsc ⊢
        have hsc' : ChoiceSite.mapIter = site ∧
            (cands.size + (if mapIterMandatoryRemains cands start = true then 0 else 1)) = b := by
          by_cases hle : cands.size + (if mapIterMandatoryRemains cands start = true then 0 else 1) ≤ 1
          · simp [hle] at hsc
          · simpa [hle] using hsc
        obtain ⟨rfl, rfl⟩ := hsc'
        (try dsimp only)
        rw [Choices.consumeAtE_eq]
        okp
  case case151 =>
    rename_i g thenB st tg env ph k'
    cases ph with
    | run i => simp [seqConsumption, Config.applyPos, entryCallSite?] at hsc
    | wait i => simp [seqConsumption, Config.applyPos, entryCallSite?] at hsc
    | pick =>
      obtain ⟨rfl, rfl, hge⟩ : site = .unseqNext ∧ b = (g.ready st).length
          ∧ 2 ≤ (g.ready st).length := by
        simp only [seqConsumption] at hsc
        split at hsc
        · simp only [Option.some.injEq, Prod.mk.injEq] at hsc
          exact ⟨hsc.1.symm, hsc.2.symm, ‹_›⟩
        · cases hsc
      by_cases hall : g.allSettled st = true
      · have := UnseqGraph.ready_nil_of_allSettled hall
        rw [this] at hge; simp at hge
      · unfold stepUnseqNext
        dsimp only
        okp
        all_goals first
          | (simp only [Choices.consumeAtE_eq]; done)
          | (exfalso; simp_all; done)
          | (rename_i hx; obtain ⟨hps, hc⟩ := Choices.consumeAtE_inv hx; rw [hc]; exact hps)

end GoLean.GoCore.Machine
