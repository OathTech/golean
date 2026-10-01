import GoLean.GoCore.MachineSound

/-!
# Supporting sweeps for the execution bridges (window charter row 2b)

[AGENT packet B worker] 2026-09-28. Two families of facts about the executable step that the
bridges of `Prefix.lean` need and that no existing module states:

* **The step's pick records** (`stepFn_picks_none` / `stepFn_picks_some`): the records a
  successful step emits are exactly the records of the consultation `seqConsumption` names —
  none when it names none, the one `PickRecord.ofPick` of the tape's pick otherwise. With the
  consumption theorems this is replay BY RECORD (`replay_coverage`).
* **The premise-free consumption theorem** (`stepFn_consumption_some'`): the `some` half of
  `MachineSound.stepFn_consumption_some` WITHOUT its `c.appendTargetLocal` premise — that
  proof never used it (`_hloc`; «kept in the statement for its callers»), and the proof below
  is the same case sweep with the premise dropped.

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

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
/-- **The consumption theorem, `some` half, premise-free**: `stepFn_consumption_some`
(MachineSound) without its `c.appendTargetLocal` premise. That proof never read the premise
(`_hloc`, «kept in the statement for its callers»: the spilling append's post-consult validate
tail is panic-free for EVERY target, `applyStmtOp_plan_appendSlice_spill`); this is the same
case sweep, copied verbatim with the binder dropped ([AGENT packet B worker]: the owning module
is outside packet B's edit boundary, so the premise is dropped here rather than there). -/
theorem stepFn_consumption_some' {σ : Store} {c : Config} {ch₀ : Choices}
    {c' : Config} {σ' : Store} {ch₀' : Choices} {site : ChoiceSite} {b : Nat} {tr : StepLabel}
    (hsc : seqConsumption ctx σ c = some (site, b))
    (h : stepFn ctx σ c ch₀ = .ok (c', σ', ch₀', tr)) :
    ch₀' = (Choices.consumeAt site b ch₀).2 ∧ ∀ ch : Choices,
      (Choices.consumeAt site b ch).1 = (Choices.consumeAt site b ch₀).1 →
      stepFn ctx σ c ch = .ok (c', σ', (Choices.consumeAt site b ch).2, tr) := by
  fun_cases stepFn ctx σ c ch₀
  all_goals first
    | (simp [seqConsumption, Config.applyPos, entryCallSite?] at hsc; done)
    | (simp [stepFn] at h; done)
    | (simp_all [stepFn]; done)
    | (simp_all [seqConsumption, Config.applyPos, entryCallSite?]; done)
    | skip
  case case6 =>
    -- The `unseqPanic` pop (E13 option (b)): bound 2, the step depends on
    -- the stream only through the pick.
    rename_i chain k' pick ch'' ps hx
    simp only [seqConsumption, Option.some.injEq, Prod.mk.injEq] at hsc
    obtain ⟨rfl, rfl⟩ := hsc
    obtain ⟨rfl, hx'⟩ := Choices.consumeAtE_inv hx
    simp only [stepFn, hx, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨by rw [hx'], fun ch hpk => ?_⟩
    rw [hx'] at hpk
    obtain ⟨p, cs, hpc⟩ : ∃ p cs, Choices.consumeAt .unseqPanic 2 ch = (p, cs) := ⟨_, _, rfl⟩
    rw [hpc] at hpk ⊢
    simp only at hpk
    subst hpk
    simp [stepFn, hpc, Choices.consumeAtE_eq]
  -- The `unseq` scheduler's pick (Stage B): the `unseqNext` pop at bound
  -- `|ready|`, the step depending on the stream only through the pick.
  case case151 =>
    simp only [stepFn] at h ⊢
    exact stepUnseqNext_consumption_some hsc h
  case case2 =>
    consumption_entry_some h hsc
  case case32 =>
    consumption_entry_some h hsc
  case case91 =>
    consumption_entry_some h hsc
  case case95 =>
    consumption_entry_some h hsc
  case case101 =>
    consumption_entry_some h hsc
  case case7 =>
    -- THE ABORT: the `repanicCollapse` consult's step is the `panic`
    -- terminal (or the render's refusal) — it never returns `.ok`, so the
    -- `some` half is vacuous here (the pool's `stepMulti_sound` carries
    -- the pick into the relation).
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨msg, -, h⟩ := h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case142 =>
    simp only [stepFn] at h ⊢
    exact stepFrameExit_consumption_some (.inl rfl) hsc h
  case case153 =>
    -- B4: a signal the table resolves consumes nothing (no entry, no apply).
    exfalso
    simp [seqConsumption, Config.applyPos, entryCallSite?_of_signalStep ‹_›] at hsc
  case case154 =>
    simp only [stepFn, signalStep_frame] at h ⊢
    exact stepFrameExit_consumption_some (.inr rfl) hsc h
  case case94 =>
    simp only [seqConsumption, Config.applyPos] at hsc
    -- the two consuming wide ops (`stmtConsult?_some`): the spilling append and
    -- (unit 5b) the `[0, n)` draw; each plan is pick-lifted and `stepFn_stmtOp_pick`
    -- closes both. C1 S3: the post-consult tail is the validate phase's,
    -- panic-free for EVERY target — no root-target proviso is needed here.
    rcases stmtConsult?_some hsc with ⟨elem, rfl, rfl, hw⟩ | ⟨rfl, rfl, hw⟩
    · obtain ⟨g, hg, hnp⟩ := applyStmtOp_plan_appendSlice_spill hw
      exact stepFn_stmtOp_pick hg hnp h
    · obtain ⟨g, hg, hnp⟩ := applyStmtOp_plan_randIntn_draw hw
      exact stepFn_stmtOp_pick hg hnp h
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
        unfold stepFn at h
        dsimp only at h
        rw [applySelect_picks_stream hcore ch₀] at h
        cases hget : commits[(Choices.consumeAt .l2Entry commits.length ch₀).1]? with
        | none =>
          rw [hget] at h
          simp [Bind.bind, Except.bind] at h
        | some p =>
          rw [hget] at h
          obtain ⟨cl, r⟩ := p
          cases r with
          | inl q =>
            obtain ⟨c₂, s₂, tr₂⟩ := q
            simp only [toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            refine ⟨rfl, fun ch hpk => ?_⟩
            unfold stepFn
            dsimp only
            rw [applySelect_picks_stream hcore ch, hpk, hget]
            rfl
          | inr msg =>
            simp only [toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            refine ⟨rfl, fun ch hpk => ?_⟩
            unfold stepFn
            dsimp only
            rw [applySelect_picks_stream hcore ch, hpk, hget]
            rfl
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
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append] at h hw
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
              have hap := applySyncOp_try_stream (env := env) (k := k') hop hl hcell
              unfold stepFn at h
              dsimp only at h
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append] at h
              rw [hap ch₀] at h
              cases hat : applyTryLock ctx σ op loc pre
                  ((Choices.consumeAt .tryLock (tryLockWidth op pre) ch₀).1 == 1) targets env k' with
              | error e =>
                rw [hat] at h
                cases_stop e <;> simp only [Except.map, toResult_panic, toResult_refusal,
                  toResult_fatal, toResult_deadlock, toResult_raceDetected, toResult_fuelOut,
                  Bind.bind, Except.bind, pure_eq_ok, deliverS_panic, Except.ok.injEq,
                  Prod.mk.injEq, reduceCtorEq] at h
                case panic msg =>
                -- refuted: a TRY head's apply never panics (`applyTryLock_noPanic`)
                exact absurd hat (applyTryLock_noPanic hcell _ _ _ _ _ msg)
              | ok p =>
                obtain ⟨c₂, σ₂⟩ := p
                rw [hat] at h
                simp only [Except.map, toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
                  Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                refine ⟨rfl, fun ch hpk => ?_⟩
                unfold stepFn
                dsimp only
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
                rw [hap ch, hpk, hat]
                rfl
  case case147 =>
    rename_i kv vv kt vt body base produced start env k'
    simp only [seqConsumption, mapIterConsult?] at hsc
    cases hcands : mapIterCandidates ctx σ kt vt base produced with
    | error e => rw [hcands] at hsc; cases hsc
    | ok pc =>
      obtain ⟨cands, trc⟩ := pc
      rw [hcands] at hsc
      (try dsimp only at hsc)
      by_cases hemp : cands.isEmpty
      · simp [hemp] at hsc
      · rw [if_neg hemp] at hsc
        obtain ⟨mand, hmand⟩ : ∃ m, mapIterMandatoryRemains cands start = m := ⟨_, rfl⟩
        rw [hmand] at hsc
        -- G-U: the projection reports the consult only at width ≥ 2.
        have hsc' : ChoiceSite.mapIter = site ∧ (cands.size + (if mand = true then 0 else 1)) = b := by
          by_cases hle : cands.size + (if mand = true then 0 else 1) ≤ 1
          · simp [hle] at hsc
          · simpa [hle] using hsc
        obtain ⟨rfl, rfl⟩ := hsc'
        rcases hcons : Choices.consumeAt .mapIter (cands.size + (if mand = true then 0 else 1)) ch₀ with ⟨idx, tail⟩
        have hpos : 0 < cands.size := by
          rcases Nat.eq_zero_or_pos cands.size with hz | hp
          · exact absurd (by simpa [Array.isEmpty_iff, Array.size_eq_zero_iff] using hz) hemp
          · exact hp
        have hltw : idx < cands.size + (if mand = true then 0 else 1) := by
          have hb := Choices.consumeAt_fst_lt (site := .mapIter) (ch := ch₀)
            (bound := cands.size + (if mand = true then 0 else 1))
            (by cases mand <;> simp <;> omega)
          rw [hcons] at hb
          exact hb
        by_cases hlt : idx < cands.size
        · rw [stepFn_mapIter_pick hcands hmand hemp hcons hlt] at h
          cases hbind : bindIterVars ctx env.pushScope σ kv vv kt vt cands[idx].2.1 cands[idx].2.2 with
          | error e => rw [hbind] at h; simp [Except.map] at h
          | ok p =>
            rw [hbind] at h
            simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            refine ⟨rfl, fun ch hpk => ?_⟩
            rcases hcons₁ : Choices.consumeAt .mapIter (cands.size + (if mand = true then 0 else 1)) ch with ⟨idx₁, tail₁⟩
            rw [hcons₁] at hpk
            simp only at hpk
            subst hpk
            rw [stepFn_mapIter_pick hcands hmand hemp hcons₁ hlt, hbind]
            rfl
        · have hmandf : mand = false := by
            cases mand
            · rfl
            · exfalso; simp at hltw; omega
          subst hmandf
          have hidx : idx = cands.size := by simp at hltw; omega
          subst hidx
          have hcons' : Choices.consumeAt .mapIter (cands.size + 1) ch₀ = (cands.size, tail) := by simpa using hcons
          rw [stepFn_mapIter_stop hcands hmand hemp hcons'] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          refine ⟨rfl, fun ch hpk => ?_⟩
          rcases hcons₁ : Choices.consumeAt .mapIter (cands.size + (if false = true then 0 else 1)) ch with ⟨idx₁, tail₁⟩
          have hcons₁' : Choices.consumeAt .mapIter (cands.size + 1) ch = (idx₁, tail₁) := by
            simpa using hcons₁
          rw [hcons₁] at hpk
          simp only at hpk
          subst hpk
          rw [stepFn_mapIter_stop hcands hmand hemp hcons₁']


end GoLean.GoCore.Machine
