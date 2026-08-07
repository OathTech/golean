import GoLean.GoCore.MultiWfSound

/-!
# The pool ∀-streams kernel checker (channels arc slice 5)

The `allStreamsOk` analogue over the ThreadPool driver — the second of
the two discharge routes the slice-2 build log recorded for `GoSpecC`'s
`∀ ch` quantifier ("the concurrent WP or a pool-level ∀-streams kernel
checker"). One kernel evaluation certifies that EVERY choice stream —
schedules (L1) and data latitude together, D8's single-stream design —
runs a seeded pool to main's `.normal` terminal with a caller-chosen
Bool readout of the joined final state.

Design (mirroring the sequential checker's discipline,
`MachineSound.lean`):

* The ONLY branched site is the L1 scheduler pick: at a boundary with
  `|runnable| > 1` the checker explores every runnable index, probing
  the REAL `stepMulti` at the singleton stream `[j]` (the consume pops
  `j`, leaving the remainder empty).
* Every OTHER consumption shape FAILS CLOSED (`false`, never unsound):
  select apply positions (L2 — `consumesSelect`, per-thread),
  `appendSlice` applies, `mapIterK` picks, and multi-candidate waiter
  pairings (L4 width > 1). The fork/join witnesses need none of these;
  a future program that does turns the checker false, visibly. The
  slice-4 CLI enumerator remains the full-width engine — this checker
  is deliberately the KERNEL-REDUCIBLE core.
* `stepThread_oblivious` is the soundness hinge: under the fail-closed
  flags (`poolThreadOblivious`), a goroutine-step that succeeds under
  one stream succeeds under EVERY stream with the same successor and
  the stream returned untouched — `stepFn_oblivious` lifted through
  the pool dispatch (wake / marker strip / spawn / singleton pairing
  are stream-free by construction).
* `raceUpdate_oblivious`: the detector's dispatcher replicates stream
  consumption only at select applies (slice 4), so under the same
  fail-closed flag its verdict is stream-independent.

`execProgLoop_ok_of_allStreamsOkPool` is the soundness theorem: checker
true at fuel `N` ⇒ every stream's pool run completes `.ok (.normal σf)`
within `N` with `post σf = true` — in particular no run deadlocks, no
run trips the race detector, on ANY modeled schedule.
-/

namespace GoLean.GoCore.Machine

-- The unused-simp-arg linter misfires on the shared multi-branch simp
-- sets (the `MultiSound.lean`/`MachineSound.lean` precedent).
set_option linter.unusedSimpArgs false

/-- Is this configuration a nonempty-branching `mapIterK` position?
(Conservative: flags every `mapIterK` `.next`, including the empty
snapshot the sequential checker probes obliviously — the pool checker
fails closed on both rather than reasoning about emptiness.) -/
def isMapIterNext : Config → Bool
  | .next (.mapIterK _ _ _ _ _ _ _ _) => true
  | _ => false

/-- The fail-closed per-thread obliviousness check: `true` only on
shapes whose `stepThread` provably ignores the choice stream
(`stepThread_oblivious`). -/
def poolThreadOblivious (s : ExecState) (ts : Array Config) (i : Nat) : Bool :=
  match ts[i]? with
  | none => false
  | some c =>
    if isBlockedConfig c then true
    else if (spawnedCont c).isSome then true
    else if (spawnPlan c).isSome then true
    else if consumesSelect c then false
    else if consumesAppendSlice c then false
    else if isMapIterNext c then false
    else
      match arrivalCases s ts i c with
      | .ok .cellPath => true
      | .ok (.single _ cs) => cs.length == 1
      | _ => false

/-- The `mapIterK` exclusion in the shape `stepFn_oblivious` consumes. -/
theorem isMapIterNext_false_elim {c : Config} (h : isMapIterNext c = false) :
    ∀ (kv vv : Option String) (kt vt : Ty) (body : Stmt)
      (rem : Array (GoValue × GoValue)) (env : LocalEnv) (k : Cont),
      c ≠ .next (.mapIterK kv vv kt vt body rem env k) := by
  intro kv vv kt vt body rem env k heq
  subst heq
  simp [isMapIterNext] at h

/-- **Stream obliviousness of the certified goroutine-step shapes**:
under the `poolThreadOblivious` flags, a `stepThread` that succeeds
under one stream succeeds under EVERY stream, with the same successor
and the stream returned untouched. -/
theorem stepThread_oblivious {s : ExecState} {ts : Array Config} {i : Nat}
    {ch₀ : Choices} {ts' : Array Config} {s' : ExecState} {ch₀' : Choices}
    (hobl : poolThreadOblivious s ts i = true)
    (h : stepThread s ts i ch₀ = .ok (ts', s', ch₀')) :
    ch₀' = ch₀ ∧ ∀ ch : Choices, stepThread s ts i ch = .ok (ts', s', ch) := by
  unfold poolThreadOblivious at hobl
  unfold stepThread at h
  cases hti : ts[i]? with
  | none => rw [hti] at hobl; cases hobl
  | some c =>
    rw [hti] at hobl h
    by_cases hblc : isBlockedConfig c = true
    · simp only [hblc, reduceIte, bind_eq_ok] at h
      obtain ⟨⟨c₂, s₂⟩, hres, h⟩ := h
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      unfold stepThread
      rw [hti]
      simp only [hblc, reduceIte, hres, Bind.bind, Except.bind]
      rfl
    · simp only [Bool.not_eq_true] at hblc
      simp only [hblc, Bool.false_eq_true, reduceIte] at h hobl
      cases hsc : spawnedCont c with
      | some k =>
        rw [hsc] at h
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨rfl, fun ch => ?_⟩
        unfold stepThread
        rw [hti]
        simp only [hblc, Bool.false_eq_true, reduceIte, hsc]
        rfl
      | none =>
        rw [hsc] at h hobl
        simp only [Option.isSome_none, Bool.false_eq_true, reduceIte] at hobl
        cases hsp : spawnPlan c with
        | some p =>
          obtain ⟨cv, args, k⟩ := p
          rw [hsp] at h
          simp only [bind_eq_ok] at h
          obtain ⟨⟨parent', child, s₂⟩, hspawn, h⟩ := h
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨rfl, fun ch => ?_⟩
          unfold stepThread
          rw [hti]
          simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp, hspawn,
            Bind.bind, Except.bind]
          rfl
        | none =>
          rw [hsp] at h hobl
          simp only [Option.isSome_none, Bool.false_eq_true, reduceIte] at hobl
          -- the fail-closed stream flags
          cases hnsel : consumesSelect c with
          | true => rw [hnsel] at hobl; simp at hobl
          | false =>
          rw [hnsel] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          cases hnapp : consumesAppendSlice c with
          | true => rw [hnapp] at hobl; simp at hobl
          | false =>
          rw [hnapp] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          cases hnmi : isMapIterNext c with
          | true => rw [hnmi] at hobl; simp at hobl
          | false =>
          rw [hnmi] at hobl
          simp only [Bool.false_eq_true, reduceIte] at hobl
          simp only [bind_eq_ok] at h
          obtain ⟨⟨plan, ch₁⟩, hplan, h⟩ := h
          cases harr : arrivalCases s ts i c with
          | error e =>
            rw [harr] at hobl
            cases hobl
          | ok r =>
            cases r with
            | cellPath =>
              rw [arrivalPlan_of_cellPath (ch := ch₀) harr] at hplan
              simp only [Except.ok.injEq, Prod.mk.injEq] at hplan
              obtain ⟨hp1, hp2⟩ := hplan
              subst hp1
              subst hp2
              simp only [bind_eq_ok] at h
              obtain ⟨⟨c₂, s₂, ch₂⟩, hstep, h⟩ := h
              simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              obtain ⟨rfl, hall⟩ := stepFn_oblivious
                (isMapIterNext_false_elim hnmi) hnapp hnsel hstep
              refine ⟨rfl, fun ch => ?_⟩
              unfold stepThread
              rw [hti]
              simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp,
                Bind.bind, Except.bind, arrivalPlan_of_cellPath (ch := ch) harr]
              rw [hall ch]
              rfl
            | single bc cands =>
              rw [harr] at hobl
              rw [arrivalPlan_of_single (ch := ch₀) harr] at hplan
              simp only [Except.ok.injEq, Prod.mk.injEq] at hplan
              obtain ⟨hp1, hp2⟩ := hplan
              subst hp1
              subst hp2
              cases cands with
              | nil => simp at hobl
              | cons cand rest =>
                cases rest with
                | nil =>
                  dsimp only at h
                  simp only [bind_eq_ok] at h
                  obtain ⟨⟨ts₂, s₂⟩, hpair, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  refine ⟨rfl, fun ch => ?_⟩
                  unfold stepThread
                  rw [hti]
                  simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp,
                    Bind.bind, Except.bind,
                    arrivalPlan_of_single (ch := ch) harr]
                  rw [hpair]
                  rfl
                | cons cand2 rest2 => simp at hobl
            | multi os =>
              rw [harr] at hobl
              cases hobl

/-- **The detector's dispatcher is stream-independent away from select
applies** (its only replication site, slice 4). -/
theorem raceUpdate_oblivious {sPre : ExecState} {tsPre : Array Config}
    {ch ch' : Choices} {m' : MultiConfig} {r : RaceState}
    (hns : ∀ cPre, tsPre[m'.cur]? = some cPre → consumesSelect cPre = false) :
    raceUpdate sPre tsPre ch m' r = raceUpdate sPre tsPre ch' m' r := by
  unfold raceUpdate
  by_cases hsz : m'.threads.size ≤ 1
  · simp [hsz]
  · simp only [hsz, Bool.false_eq_true, reduceIte]
    cases hti : tsPre[m'.cur]? with
    | none => rfl
    | some cPre =>
      have hsel := hns cPre hti
      by_cases hgrow : tsPre.size < m'.threads.size
      · simp [hgrow]
      · simp only [if_neg hgrow]
        by_cases hblk : isBlockedConfig cPre = true
        · simp [hblk]
        · simp only [hblk, Bool.false_eq_true, reduceIte]
          cases cPre <;> try rfl
          case retV v k =>
            cases k <;> try rfl
            case chanStK op done pending env kk =>
              cases pending <;> rfl
            case selectOpsK clauses d done pending env kk =>
              cases pending with
              | nil => simp [consumesSelect] at hsel
              | cons e rest => rfl

/-- **THE POOL ∀-STREAMS CHECKER** (docstring above): kernel-evaluable
certification that every choice stream completes the pool run at main's
`.normal` terminal with `post` true of the joined final state. -/
def allStreamsOkPool (post : ExecState → Bool) :
    Nat → MultiConfig → RaceState → Bool
  | 0, _, _ => false
  | fuel + 1, m, r =>
    if m.threads.isEmpty then false
    else
      match m.panicMsg? with
      | some _ => false
      | none =>
        match m.mainOutcome? with
        | some (.normal σf) => post σf
        | some _ => false
        | none =>
          if (runnableIdxs m.shared m.threads).isEmpty then false
          else
            let probe : Nat → Choices → Bool := fun i probeCh =>
              poolThreadOblivious m.shared m.threads i &&
              match stepMulti m probeCh with
              | .ok (m', chRem) =>
                  chRem.isEmpty &&
                  (match raceUpdate m.shared m.threads probeCh m' r with
                   | .ok r' => allStreamsOkPool post fuel m' r'
                   | .error _ => false)
              | .error _ => false
            match m.threads[m.cur]? with
            | none => false
            | some c =>
              if c.atBoundary then
                match runnableIdxs m.shared m.threads with
                | [] => false
                | [i] => probe i []
                | rs =>
                    (List.range rs.length).all fun j =>
                      match rs[j]? with
                      | some i => probe i [j]
                      | none => false
              else probe m.cur []


/-- A certified thread shape is never a select apply (the flag is
explicit on the cell path; the wake/marker/spawn shapes are
structurally not `.retV _ (.selectOpsK …)`). Feeds
`raceUpdate_oblivious`. -/
theorem poolThreadOblivious_nsel {s : ExecState} {ts : Array Config}
    {i : Nat} {c : Config}
    (hobl : poolThreadOblivious s ts i = true) (hti : ts[i]? = some c) :
    consumesSelect c = false := by
  unfold poolThreadOblivious at hobl
  rw [hti] at hobl
  dsimp only at hobl
  by_cases hblc : isBlockedConfig c = true
  · cases c <;> simp_all [isBlockedConfig, consumesSelect]
  · simp only [Bool.not_eq_true] at hblc
    simp only [hblc, Bool.false_eq_true, reduceIte] at hobl
    cases hsc : spawnedCont c with
    | some k =>
      obtain rfl := spawnedCont_shape hsc
      rfl
    | none =>
      simp only [hsc, Option.isSome_none, Bool.false_eq_true,
        reduceIte] at hobl
      cases hsp : spawnPlan c with
      | some p =>
        match c, hsp with
        | .retV cv (.goCalleeK [] env k), _ => rfl
        | .retV v (.goArgsK cv vals [] env k), _ => rfl
      | none =>
        simp only [hsp, Option.isSome_none, Bool.false_eq_true,
          reduceIte] at hobl
        cases hnsel : consumesSelect c with
        | true => rw [hnsel] at hobl; simp at hobl
        | false => rfl

/-- The one-layer unfolding of `execProgLoop`, as an equation. -/
theorem execProgLoop_unfold (fuel : Nat) (m : MultiConfig) (r : RaceState)
    (ch : Choices) :
    execProgLoop fuel m r ch
      = (if m.threads.isEmpty then
          throw (.internal "thread pool without a main goroutine")
        else
          match m.panicMsg? with
          | some msg => throw (.panic msg)
          | none =>
            match m.mainOutcome? with
            | some out => return (out, ch)
            | none =>
              if (runnableIdxs m.shared m.threads).isEmpty then
                throw .deadlock
              else
                match fuel with
                | 0 => throw .fuelOut
                | fuel + 1 => do
                    let (m', choices') ← stepMulti m ch
                    let r' ← raceUpdate m.shared m.threads ch m' r
                    execProgLoop fuel m' r' choices') := by
  rw [execProgLoop.eq_def]
  rfl

set_option maxHeartbeats 1600000 in
/-- **Checker soundness**: `allStreamsOkPool post fuel m r = true`
certifies that EVERY choice stream's pool run from `(m, r)` completes
at main's `.normal` terminal within `fuel`, with `post` true of the
joined final state — schedules and data latitude quantified together
(one stream), deadlock and race refusals excluded on every modeled
schedule. -/
theorem execProgLoop_ok_of_allStreamsOkPool {post : ExecState → Bool} :
    ∀ {fuel : Nat} {m : MultiConfig} {r : RaceState},
      allStreamsOkPool post fuel m r = true →
      ∀ ch : Choices, ∃ (σf : ExecState) (ch' : Choices),
        execProgLoop fuel m r ch = .ok (.normal σf, ch') ∧ post σf = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro m r hall ch
    simp [allStreamsOkPool] at hall
  | succ n ih =>
    intro m r hall ch
    unfold allStreamsOkPool at hall
    rw [execProgLoop_unfold]
    by_cases hemp : m.threads.isEmpty
    · rw [if_pos hemp] at hall; cases hall
    · rw [if_neg hemp] at hall
      rw [if_neg hemp]
      cases hp : m.panicMsg? with
      | some msg => rw [hp] at hall; cases hall
      | none =>
        rw [hp] at hall
        cases hm : m.mainOutcome? with
        | some out =>
          rw [hm] at hall
          cases out with
          | normal σf => exact ⟨σf, ch, rfl, hall⟩
          | returned σf => cases hall
          | broke σf => cases hall
          | continued σf => cases hall
        | none =>
          rw [hm] at hall
          by_cases hrun : (runnableIdxs m.shared m.threads).isEmpty
          · rw [if_pos hrun] at hall; cases hall
          · rw [if_neg hrun] at hall
            rw [if_neg hrun]
            dsimp only at hall
            -- the per-branch probe fact, discharged uniformly below
            have hprobe : ∀ {i : Nat} {probeCh : Choices},
                (poolThreadOblivious m.shared m.threads i &&
                  match stepMulti m probeCh with
                  | .ok (m', chRem) =>
                      chRem.isEmpty &&
                      (match raceUpdate m.shared m.threads probeCh m' r with
                       | .ok r' => allStreamsOkPool post n m' r'
                       | .error _ => false)
                  | .error _ => false) = true →
                -- what the induction needs: the probe's successor pool,
                -- the empty remainder, the detector verdict, and the
                -- recursive certificate
                ∃ (m' : MultiConfig) (r' : RaceState),
                  poolThreadOblivious m.shared m.threads i = true
                  ∧ stepMulti m probeCh = .ok (m', [])
                  ∧ raceUpdate m.shared m.threads probeCh m' r = .ok r'
                  ∧ allStreamsOkPool post n m' r' = true := by
              intro i probeCh hpr
              rw [Bool.and_eq_true] at hpr
              obtain ⟨hobl, hpr⟩ := hpr
              cases hsm : stepMulti m probeCh with
              | error e => rw [hsm] at hpr; cases hpr
              | ok p =>
                obtain ⟨m', chRem⟩ := p
                rw [hsm] at hpr
                dsimp only at hpr
                rw [Bool.and_eq_true] at hpr
                obtain ⟨hemp', hpr⟩ := hpr
                have hchRem : chRem = [] := by
                  cases chRem with
                  | nil => rfl
                  | cons a l => simp [List.isEmpty] at hemp'
                subst hchRem
                cases hru : raceUpdate m.shared m.threads probeCh m' r with
                | error e => rw [hru] at hpr; cases hpr
                | ok r' =>
                  rw [hru] at hpr
                  exact ⟨m', r', hobl, rfl, hru, hpr⟩
            cases hti : m.threads[m.cur]? with
            | none => rw [hti] at hall; cases hall
            | some c =>
              rw [hti] at hall
              dsimp only at hall
              -- shared finisher: from a certified probe for thread `i`
              -- and the real `stepMulti` landing on the same successor,
              -- chain the detector and the induction hypothesis.
              have hfinish : ∀ {i : Nat} {probeCh chTail : Choices}
                  {m' : MultiConfig} {r' : RaceState},
                  poolThreadOblivious m.shared m.threads i = true →
                  raceUpdate m.shared m.threads probeCh m' r = .ok r' →
                  allStreamsOkPool post n m' r' = true →
                  stepMulti m ch = .ok (m', chTail) →
                  m'.cur = i →
                  ∃ (σf : ExecState) (ch' : Choices),
                    ((match n + 1 with
                      | 0 => throw GoError.fuelOut
                      | fuel + 1 => do
                          let x ← stepMulti m ch
                          match x with
                          | (m', choices') => do
                              let r' ← raceUpdate m.shared m.threads ch m' r
                              execProgLoop fuel m' r' choices'
                      : Except GoError (ExecOutcome × Choices)))
                      = .ok (.normal σf, ch') ∧ post σf = true := by
                intro i probeCh chTail m' r' hobl hru hnext hreal hcur
                have hruReal : raceUpdate m.shared m.threads ch m' r = .ok r' := by
                  rw [raceUpdate_oblivious (ch' := probeCh)
                    (fun cPre hcp => poolThreadOblivious_nsel
                      (hcur ▸ hobl) (hcur ▸ hcp))]
                  exact hru
                obtain ⟨σf, ch'', hrec, hpost⟩ := ih hnext chTail
                refine ⟨σf, ch'', ?_, hpost⟩
                dsimp only
                rw [hreal]
                simp only [Bind.bind, Except.bind]
                rw [hruReal]
                exact hrec
              by_cases hb : c.atBoundary = true
              · rw [if_pos hb] at hall
                cases hrs : runnableIdxs m.shared m.threads with
                | nil => rw [hrs] at hall; cases hall
                | cons r0 rest =>
                  rw [hrs] at hall
                  cases rest with
                  | nil =>
                    obtain ⟨m', r', hobl, hsm, hru, hnext⟩ := hprobe hall
                    have hinto : stepThreadInto m r0 [] = .ok (m', []) := by
                      unfold stepMulti at hsm
                      rw [hti] at hsm
                      dsimp only at hsm
                      rw [if_pos hb, hrs] at hsm
                      exact hsm
                    obtain ⟨ts₂, s₂, hst, hm'⟩ :
                        ∃ ts₂ s₂,
                          stepThread m.shared m.threads r0 [] = .ok (ts₂, s₂, [])
                          ∧ m' = ⟨ts₂, s₂, r0⟩ := by
                      unfold stepThreadInto at hinto
                      simp only [bind_eq_ok] at hinto
                      obtain ⟨⟨ts₂, s₂, chr⟩, hst, hinto⟩ := hinto
                      simp only [pure_eq_ok, Except.ok.injEq,
                        Prod.mk.injEq] at hinto
                      obtain ⟨rfl, rfl⟩ := hinto
                      exact ⟨ts₂, s₂, hst, rfl⟩
                    obtain ⟨-, hallst⟩ := stepThread_oblivious hobl hst
                    have hreal : stepMulti m ch = .ok (m', ch) := by
                      unfold stepMulti
                      rw [hti]
                      dsimp only
                      rw [if_pos hb, hrs]
                      dsimp only
                      unfold stepThreadInto
                      rw [hallst ch]
                      subst hm'
                      rfl
                    exact hfinish hobl hru hnext hreal (by rw [hm'])
                  | cons r1 rest' =>
                    rcases hcons : Choices.consume ch (r0 :: r1 :: rest').length
                      with ⟨pick, tail⟩
                    have hpicklt : pick < (r0 :: r1 :: rest').length := by
                      have hb0 : 0 < (r0 :: r1 :: rest').length := by simp
                      have := consume_fst_lt (ch := ch) hb0
                      rw [hcons] at this
                      exact this
                    rw [List.all_eq_true] at hall
                    have hj := hall pick (by
                      simpa using List.mem_range.mpr hpicklt)
                    cases hget : (r0 :: r1 :: rest')[pick]? with
                    | none =>
                      rw [List.getElem?_eq_none_iff] at hget
                      omega
                    | some i =>
                      rw [hget] at hj
                      obtain ⟨m', r', hobl, hsm, hru, hnext⟩ := hprobe hj
                      have hconsProbe :
                          Choices.consume [pick] (r0 :: r1 :: rest').length
                            = (pick, []) := by
                        simp only [Choices.consume, Prod.mk.injEq]
                        refine ⟨Nat.mod_eq_of_lt ?_, trivial⟩
                        omega
                      have hinto : stepThreadInto m i [] = .ok (m', []) := by
                        unfold stepMulti at hsm
                        rw [hti] at hsm
                        dsimp only at hsm
                        rw [if_pos hb, hrs] at hsm
                        dsimp only at hsm
                        simp only [hconsProbe, hget] at hsm
                        exact hsm
                      obtain ⟨ts₂, s₂, hst, hm'⟩ :
                          ∃ ts₂ s₂,
                            stepThread m.shared m.threads i []
                              = .ok (ts₂, s₂, [])
                            ∧ m' = ⟨ts₂, s₂, i⟩ := by
                        unfold stepThreadInto at hinto
                        simp only [bind_eq_ok] at hinto
                        obtain ⟨⟨ts₂, s₂, chr⟩, hst, hinto⟩ := hinto
                        simp only [pure_eq_ok, Except.ok.injEq,
                          Prod.mk.injEq] at hinto
                        obtain ⟨rfl, rfl⟩ := hinto
                        exact ⟨ts₂, s₂, hst, rfl⟩
                      obtain ⟨-, hallst⟩ := stepThread_oblivious hobl hst
                      have hreal : stepMulti m ch = .ok (m', tail) := by
                        unfold stepMulti
                        rw [hti]
                        dsimp only
                        rw [if_pos hb, hrs]
                        dsimp only
                        rw [hcons]
                        dsimp only
                        rw [hget]
                        dsimp only
                        unfold stepThreadInto
                        rw [hallst tail]
                        subst hm'
                        rfl
                      exact hfinish hobl hru hnext hreal (by rw [hm'])
              · rw [if_neg hb] at hall
                obtain ⟨m', r', hobl, hsm, hru, hnext⟩ := hprobe hall
                have hinto : stepThreadInto m m.cur [] = .ok (m', []) := by
                  unfold stepMulti at hsm
                  rw [hti] at hsm
                  dsimp only at hsm
                  rw [if_neg hb] at hsm
                  exact hsm
                obtain ⟨ts₂, s₂, hst, hm'⟩ :
                    ∃ ts₂ s₂,
                      stepThread m.shared m.threads m.cur []
                        = .ok (ts₂, s₂, [])
                      ∧ m' = ⟨ts₂, s₂, m.cur⟩ := by
                  unfold stepThreadInto at hinto
                  simp only [bind_eq_ok] at hinto
                  obtain ⟨⟨ts₂, s₂, chr⟩, hst, hinto⟩ := hinto
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hinto
                  obtain ⟨rfl, rfl⟩ := hinto
                  exact ⟨ts₂, s₂, hst, rfl⟩
                obtain ⟨-, hallst⟩ := stepThread_oblivious hobl hst
                have hreal : stepMulti m ch = .ok (m', ch) := by
                  unfold stepMulti
                  rw [hti]
                  dsimp only
                  rw [if_neg hb]
                  unfold stepThreadInto
                  rw [hallst ch]
                  subst hm'
                  rfl
                exact hfinish hobl hru hnext hreal (by rw [hm'])

/-- Fuel monotonicity of the pool driver: a completed run is stable
under more fuel (the classification arms precede the fuel check —
`execStmt_mono`'s pool twin, what lifts a kernel-checked bound to
every larger fuel in `TerminatesC`-shaped statements). -/
theorem execProgLoop_mono :
    ∀ {fuel : Nat} {m : MultiConfig} {r : RaceState} {ch : Choices}
      {out : ExecOutcome} {ch' : Choices} {fuel' : Nat},
      execProgLoop fuel m r ch = .ok (out, ch') → fuel ≤ fuel' →
      execProgLoop fuel' m r ch = .ok (out, ch') := by
  intro fuel
  induction fuel with
  | zero =>
    intro m r ch out ch' fuel' h hle
    rw [execProgLoop_unfold] at h
    rw [execProgLoop_unfold]
    by_cases hemp : m.threads.isEmpty
    · rw [if_pos hemp] at h; cases h
    · rw [if_neg hemp] at h
      rw [if_neg hemp]
      cases hp : m.panicMsg? with
      | some msg => rw [hp] at h; cases h
      | none =>
        rw [hp] at h
        cases hm : m.mainOutcome? with
        | some o =>
          rw [hm] at h
          exact h
        | none =>
          rw [hm] at h
          by_cases hrun : (runnableIdxs m.shared m.threads).isEmpty
          · rw [if_pos hrun] at h; cases h
          · rw [if_neg hrun] at h
            simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ n ih =>
    intro m r ch out ch' fuel' h hle
    cases fuel' with
    | zero => omega
    | succ n' =>
      rw [execProgLoop_unfold] at h
      rw [execProgLoop_unfold]
      by_cases hemp : m.threads.isEmpty
      · rw [if_pos hemp] at h; cases h
      · rw [if_neg hemp] at h
        rw [if_neg hemp]
        cases hp : m.panicMsg? with
        | some msg => rw [hp] at h; cases h
        | none =>
          rw [hp] at h
          cases hm : m.mainOutcome? with
          | some o =>
            rw [hm] at h
            exact h
          | none =>
            rw [hm] at h
            by_cases hrun : (runnableIdxs m.shared m.threads).isEmpty
            · rw [if_pos hrun] at h; cases h
            · rw [if_neg hrun] at h
              rw [if_neg hrun]
              dsimp only at h ⊢
              cases hsm : stepMulti m ch with
              | error e =>
                rw [hsm] at h
                simp [Bind.bind, Except.bind] at h
              | ok p =>
                obtain ⟨m', ch₁⟩ := p
                rw [hsm] at h
                simp only [Bind.bind, Except.bind] at h ⊢
                cases hru : raceUpdate m.shared m.threads ch m' r with
                | error e =>
                  rw [hru] at h
                  simp at h
                | ok r' =>
                  rw [hru] at h
                  exact ih h (by omega)

end GoLean.GoCore.Machine
