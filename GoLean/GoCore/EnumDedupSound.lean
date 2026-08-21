import GoLean.GoCore.EnumDedupCheck

/-!
# Dedup-checker soundness (POR slice P3 — the theorem)

`checkCert = true` ⟹ the certificate's member set EQUALS `SlowObs`
(design note `docs/2026-08-21_w32-por-design.md` §4). The two halves:

- **Total coverage (completeness's engine):** at a certified-shape
  node whose explicit branch vectors ALL step successfully (what
  `checkEdge` verified), EVERY stream's `stepMulti` succeeds and
  matches one of them — same successor, same event
  (`stepMulti_total_covered`). Stated vec→run (from the checker's
  successes to the arbitrary stream) so the completeness induction
  never needs a "`stepFn` cannot throw `.panic`" walk: the run's step
  is DETERMINED by the matched vector's. The N-OBL class rides
  `stepThread_oblivious` (MultiStreams); the N-L4 class rides the new
  one-pick determinization `stepThread_l4_run`.
- **The driver induction** (`checkCert_complete`): any stream, any
  fuel, from any certificate node — the run's observation is a
  member. Soundness (`checkCert_sound`) is the witnesses' replay.
-/

namespace GoLean.GoCore.Machine

open GoLean

set_option linter.unusedSimpArgs false

/-- **N-L4 pick determinization** (the one-pick analogue of
`stepThread_oblivious`, vec→run direction): at a single-arrival
multi-candidate pairing shape, a SUCCESSFUL explicit-pick step `[p]`
determines the step under every stream whose L4 draw reduces to `p` —
same successor, same state, same event, the stream's tail returned. -/
theorem stepThread_l4_run {s : ExecState} {ts : Array Config} {i : Nat}
    {c bc : Config} {cs : List (Nat × PairTarget)}
    (hti : ts[i]? = some c)
    (hblc : isBlockedConfig c = false)
    (hsc : opDoneInner c = none)
    (hsp : spawnPlan c = none)
    (harr : arrivalCases s ts i c = .ok (.single bc cs))
    (hlen : 2 ≤ cs.length)
    {p : Nat} (hplt : p < cs.length)
    {ts' : Array Config} {s' : ExecState} {ev : StepEvent}
    (hvec : stepThread s ts i [p] = .ok (ts', s', [], ev)) :
    ∀ {ch rest : Choices}, Choices.consume ch cs.length = (p, rest) →
      stepThread s ts i ch = .ok (ts', s', rest, ev) := by
  intro ch rest hcons
  have hlt : 1 < cs.length := by omega
  have hcP : Choices.consume [p] cs.length = (p, []) := by
    simp only [Choices.consume]
    have hmax : max 1 cs.length = cs.length := by omega
    rw [hmax, Nat.mod_eq_of_lt hplt]
  have hconsE' : Choices.consumeAtE .l4Waiter cs.length [p]
      = (p, [], [⟨.l4Waiter, cs.length, p⟩]) := by
    rw [Choices.consumeAtE_of_lt hlt, hcP]
  have hconsE : Choices.consumeAtE .l4Waiter cs.length ch
      = (p, rest, [⟨.l4Waiter, cs.length, p⟩]) := by
    rw [Choices.consumeAtE_of_lt hlt, hcons]
  unfold stepThread at hvec
  rw [hti] at hvec
  simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp] at hvec
  simp only [bind_eq_ok] at hvec
  obtain ⟨⟨plan, ch₁, ps₁⟩, hplan, hvec⟩ := hvec
  rw [arrivalPlan_of_single (ch := [p]) harr] at hplan
  simp only [Except.ok.injEq, Prod.mk.injEq] at hplan
  obtain ⟨hp1, hp2, hp3⟩ := hplan
  subst hp1; subst hp2; subst hp3
  cases cs with
  | nil => simp at hlen
  | cons c0 cs' =>
    dsimp only at hvec
    rw [hconsE'] at hvec
    try dsimp only at hvec
    cases hget : (c0 :: cs')[p]? with
    | none =>
      rw [hget] at hvec
      simp [throw, throwThe, MonadExceptOf.throw] at hvec
    | some cand =>
      rw [hget] at hvec
      simp only [bind_eq_ok] at hvec
      obtain ⟨⟨ts₂, s₂⟩, hpair, hvec⟩ := hvec
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hvec
      obtain ⟨h1, h2, -, h4⟩ := hvec
      subst h1; subst h2; subst h4
      unfold stepThread
      rw [hti]
      simp only [hblc, Bool.false_eq_true, reduceIte, hsc, hsp,
        Bind.bind, Except.bind, arrivalPlan_of_single (ch := ch) harr]
      try dsimp only
      rw [hconsE]
      try dsimp only
      rw [hget]
      dsimp only
      rw [hpair]
      rfl

/-- Inner total coverage: at a certified target whose explicit
suffixes ALL step successfully, EVERY stream's goroutine-step succeeds
and matches one of them (same successor and event; the stream's
unconsumed tail returned). -/
theorem stepThread_total_covered {s : ExecState} {ts : Array Config}
    {i : Nat} {ivs : List (List Nat)}
    (hiv : innerVecs s ts i = some ivs)
    (hedges : ∀ v ∈ ivs, ∃ ts' s' ev,
      stepThread s ts i v = .ok (ts', s', [], ev)) :
    ∀ ch : Choices, ∃ v ∈ ivs, ∃ ts' s' ev tail,
      stepThread s ts i v = .ok (ts', s', [], ev)
      ∧ stepThread s ts i ch = .ok (ts', s', tail, ev) := by
  intro ch
  unfold innerVecs at hiv
  by_cases hobl : poolThreadOblivious s ts i = true
  · rw [if_pos hobl] at hiv
    simp only [Option.some.injEq] at hiv
    subst hiv
    obtain ⟨ts', s', ev, hv⟩ := hedges [] (by simp)
    obtain ⟨-, hall⟩ := stepThread_oblivious hobl hv
    exact ⟨[], by simp, ts', s', ev, ch, hv, hall ch⟩
  · rw [if_neg hobl] at hiv
    cases hti : ts[i]? with
    | none => rw [hti] at hiv; cases hiv
    | some c =>
      rw [hti] at hiv
      dsimp only at hiv
      cases hblc : isBlockedConfig c with
      | true => rw [hblc] at hiv; simp at hiv
      | false =>
        rw [hblc] at hiv
        simp only [Bool.false_eq_true, reduceIte] at hiv
        cases hsc : opDoneInner c with
        | some inner => rw [hsc] at hiv; simp at hiv
        | none =>
          rw [hsc] at hiv
          simp only [Option.isSome_none, Bool.false_eq_true, reduceIte] at hiv
          cases hsp : spawnPlan c with
          | some pl => rw [hsp] at hiv; simp at hiv
          | none =>
            rw [hsp] at hiv
            simp only [Option.isSome_none, Bool.false_eq_true,
              reduceIte] at hiv
            cases hnsel : consumesSelect c with
            | true => rw [hnsel] at hiv; simp at hiv
            | false =>
              rw [hnsel] at hiv
              simp only [Bool.false_eq_true, reduceIte] at hiv
              cases hnapp : consumesAppendSlice c with
              | true => rw [hnapp] at hiv; simp at hiv
              | false =>
                rw [hnapp] at hiv
                simp only [Bool.false_eq_true, reduceIte] at hiv
                cases hnmi : isMapIterNext c with
                | true => rw [hnmi] at hiv; simp at hiv
                | false =>
                  rw [hnmi] at hiv
                  simp only [Bool.false_eq_true, reduceIte] at hiv
                  cases harr : arrivalCases s ts i c with
                  | error e => rw [harr] at hiv; cases hiv
                  | ok a =>
                    rw [harr] at hiv
                    cases a with
                    | cellPath => cases hiv
                    | multi os => cases hiv
                    | single bc cs =>
                      dsimp only at hiv
                      by_cases hlen : 2 ≤ cs.length
                      · rw [if_pos hlen] at hiv
                        simp only [Option.some.injEq] at hiv
                        subst hiv
                        rcases hcons : Choices.consume ch cs.length
                          with ⟨p, rest⟩
                        have hplt : p < cs.length := by
                          have := consume_fst_lt (ch := ch)
                            (bound := cs.length) (by omega)
                          rw [hcons] at this
                          exact this
                        have hpmem : [p] ∈ (List.range cs.length).map
                            (fun q => [q]) := by
                          simp only [List.mem_map, List.mem_range]
                          exact ⟨p, hplt, rfl⟩
                        obtain ⟨ts', s', ev, hv⟩ := hedges [p] hpmem
                        exact ⟨[p], hpmem, ts', s', ev, rest, hv,
                          stepThread_l4_run hti hblc hsc hsp harr hlen
                            hplt hv hcons⟩
                      · rw [if_neg hlen] at hiv; cases hiv

/-- `slotVecsAux`'s membership property: each menu position's inner
suffixes are present, slot-prefixed. -/
theorem slotVecsAux_mem {s : ExecState} {ts : Array Config} :
    ∀ {rs : List Nat} {p₀ : Nat} {out : List (List Nat)},
      slotVecsAux s ts rs p₀ = some out →
      ∀ {j i}, rs[j]? = some i →
        ∃ ivs, innerVecs s ts i = some ivs
          ∧ ∀ v ∈ ivs, ((p₀ + j) :: v) ∈ out := by
  intro rs
  induction rs with
  | nil =>
    intro p₀ out hsv j i hget
    simp at hget
  | cons r rest ih =>
    intro p₀ out hsv j i hget
    unfold slotVecsAux at hsv
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hsv
    obtain ⟨ivs, hivs, tail, htail, hout⟩ := hsv
    subst hout
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      refine ⟨ivs, hivs, fun v hv => ?_⟩
      simp only [Nat.add_zero, List.mem_append, List.mem_map]
      exact .inl ⟨v, hv, rfl⟩
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hget
      obtain ⟨ivs', hivs', hmem⟩ := ih htail hget
      refine ⟨ivs', hivs', fun v hv => ?_⟩
      have hin := hmem v hv
      simp only [List.mem_append]
      right
      have harith : p₀ + 1 + j' = p₀ + (j' + 1) := by omega
      rw [harith] at hin
      exact hin

/-- **Node total coverage** (the completeness induction's engine): at a
node with certified branch vectors that ALL step successfully (what
`checkEdge` verified), EVERY stream's `stepMulti` succeeds and matches
one of them — same successor pool, same event. -/
theorem stepMulti_total_covered {m : MultiConfig} {vecs : List (List Nat)}
    (hv : nodeVecs m = some vecs)
    (hedges : ∀ vec ∈ vecs, ∃ m' ev,
      stepMulti m vec = .ok (m', [], ev)) :
    ∀ ch : Choices, ∃ vec ∈ vecs, ∃ m' ev tail,
      stepMulti m vec = .ok (m', [], ev)
      ∧ stepMulti m ch = .ok (m', tail, ev) := by
  intro ch
  unfold nodeVecs at hv
  cases hti : m.threads[m.cur]? with
  | none => rw [hti] at hv; cases hv
  | some c =>
    rw [hti] at hv
    dsimp only at hv
    by_cases hb : c.atBoundary = true
    · rw [if_pos hb] at hv
      cases hrs : schedSlots m.shared m.threads m.cur c.boundarySite with
      | nil => rw [hrs] at hv; cases hv
      | cons r0 rest =>
        rw [hrs] at hv
        cases rest with
        | nil =>
          try dsimp only at hv
          -- singleton menu: no scheduling consumption on either side.
          -- Convert pool-level edge successes to goroutine-step ones.
          have hedges' : ∀ v ∈ vecs, ∃ ts' s' ev,
              stepThread m.shared m.threads r0 v = .ok (ts', s', [], ev) := by
            intro v hvm
            obtain ⟨m', ev, hsm⟩ := hedges v hvm
            unfold stepMulti at hsm
            rw [hti] at hsm
            dsimp only at hsm
            rw [if_pos hb, hrs] at hsm
            dsimp only at hsm
            rw [show Choices.consumeAtE c.boundarySite [r0].length v
                = (0, v, [])
              from Choices.consumeAtE_le_one (by simp)
                (Config.boundarySite_consumeAtOne c)] at hsm
            simp only [List.getElem?_cons_zero] at hsm
            simp only [bind_eq_ok] at hsm
            obtain ⟨⟨m₂, ch₂, ev₂⟩, hinto, hsm⟩ := hsm
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hsm
            obtain ⟨rfl, rfl, hEv⟩ := hsm
            unfold stepThreadInto at hinto
            simp only [bind_eq_ok] at hinto
            obtain ⟨⟨ts₂, s₂, chr, ev₃⟩, hst, hinto⟩ := hinto
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hinto
            obtain ⟨rfl, rfl, rfl⟩ := hinto
            exact ⟨ts₂, s₂, ev₃, hst⟩
          obtain ⟨v, hvm, ts', s', ev, tail, hvstep, hchstep⟩ :=
            stepThread_total_covered hv hedges' ch
          -- the pool step at a singleton menu adds no pick record
          refine ⟨v, hvm, ⟨ts', s', r0⟩, ev, tail, ?_, ?_⟩
          · unfold stepMulti
            rw [hti]
            dsimp only
            rw [if_pos hb, hrs]
            dsimp only
            rw [show Choices.consumeAtE c.boundarySite [r0].length v
                = (0, v, [])
              from Choices.consumeAtE_le_one (by simp)
                (Config.boundarySite_consumeAtOne c)]
            simp only [List.getElem?_cons_zero]
            simp only [Bind.bind, Except.bind]
            unfold stepThreadInto
            rw [hvstep]
            rfl
          · unfold stepMulti
            rw [hti]
            dsimp only
            rw [if_pos hb, hrs]
            dsimp only
            rw [show Choices.consumeAtE c.boundarySite [r0].length ch
                = (0, ch, [])
              from Choices.consumeAtE_le_one (by simp)
                (Config.boundarySite_consumeAtOne c)]
            simp only [List.getElem?_cons_zero]
            simp only [Bind.bind, Except.bind]
            unfold stepThreadInto
            rw [hchstep]
            rfl
        | cons r1 rest' =>
          try dsimp only at hv
          have hlt2 : 1 < (r0 :: r1 :: rest').length := by
            simp only [List.length_cons]; omega
          rcases hcons : Choices.consume ch (r0 :: r1 :: rest').length
            with ⟨pick, tail₀⟩
          have hpicklt : pick < (r0 :: r1 :: rest').length := by
            have := consume_fst_lt (ch := ch)
              (bound := (r0 :: r1 :: rest').length) (by omega)
            rw [hcons] at this
            exact this
          have hget : (r0 :: r1 :: rest')[pick]?
              = some ((r0 :: r1 :: rest')[pick]) :=
            List.getElem?_eq_getElem hpicklt
          obtain ⟨ivs, hivs, hpref⟩ := slotVecsAux_mem hv hget
          have hconsV : ∀ v : List Nat,
              Choices.consumeAtE c.boundarySite
                  (r0 :: r1 :: rest').length (pick :: v)
                = (pick, v,
                   [⟨c.boundarySite, (r0 :: r1 :: rest').length, pick⟩]) := by
            intro v
            have hcP : Choices.consume (pick :: v)
                (r0 :: r1 :: rest').length = (pick, v) := by
              simp only [Choices.consume]
              have hmax : max 1 (r0 :: r1 :: rest').length
                  = (r0 :: r1 :: rest').length := by
                simp only [List.length_cons]; omega
              rw [hmax, Nat.mod_eq_of_lt hpicklt]
            rw [Choices.consumeAtE_of_lt hlt2, hcP]
          -- pool-edge successes at this slot ⇒ goroutine-step successes
          have hedges' : ∀ v ∈ ivs, ∃ ts' s' ev,
              stepThread m.shared m.threads ((r0 :: r1 :: rest')[pick]) v
                = .ok (ts', s', [], ev) := by
            intro v hvm
            have hmem : (pick :: v) ∈ vecs := by
              have hp := hpref v hvm
              simpa using hp
            obtain ⟨m', ev, hsm⟩ := hedges (pick :: v) hmem
            unfold stepMulti at hsm
            rw [hti] at hsm
            dsimp only at hsm
            rw [if_pos hb, hrs] at hsm
            dsimp only at hsm
            rw [hconsV v] at hsm
            dsimp only at hsm
            rw [hget] at hsm
            dsimp only at hsm
            simp only [bind_eq_ok] at hsm
            obtain ⟨⟨m₂, ch₂, ev₂⟩, hinto, hsm⟩ := hsm
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hsm
            obtain ⟨rfl, rfl, hEv⟩ := hsm
            unfold stepThreadInto at hinto
            simp only [bind_eq_ok] at hinto
            obtain ⟨⟨ts₂, s₂, chr, ev₃⟩, hst, hinto⟩ := hinto
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hinto
            obtain ⟨rfl, rfl, rfl⟩ := hinto
            exact ⟨ts₂, s₂, ev₃, hst⟩
          obtain ⟨v, hvm, ts', s', ev, tail, hvstep, hchstep⟩ :=
            stepThread_total_covered hivs hedges' tail₀
          have hvecmem : (pick :: v) ∈ vecs := by
            have hp := hpref v hvm
            simpa using hp
          refine ⟨pick :: v, hvecmem,
            ⟨ts', s', (r0 :: r1 :: rest')[pick]⟩,
            { ev with picks :=
                ⟨c.boundarySite, (r0 :: r1 :: rest').length, pick⟩
                  :: ev.picks },
            tail, ?_, ?_⟩
          · unfold stepMulti
            rw [hti]
            dsimp only
            rw [if_pos hb, hrs]
            dsimp only
            rw [hconsV v]
            dsimp only
            rw [hget]
            dsimp only
            simp only [Bind.bind, Except.bind]
            unfold stepThreadInto
            rw [hvstep]
            rfl
          · unfold stepMulti
            rw [hti]
            dsimp only
            rw [if_pos hb, hrs]
            dsimp only
            rw [show Choices.consumeAtE c.boundarySite
                  (r0 :: r1 :: rest').length ch
                = (pick, tail₀,
                   [⟨c.boundarySite, (r0 :: r1 :: rest').length, pick⟩])
              from by rw [Choices.consumeAtE_of_lt hlt2, hcons]]
            dsimp only
            rw [hget]
            dsimp only
            simp only [Bind.bind, Except.bind]
            unfold stepThreadInto
            rw [hchstep]
            rfl
    · rw [if_neg hb] at hv
      have hedges' : ∀ v ∈ vecs, ∃ ts' s' ev,
          stepThread m.shared m.threads m.cur v = .ok (ts', s', [], ev) := by
        intro v hvm
        obtain ⟨m', ev, hsm⟩ := hedges v hvm
        unfold stepMulti at hsm
        rw [hti] at hsm
        dsimp only at hsm
        rw [if_neg hb] at hsm
        unfold stepThreadInto at hsm
        simp only [bind_eq_ok] at hsm
        obtain ⟨⟨ts₂, s₂, chr, ev₃⟩, hst, hsm⟩ := hsm
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hsm
        obtain ⟨rfl, rfl, rfl⟩ := hsm
        exact ⟨ts₂, s₂, ev₃, hst⟩
      obtain ⟨v, hvm, ts', s', ev, tail, hvstep, hchstep⟩ :=
        stepThread_total_covered hv hedges' ch
      refine ⟨v, hvm, ⟨ts', s', m.cur⟩, ev, tail, ?_, ?_⟩
      · unfold stepMulti
        rw [hti]
        dsimp only
        rw [if_neg hb]
        unfold stepThreadInto
        rw [hvstep]
        rfl
      · unfold stepMulti
        rw [hti]
        dsimp only
        rw [if_neg hb]
        unfold stepThreadInto
        rw [hchstep]
        rfl

end GoLean.GoCore.Machine
