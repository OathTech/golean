import GoLean.GoCore.EnumDedupCheck
import GoLean.GoCore.MachineEqb

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
theorem stepThread_l4_run {s : ExecState} {ts : Array Thread} {i : Nat}
    {c bc : Config} {cs : List (Nat × PairTarget)}
    (hti : ts[i]? = some (.running c none))
    (hblc : isBlockedConfig c = false)
    (hab : c.abort? = none)
    (hsp : spawnPlan c = none)
    (harr : arrivalCases s ts i c = .ok (.single bc cs))
    (hlen : 2 ≤ cs.length)
    {p : Nat} (hplt : p < cs.length)
    {ts' : Array Thread} {s' : ExecState} {ev : StepEvent}
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
  simp only [hblc, Bool.false_eq_true, reduceIte, hab, hsp] at hvec
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
      simp only [hblc, Bool.false_eq_true, reduceIte, hab, hsp,
        Bind.bind, Except.bind, arrivalPlan_of_single (ch := ch) harr]
      try dsimp only
      rw [hconsE]
      try dsimp only
      rw [hget]
      dsimp only
      rw [hpair]
      rfl

-- (`except_bind_ok` and `bind_pair_stream` moved to MachineSound with the B8
-- consumption lemmas; used here as before.)

/-- **N-APP determinization**: a NON-SPILLING `appendSlice` apply is
stream-oblivious — `applyStmtOp` returns the stream verbatim and the
state result is stream-independent. -/
theorem applyStmtOp_append_nospill {s : ExecState} {vs : List GoValue}
    {elem : GoCore.Ty} {nt : Nat}
    (h : appendApplyNoSpill s vs = true) :
    ∀ ch : Choices, applyStmtOp s ch (.appendSlice elem) nt vs
      = (match applyStmtOp s [] (.appendSlice elem) nt vs with
         | .ok (s', _) => .ok (s', ch)
         | .error e => .error e) := by
  intro ch
  match vs, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | _ :: _ :: _ :: _ :: _, _ => rfl
  | [tv, sliceV, elemsV], h =>
    unfold applyStmtOp
    dsimp only
    cases hsl : valueAsSlice sliceV with
    | error e => rfl
    | ok slice =>
      simp only [except_bind_ok]
      cases hel : valueAsSlice elemsV with
      | error e => rfl
      | ok elems =>
        simp only [except_bind_ok]
        cases hv1 : validateSlice slice with
        | error e => rfl
        | ok u1 =>
          simp only [except_bind_ok]
          cases hv2 : validateSlice elems with
          | error e => rfl
          | ok u2 =>
            simp only [except_bind_ok]
            cases hvis : sliceVisibleValues s elems with
            | error e => rfl
            | ok elemValues =>
              simp only [except_bind_ok]
              cases htl : valueAsLoc tv with
              | error e => rfl
              | ok tloc =>
                simp only [except_bind_ok]
                by_cases hcap : slice.len + elemValues.size ≤ slice.cap
                · simp only [if_pos hcap]
                  exact bind_pair_stream _ _ ch
                · exfalso
                  unfold appendApplyNoSpill at h
                  simp only [hsl, hel, hvis, decide_eq_true_eq] at h
                  exact hcap h

/-- `stepFn` at a non-spilling `appendSlice` apply position is
stream-oblivious (the N-APP class's `stepFn` half). -/
theorem stepFn_append_nospill {s : ExecState} {v : GoValue}
    {elem : GoCore.Ty} {nt : Nat} {done : List GoValue} {env : LocalEnv}
    {k : Cont}
    (hns : appendApplyNoSpill s ((v :: done).reverse) = true) :
    ∀ ch : Choices,
      stepFn s (.retV v (.stmtOpK (.appendSlice elem) nt done [] env k)) ch
        = (match stepFn s
              (.retV v (.stmtOpK (.appendSlice elem) nt done [] env k)) [] with
           | .ok (c', s', _) => .ok (c', s', ch)
           | .error e => .error e) := by
  intro ch
  unfold stepFn
  dsimp only
  rw [applyStmtOp_append_nospill hns ch]
  cases hap : applyStmtOp s [] (.appendSlice elem) nt ((v :: done).reverse) with
  | error e => cases_stop e <;> rfl
  | ok p =>
    obtain ⟨s₂, ch₂⟩ := p
    rfl

/-- N-APP obliviousness at the `stepThread` level: mirrors
`stepThread_oblivious`'s conclusion for the non-spilling append apply
shape. -/
theorem stepThread_append_oblivious {s : ExecState} {ts : Array Thread}
    {i : Nat} {v : GoValue} {elem : GoCore.Ty} {nt : Nat}
    {done : List GoValue} {env : LocalEnv} {k : Cont}
    (hti : ts[i]? = some (.running (.retV v (.stmtOpK (.appendSlice elem) nt done [] env k)) none))
    (hns : appendApplyNoSpill s ((v :: done).reverse) = true)
    {ch₀ : Choices} {ts' : Array Thread} {s' : ExecState} {ch₀' : Choices}
    {ev : StepEvent}
    (h : stepThread s ts i ch₀ = .ok (ts', s', ch₀', ev)) :
    ch₀' = ch₀
      ∧ ∀ ch : Choices, stepThread s ts i ch = .ok (ts', s', ch, ev) := by
  have harr : arrivalCases s ts i
      (.retV v (.stmtOpK (.appendSlice elem) nt done [] env k))
      = .ok .cellPath := rfl
  have hsel : selectApplyPlan
      (.retV v (.stmtOpK (.appendSlice elem) nt done [] env k)) = none := rfl
  clear hsel
  unfold stepThread at h
  rw [hti] at h
  simp only [isBlockedConfig, Config.abort?, spawnPlan, Bool.false_eq_true,
    reduceIte] at h
  rw [arrivalPlan_of_cellPath (ch := ch₀) harr] at h
  simp only [except_bind_ok] at h
  try dsimp only at h
  simp only [selectApplyPlan] at h
  try dsimp only at h
  rw [stepFn_append_nospill hns ch₀] at h
  cases hbase : stepFn s
      (.retV v (.stmtOpK (.appendSlice elem) nt done [] env k)) [] with
  | error e =>
    rw [hbase] at h
    dsimp only at h
    cases h
  | ok p =>
    obtain ⟨cB, sB, chB⟩ := p
    rw [hbase] at h
    simp only [except_bind_ok] at h
    try dsimp only at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    unfold stepThread
    rw [hti]
    simp only [isBlockedConfig, Config.abort?, spawnPlan, Bool.false_eq_true,
      reduceIte]
    rw [arrivalPlan_of_cellPath (ch := ch) harr]
    simp only [except_bind_ok]
    try dsimp only
    simp only [selectApplyPlan]
    try dsimp only
    rw [stepFn_append_nospill hns ch, hbase]
    simp only [except_bind_ok]
    try dsimp only
    rfl

/-- Inner total coverage: at a certified target whose explicit
suffixes ALL step successfully, EVERY stream's goroutine-step succeeds
and matches one of them (same successor and event; the stream's
unconsumed tail returned). -/
theorem stepThread_total_covered {s : ExecState} {ts : Array Thread}
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
    | some t =>
      rw [hti] at hiv
      rcases t with ⟨c, b⟩ | msg
      case aborted => simp at hiv
      cases b with
      | some site => simp at hiv
      | none =>
      dsimp only at hiv
      cases hblc : isBlockedConfig c with
      | true => rw [hblc] at hiv; simp at hiv
      | false =>
        rw [hblc] at hiv
        simp only [Bool.false_eq_true, reduceIte] at hiv
        cases hab : c.abort? with
        | some p => rw [hab] at hiv; simp at hiv
        | none =>
          rw [hab] at hiv
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
              | true =>
                rw [hnapp] at hiv
                simp only [reduceIte] at hiv
                split at hiv
                next v elem nt done env k =>
                  split at hiv
                  next hns =>
                    simp only [Option.some.injEq] at hiv
                    subst hiv
                    obtain ⟨ts', s', ev, hv⟩ := hedges [] (by simp)
                    obtain ⟨-, hall⟩ :=
                      stepThread_append_oblivious hti hns hv
                    exact ⟨[], by simp, ts', s', ev, ch, hv, hall ch⟩
                  next => cases hiv
                next => cases hiv
              | false =>
                rw [hnapp] at hiv
                simp only [Bool.false_eq_true, reduceIte] at hiv
                -- Q-TRYLOCK: the TRY heads' apply is refused (`none`).
                cases hntl : consumesTryLock c with
                | true => rw [hntl] at hiv; simp at hiv
                | false =>
                rw [hntl] at hiv
                simp only [Bool.false_eq_true, reduceIte] at hiv
                cases hnmi : isMapIterNext c with
                | true => rw [hnmi] at hiv; simp at hiv
                | false =>
                  rw [hnmi] at hiv
                  simp only [Bool.false_eq_true, reduceIte] at hiv
                  cases hnnv : consumesNilValueMethod s c with
                  | true => rw [hnnv] at hiv; simp at hiv
                  | false =>
                  rw [hnnv] at hiv
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
                          stepThread_l4_run hti hblc hab hsp harr hlen
                            hplt hv hcons⟩
                      · rw [if_neg hlen] at hiv; cases hiv

/-- `slotVecsAux`'s membership property: each menu position's inner
suffixes are present, slot-prefixed. -/
theorem slotVecsAux_mem {s : ExecState} {ts : Array Thread} :
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
  | some t =>
    rw [hti] at hv
    dsimp only at hv
    by_cases hb : t.atBoundary = true
    · rw [if_pos hb] at hv
      cases hrs : schedSlots m.shared m.threads m.cur t.boundarySite with
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
            rw [show Choices.consumeAtE t.boundarySite [r0].length v
                = (0, v, [])
              from Choices.consumeAtE_le_one (by simp)] at hsm
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
            rw [show Choices.consumeAtE t.boundarySite [r0].length v
                = (0, v, [])
              from Choices.consumeAtE_le_one (by simp)]
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
            rw [show Choices.consumeAtE t.boundarySite [r0].length ch
                = (0, ch, [])
              from Choices.consumeAtE_le_one (by simp)]
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
              Choices.consumeAtE t.boundarySite
                  (r0 :: r1 :: rest').length (pick :: v)
                = (pick, v,
                   [⟨t.boundarySite, (r0 :: r1 :: rest').length, pick⟩]) := by
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
                ⟨t.boundarySite, (r0 :: r1 :: rest').length, pick⟩
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
            rw [show Choices.consumeAtE t.boundarySite
                  (r0 :: r1 :: rest').length ch
                = (pick, tail₀,
                   [⟨t.boundarySite, (r0 :: r1 :: rest').length, pick⟩])
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


/-! ## The driver: soundness and completeness of `checkCert` -/

theorem Obs.eqb_sound {a b : Obs} (h : Obs.eqb a b = true) : a = b := by
  cases a <;> cases b <;> (try exact Bool.noConfusion h)
  case ok.ok vs ws =>
    cases eqbListP_sound (fun _ _ hh => GoValue.eqb_sound hh)
      (show eqbListP GoValue.eqb vs ws = true from h)
    rfl
  case terminal.terminal x y =>
    cases eq_of_beq (show (x == y) = true from h)
    rfl

theorem obsMem_mem {mems : Array (Obs × Choices × Nat)} {o : Obs}
    (h : obsMem mems o = true) : o ∈ mems.toList.map (·.1) := by
  unfold obsMem at h
  rw [List.any_eq_true] at h
  obtain ⟨t, htm, hq⟩ := h
  cases Obs.eqb_sound hq
  exact List.mem_map.mpr ⟨t, htm, rfl⟩

/-- Extract `checkStep`'s content: certified vectors exist, indices
align, and every edge checks. -/
theorem checkStep_parts {nodeEqb : DedupNode → DedupNode → Bool}
    {mems : Array (Obs × Choices × Nat)} {nodes : Array DedupNode}
    {succs : Array Nat} {nd : DedupNode}
    (h : checkStep nodeEqb mems nodes succs nd = true) :
    ∃ vecs, nodeVecs nd.m = some vecs
      ∧ vecs.length = succs.size
      ∧ ∀ (j : Nat) (vec : List Nat), vecs[j]? = some vec →
          ∃ kj, succs[j]? = some kj
            ∧ checkEdge nodeEqb mems nodes nd vec kj = true := by
  unfold checkStep at h
  cases hv : nodeVecs nd.m with
  | none => rw [hv] at h; cases h
  | some vecs =>
    rw [hv] at h
    dsimp only at h
    rw [Bool.and_eq_true] at h
    obtain ⟨hlen, hall⟩ := h
    rw [List.all_eq_true] at hall
    refine ⟨vecs, rfl, by simpa using hlen, ?_⟩
    intro (j : Nat) vec hj
    have hjlt : j < vecs.length := by
      rw [List.getElem?_eq_some_iff] at hj
      exact hj.1
    have := hall j (by simpa using List.mem_range.mpr hjlt)
    rw [hj] at this
    cases hsk : succs[j]? with
    | none => rw [hsk] at this; cases this
    | some kj =>
      rw [hsk] at this
      exact ⟨kj, rfl, this⟩

/-- The per-edge successes `stepMulti_total_covered` consumes, from a
passed `checkStep`. -/
theorem checkStep_edges {nodeEqb : DedupNode → DedupNode → Bool}
    {mems : Array (Obs × Choices × Nat)} {nodes : Array DedupNode}
    {succs : Array Nat} {nd : DedupNode} {vecs : List (List Nat)}
    (_hv : nodeVecs nd.m = some vecs)
    (hparts : ∀ (j : Nat) (vec : List Nat), vecs[j]? = some vec →
      ∃ kj, succs[j]? = some kj
        ∧ checkEdge nodeEqb mems nodes nd vec kj = true) :
    ∀ vec ∈ vecs, ∃ m' ev, stepMulti nd.m vec = .ok (m', [], ev) := by
  intro vec hvm
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hvm
  obtain ⟨kj, -, hedge⟩ := hparts j vec hj
  unfold checkEdge at hedge
  cases hsm : stepMulti nd.m vec with
  | error e => rw [hsm] at hedge; cases hedge
  | ok p =>
    obtain ⟨m', chRem, ev⟩ := p
    rw [hsm] at hedge
    dsimp only at hedge
    rw [Bool.and_eq_true] at hedge
    obtain ⟨hemp, -⟩ := hedge
    have : chRem = [] := by
      cases chRem with
      | nil => rfl
      | cons a l => simp [List.isEmpty] at hemp
    subst this
    exact ⟨m', ev, rfl⟩

set_option maxHeartbeats 1600000 in
/-- **Completeness** (the dangerous direction): from any certificate
node, any stream's observation at any fuel is a member. Induction on
fuel; the step arm rides `stepMulti_total_covered` — the run's step is
determined by a checked vector's, so the successor is a certificate
node (or the race refusal, a member). -/
theorem checkCert_complete_aux
    {nodeEqb : DedupNode → DedupNode → Bool}
    (hEqb : ∀ a b, nodeEqb a b = true → a = b)
    {resultLocs : List Loc} {cert : DedupCert}
    (hsz : cert.succ.size = cert.nodes.size)
    (hall : ∀ (k : Nat) (nd : DedupNode) (succs : Array Nat), cert.nodes[k]? = some nd →
      cert.succ[k]? = some succs →
      checkNode nodeEqb cert.members cert.nodes resultLocs succs nd = true) :
    ∀ (fuel : Nat) (m : MultiConfig) (r : RaceState),
      (∃ k : Nat, cert.nodes[k]? = some ⟨m, r⟩) →
      ∀ (ch : Choices) (o : Obs),
        obsOf? resultLocs (execProgLoop fuel m r ch) = some o →
        o ∈ cert.obsSet := by
  intro fuel
  induction fuel with
  | zero =>
    intro m r hin ch o hobs
    obtain ⟨k, hk⟩ := hin
    have hklt : k < cert.nodes.size := by
      rw [Array.getElem?_eq_some_iff] at hk
      exact hk.1
    obtain ⟨succs, hsk⟩ : ∃ succs, cert.succ[k]? = some succs :=
      ⟨cert.succ[k]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
    have hnode := hall k ⟨m, r⟩ succs hk hsk
    unfold checkNode at hnode
    rw [execProgLoop_unfold] at hobs
    try dsimp only at hobs
    dsimp only at hnode
    by_cases hemp : m.threads.isEmpty
    · rw [if_pos hemp] at hnode; cases hnode
    · rw [if_neg hemp] at hnode
      rw [if_neg hemp] at hobs
      try dsimp only at hobs
      cases hp : m.panicMsg? with
      | some msg =>
        rw [hp] at hnode hobs
        try dsimp only at hnode hobs
        simp only [obsOf?, throw, throwThe, MonadExceptOf.throw,
          Option.some.injEq] at hobs
        cases hobs
        exact obsMem_mem hnode
      | none =>
        rw [hp] at hnode hobs
        try dsimp only at hnode hobs
        cases hm : m.mainOutcome? with
        | some σf =>
          rw [hm] at hnode hobs
          try dsimp only at hnode hobs
          try dsimp only at hnode hobs
          cases hload : loadMany σf resultLocs with
          | error e =>
            rw [hload] at hnode; cases hnode
          | ok vs =>
            rw [hload] at hnode
            try dsimp only at hnode
            cases hrs : runnableIdxs m.shared m.threads with
            | nil =>
              rw [hrs] at hnode hobs
              try dsimp only at hnode hobs
              simp only [obsOf?, pure_eq_ok] at hobs
              rw [hload] at hobs
              simp only [Option.some.injEq] at hobs
              cases hobs
              exact obsMem_mem hnode
            | cons r0 rest =>
              rw [hrs] at hnode hobs
              try dsimp only at hnode hobs
              try dsimp only at hobs
              rcases hcons : Choices.consume ch 2 with ⟨pick, ch₁⟩
              rw [hcons] at hobs
              try dsimp only at hobs
              try dsimp only at hobs
              rw [Bool.and_eq_true] at hnode
              try dsimp only at hnode
              obtain ⟨hmem, -⟩ := hnode
              by_cases hpick : (pick == 0) = true
              · rw [if_pos hpick] at hobs
                simp only [obsOf?, pure_eq_ok] at hobs
                rw [hload] at hobs
                simp only [Option.some.injEq] at hobs
                cases hobs
                exact obsMem_mem hmem
              · rw [if_neg hpick] at hobs
                simp [obsOf?, throw, throwThe, MonadExceptOf.throw] at hobs
        | none =>
          rw [hm] at hnode hobs
          try dsimp only at hnode hobs
          by_cases hrun : (runnableIdxs m.shared m.threads).isEmpty
          · rw [if_pos hrun] at hnode; cases hnode
          · rw [if_neg hrun] at hnode
            rw [if_neg hrun] at hobs
            try dsimp only at hobs
            simp [obsOf?, throw, throwThe, MonadExceptOf.throw] at hobs
  | succ n ih =>
    intro m r hin ch o hobs
    obtain ⟨k, hk⟩ := hin
    have hklt : k < cert.nodes.size := by
      rw [Array.getElem?_eq_some_iff] at hk
      exact hk.1
    obtain ⟨succs, hsk⟩ : ∃ succs, cert.succ[k]? = some succs :=
      ⟨cert.succ[k]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
    have hnode := hall k ⟨m, r⟩ succs hk hsk
    unfold checkNode at hnode
    rw [execProgLoop_unfold] at hobs
    try dsimp only at hobs
    dsimp only at hnode
    -- the shared STEP argument, used by both stepping arms below
    have hstepArm : ∀ (chS : Choices),
        checkStep nodeEqb cert.members cert.nodes succs ⟨m, r⟩ = true →
        obsOf? resultLocs
          ((do
            let x ← stepMulti m chS
            match x with
            | (m', choices', ev) => do
                let r' ← raceUpdate m.shared m.threads ev m' r
                execProgLoop n m' r' choices')
           : Except Stop (ExecState × Choices)) = some o →
        o ∈ cert.obsSet := by
      intro chS hstep hobs'
      obtain ⟨vecs, hv, -, hparts⟩ := checkStep_parts hstep
      have hedges := checkStep_edges hv hparts
      obtain ⟨vec, hvm, m', ev, tail, hvstep, hchstep⟩ :=
        stepMulti_total_covered hv hedges chS
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hvm
      obtain ⟨kj, hkj, hedge⟩ := hparts j vec hj
      unfold checkEdge at hedge
      rw [hvstep] at hedge
      dsimp only at hedge
      rw [Bool.and_eq_true] at hedge
      obtain ⟨-, hedge⟩ := hedge
      rw [hchstep] at hobs'
      simp only [Bind.bind, Except.bind] at hobs'
      cases hru : raceUpdate m.shared m.threads ev m' r with
      | ok r' =>
        rw [hru] at hedge hobs'
        dsimp only at hedge
        cases hnd : cert.nodes[kj]? with
        | none => rw [hnd] at hedge; cases hedge
        | some ndS =>
          rw [hnd] at hedge
          cases hEqb _ _ hedge
          exact ih m' r' ⟨kj, hnd⟩ tail o hobs'
      | error e =>
        rw [hru] at hedge hobs'
        cases_stop e
        case raceDetected =>
          simp only [obsOf?, Option.some.injEq] at hobs'
          cases hobs'
          exact obsMem_mem hedge
        all_goals cases hedge
    by_cases hemp : m.threads.isEmpty
    · rw [if_pos hemp] at hnode; cases hnode
    · rw [if_neg hemp] at hnode
      rw [if_neg hemp] at hobs
      try dsimp only at hobs
      cases hp : m.panicMsg? with
      | some msg =>
        rw [hp] at hnode hobs
        try dsimp only at hnode hobs
        simp only [obsOf?, throw, throwThe, MonadExceptOf.throw,
          Option.some.injEq] at hobs
        cases hobs
        exact obsMem_mem hnode
      | none =>
        rw [hp] at hnode hobs
        try dsimp only at hnode hobs
        cases hm : m.mainOutcome? with
        | some σf =>
          rw [hm] at hnode hobs
          try dsimp only at hnode hobs
          try dsimp only at hnode hobs
          cases hload : loadMany σf resultLocs with
          | error e =>
            rw [hload] at hnode; cases hnode
          | ok vs =>
            rw [hload] at hnode
            try dsimp only at hnode
            cases hrs : runnableIdxs m.shared m.threads with
            | nil =>
              rw [hrs] at hnode hobs
              try dsimp only at hnode hobs
              simp only [obsOf?, pure_eq_ok] at hobs
              rw [hload] at hobs
              simp only [Option.some.injEq] at hobs
              cases hobs
              exact obsMem_mem hnode
            | cons r0 rest =>
              rw [hrs] at hnode hobs
              try dsimp only at hnode hobs
              try dsimp only at hobs
              rcases hcons : Choices.consume ch 2 with ⟨pick, ch₁⟩
              rw [hcons] at hobs
              try dsimp only at hobs
              try dsimp only at hobs
              rw [Bool.and_eq_true] at hnode
              try dsimp only at hnode
              obtain ⟨hmem, hstep⟩ := hnode
              by_cases hpick : (pick == 0) = true
              · rw [if_pos hpick] at hobs
                simp only [obsOf?, pure_eq_ok] at hobs
                rw [hload] at hobs
                simp only [Option.some.injEq] at hobs
                cases hobs
                exact obsMem_mem hmem
              · rw [if_neg hpick] at hobs
                exact hstepArm ch₁ hstep hobs
        | none =>
          rw [hm] at hnode hobs
          try dsimp only at hnode hobs
          by_cases hrun : (runnableIdxs m.shared m.threads).isEmpty
          · rw [if_pos hrun] at hnode; cases hnode
          · rw [if_neg hrun] at hnode
            rw [if_neg hrun] at hobs
            try dsimp only at hobs
            exact hstepArm ch hnode hobs

/-- **THE THEOREM** (design note §4; the binding constraint's shape):
an accepted certificate's member set EQUALS the slow semantics'
observation set — soundness by witness replay, completeness by the
fuel induction over the certified graph. `hEqb` is the node equality's
soundness (discharged by `dedupNodeEqb_sound`, `MachineEqb.lean`). -/
theorem checkCert_slowObs
    {nodeEqb : DedupNode → DedupNode → Bool}
    (hEqb : ∀ a b, nodeEqb a b = true → a = b)
    {resultLocs : List Loc} {m₀ : MultiConfig} {r₀ : RaceState}
    {cert : DedupCert}
    (hc : checkCert nodeEqb resultLocs m₀ r₀ cert = true) :
    ∀ o : Obs, o ∈ cert.obsSet ↔ SlowObs resultLocs m₀ r₀ o := by
  unfold checkCert at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hroot, hsz⟩, hnodes⟩, hwits⟩ := hc
  have hsz' : cert.succ.size = cert.nodes.size := by simpa using hsz
  rw [List.all_eq_true] at hnodes
  have hall : ∀ (k : Nat) (nd : DedupNode) (succs : Array Nat), cert.nodes[k]? = some nd →
      cert.succ[k]? = some succs →
      checkNode nodeEqb cert.members cert.nodes resultLocs succs nd
        = true := by
    intro k nd succs hk hsk
    have hklt : k < cert.nodes.size := by
      rw [Array.getElem?_eq_some_iff] at hk
      exact hk.1
    have := hnodes k (by simpa using List.mem_range.mpr hklt)
    rw [hk, hsk] at this
    exact this
  intro o
  constructor
  · -- soundness: the witness replay
    intro hmem
    rw [List.all_eq_true] at hwits
    unfold DedupCert.obsSet at hmem
    rw [List.mem_map] at hmem
    obtain ⟨t, htm, hto⟩ := hmem
    have := hwits t htm
    unfold obsOfEqb at this
    cases hrep : obsOf? resultLocs
        (execProgLoop t.2.2 m₀ r₀ t.2.1) with
    | none => rw [hrep] at this; cases this
    | some a =>
      rw [hrep] at this
      cases Obs.eqb_sound this
      exact ⟨t.2.2, t.2.1, hto ▸ hrep⟩
  · -- completeness
    intro hslow
    obtain ⟨fuel, ch, hobs⟩ := hslow
    cases hnd0 : cert.nodes[0]? with
    | none => rw [hnd0] at hroot; cases hroot
    | some nd0 =>
      rw [hnd0] at hroot
      cases hEqb _ _ hroot
      exact checkCert_complete_aux hEqb hsz' hall fuel m₀ r₀
        ⟨0, hnd0⟩ ch o hobs

/-- The instantiated headline: the CONCRETE checker (the sound
state-tower node equality plugged in) — what the CLI's
`--engine dedup` path evaluates. A `true` here IS the set-equality
claim over the slow semantics. -/
theorem checkCertM_slowObs {resultLocs : List Loc} {m₀ : MultiConfig}
    {r₀ : RaceState} {cert : DedupCert}
    (hc : checkCert dedupNodeEqb resultLocs m₀ r₀ cert = true) :
    ∀ o : Obs, o ∈ cert.obsSet ↔ SlowObs resultLocs m₀ r₀ o :=
  checkCert_slowObs (nodeEqb := dedupNodeEqb)
    (fun a b h => dedupNodeEqb_sound a b h) hc

end GoLean.GoCore.Machine
