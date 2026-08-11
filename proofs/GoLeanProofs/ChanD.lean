import GoLeanProofs.LangD

/-!
# The channel WP law family on the D-carrier (channel-logic arc, slice 1)

The first channel-primitive WP laws over the decomposed per-thread
Language (`LangD.lean`), per `docs/2026-08-11_channel-wp-laws.md`. This
slice ships the RENDEZVOUS-CLASS laws — the channel cell pinned by an
Iris invariant to the unbuffered open empty shape
(`chanData #[] 0 false`), the class the exemplar witnesses — plus the
supporting D-carrier lifting cores. The general-`S` family (buffered
cells, close/len/cap under sharing, select) is designed in the note
(§3) and grows from these with its consumers; shipping it without a
witness would be the scaffold smell the non-vacuity gate exists for.

**The wider envelope, absorbed** (note §1a): `StepDC`'s pairing rules
quantify the partner pool existentially, so these laws' continuations
are DISJUNCTIVE over the outcome set — an open-channel send absorbs
both its park and a (possibly phantom) pairing, a receive absorbs
delivery of any value, and a PARKED configuration absorbs the
`pairRelease` self-step (a pairing elsewhere in the ∃-pool leaves the
parked thread untouched — `ts'[j] = p`), which is why the parked laws
are proved by Löb induction. All of it is sound-conservative: a law
here can only make a WP harder to prove, never a false export provable
(the exported judgments quantify `execProg` alone).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open Iris.ProgramLogic.Language.Notation
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open Iris.BI

namespace GoLean.Iris

/-! ## The pure inversion kit

Shape facts about the machine's pairing helpers, consumed by the laws'
step case analyses. All constructive. -/

/-- Delivery entry is state-preserving: the delivered value rides in
the successor configuration; the stores are the receiving thread's own
later steps. -/
theorem resumeRecvDelivery_state {s : ExecState} {v : GoValue} {ok : Bool}
    {targets : List Assignee} {env : LocalEnv} {k : Cont} {c : Config}
    {s' : ExecState}
    (h : resumeRecvDelivery s v ok targets env k = .ok (c, s')) : s' = s := by
  cases targets with
  | nil =>
    simp only [resumeRecvDelivery, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | cons t ts =>
    simp only [resumeRecvDelivery, enterRecvTargets] at h
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2.symm
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-- `selectRecvDelivery` is state-preserving (the select-clause twin). -/
theorem selectRecvDelivery_state {s : ExecState} {v : GoValue} {ok : Bool}
    {targets : List Assignee} {body : Stmt} {env : LocalEnv} {k : Cont}
    {c : Config} {s' : ExecState}
    (h : selectRecvDelivery s v ok targets body env k = .ok (c, s')) : s' = s := by
  cases targets with
  | nil =>
    simp only [selectRecvDelivery, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | cons t ts =>
    simp only [selectRecvDelivery, enterRecvTargets] at h
    split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2.symm
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h

/-- An arriving SEND's pairing is pure control: whatever the
∃-quantified partner, a successful `applyPairing` from a
`.blockedSend` arrival shape leaves the state unchanged and steps the
arriving thread to `.next k`. (The delivery lands in the PARTNER's
configuration; nonempty buffers refuse `.internal`.) -/
theorem applyPairing_sendArrive_proj {σ : ExecState} {threads : Array Config}
    {i : Nat} {loc : Loc} {v' : GoValue} {k : Cont} {cand : Nat × PairTarget}
    {ts' : Array Config} {σ'' : ExecState} {c : Config}
    (hti : threads[i]? = some c) (hblc : isBlockedConfig c = false)
    (h : applyPairing σ threads i (.blockedSend (some loc) v' k) cand
      = .ok (ts', σ'')) :
    σ'' = σ ∧ ts'[i]? = some (.next k) := by
  have hilt : i < threads.size := (Array.getElem?_eq_some_iff.mp hti).1
  obtain ⟨cn, ct⟩ := cand
  cases ct with
  | opWaiter j =>
    simp only [applyPairing] at h
    cases hj : threads[j]? with
    | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
    | some pc =>
      simp only [hj] at h
      cases pc <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h)
      case blockedRecv ch2 targets elem2 envr kr =>
        simp only [bind_eq_ok] at h
        obtain ⟨⟨buf, cap, closed⟩, -, h⟩ := h
        split at h
        · simp only [bind_eq_ok] at h
          obtain ⟨⟨cr, s₂⟩, hres, h⟩ := h
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hts, hσ⟩ := h
          have hne : i ≠ j := by
            rintro rfl
            rw [hti] at hj
            injection hj with hj
            rw [hj] at hblc
            simp [isBlockedConfig] at hblc
          refine ⟨hσ ▸ (resumeRecvDelivery_state hres), ?_⟩
          rw [← hts, Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
          simp [hilt]
        · simp [throw, throwThe, MonadExceptOf.throw] at h
  | selectWaiter j ci =>
    simp only [applyPairing] at h
    cases hj : threads[j]? with
    | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
    | some pc =>
      simp only [hj] at h
      cases pc <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h)
      case blockedSelect evs envs ks =>
        cases hev : evs[ci]? with
        | none => simp [hev, throw, throwThe, MonadExceptOf.throw] at h
        | some cl =>
          simp only [hev] at h
          cases cl <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case recvEv chv targets elem2 body =>
            simp only [bind_eq_ok] at h
            obtain ⟨⟨buf, cap, closed⟩, -, h⟩ := h
            split at h
            · simp only [bind_eq_ok] at h
              obtain ⟨⟨cs', s₂⟩, hres, h⟩ := h
              simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨hts, hσ⟩ := h
              have hne : i ≠ j := by
                rintro rfl
                rw [hti] at hj
                injection hj with hj
                rw [hj] at hblc
                simp [isBlockedConfig] at hblc
              refine ⟨hσ ▸ (selectRecvDelivery_state hres), ?_⟩
              rw [← hts, Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
              simp [hilt]
            · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- An arriving zero-target RECEIVE's pairing at an EMPTY cell is pure
control with the delivered value discarded: state unchanged, the
arriving thread at `.next k`. (The partner's value is ∃-quantified —
the wider envelope — but a zero-target delivery drops it.) -/
theorem applyPairing_recvArrive_nil_proj {σ : ExecState}
    {threads : Array Config} {i : Nat} {loc : Loc} {elem : Ty}
    {env : LocalEnv} {k : Cont} {cand : Nat × PairTarget}
    {ts' : Array Config} {σ'' : ExecState} {c : Config}
    (hti : threads[i]? = some c) (hblc : isBlockedConfig c = false)
    (hload : loadLoc σ loc = .ok (.chanData #[] 0 false))
    (h : applyPairing σ threads i (.blockedRecv (some loc) [] elem env k) cand
      = .ok (ts', σ'')) :
    σ'' = σ ∧ ts'[i]? = some (.next k) := by
  have hilt : i < threads.size := (Array.getElem?_eq_some_iff.mp hti).1
  have hcell : chanCell σ loc = .ok (#[], 0, false) := by
    unfold chanCell
    rw [hload]
    rfl
  obtain ⟨cn, ct⟩ := cand
  cases ct with
  | opWaiter j =>
    simp only [applyPairing] at h
    cases hj : threads[j]? with
    | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
    | some pc =>
      simp only [hj] at h
      cases pc <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h)
      case blockedSend ch2 vs ks =>
        simp only [bind_eq_ok] at h
        obtain ⟨⟨buf, cap, closed⟩, hbc, h⟩ := h
        rw [hcell] at hbc
        simp only [Except.ok.injEq, Prod.mk.injEq] at hbc
        obtain ⟨rfl, rfl, rfl⟩ := hbc
        simp only [show (#[] : Array GoValue)[0]? = (none : Option GoValue)
          from rfl] at h
        simp only [bind_eq_ok] at h
        obtain ⟨⟨cr, s₂⟩, hres, h⟩ := h
        simp only [resumeRecvDelivery, pure_eq_ok, Except.ok.injEq,
          Prod.mk.injEq] at hres
        obtain ⟨rfl, rfl⟩ := hres
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨hts, hσ⟩ := h
        have hne : i ≠ j := by
          rintro rfl
          rw [hti] at hj
          injection hj with hj
          rw [hj] at hblc
          simp [isBlockedConfig] at hblc
        refine ⟨hσ.symm, ?_⟩
        rw [← hts, Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
        simp [hilt]
  | selectWaiter j ci =>
    simp only [applyPairing] at h
    cases hj : threads[j]? with
    | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
    | some pc =>
      simp only [hj] at h
      cases pc <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h)
      case blockedSelect evs envs ks =>
        cases hev : evs[ci]? with
        | none => simp [hev, throw, throwThe, MonadExceptOf.throw] at h
        | some cl =>
          simp only [hev] at h
          cases cl <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case sendEv chv vv selem body =>
            simp only [bind_eq_ok] at h
            obtain ⟨v'', -, ⟨buf, cap, closed⟩, hbc, h⟩ := h
            rw [hcell] at hbc
            simp only [Except.ok.injEq, Prod.mk.injEq] at hbc
            obtain ⟨rfl, rfl, rfl⟩ := hbc
            simp only [show (#[] : Array GoValue)[0]? = (none : Option GoValue)
              from rfl] at h
            simp only [bind_eq_ok] at h
            obtain ⟨⟨cr, s₂⟩, hres, h⟩ := h
            simp only [resumeRecvDelivery, pure_eq_ok, Except.ok.injEq,
              Prod.mk.injEq] at hres
            obtain ⟨rfl, rfl⟩ := hres
            simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨hts, hσ⟩ := h
            have hne : i ≠ j := by
              rintro rfl
              rw [hti] at hj
              injection hj with hj
              rw [hj] at hblc
              simp [isBlockedConfig] at hblc
            refine ⟨hσ.symm, ?_⟩
            rw [← hts, Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
            simp [hilt]

/-- The partner-side write of a successful pairing, per parked shape:
the result pool is a two-point update whose partner write is `.next ks`
for a parked plain SEND and `.next kr` for a parked zero-target
RECEIVE. Feeds the parked laws' `pairRelease` case: a parked thread's
release is either its own completion (`.next k`) or — when the
∃-pairing's partner is some OTHER index — the identity (the spin the
Löb induction absorbs). -/
theorem applyPairing_partner_write {σ : ExecState} {threads : Array Config}
    {i : Nat} {bc : Config} {cand : Nat × PairTarget}
    {ts' : Array Config} {σ'' : ExecState}
    (h : applyPairing σ threads i bc cand = .ok (ts', σ'')) :
    ∃ (j' : Nat) (ci' cj' : Config),
      ts' = (threads.setIfInBounds i ci').setIfInBounds j' cj'
      ∧ (∀ ch vs ks, threads[j']? = some (.blockedSend ch vs ks) →
          cj' = .next ks)
      ∧ (∀ ch elem envr kr,
          threads[j']? = some (.blockedRecv ch [] elem envr kr) →
          cj' = .next kr) := by
  obtain ⟨cn, ct⟩ := cand
  cases bc <;>
    try (simp [applyPairing, throw, throwThe, MonadExceptOf.throw] at h)
  case blockedSend ch v k =>
    cases ct
    case opWaiter j =>
      cases ch
      case none => simp [applyPairing, throw, throwThe, MonadExceptOf.throw] at h
      case some loc =>
        simp only [applyPairing] at h
        cases hj : threads[j]? with
        | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
        | some pc =>
          simp only [hj] at h
          cases pc <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedRecv ch2 targets elem2 envr kr =>
            simp only [bind_eq_ok] at h
            obtain ⟨⟨buf, cap, closed⟩, -, h⟩ := h
            split at h
            · simp only [bind_eq_ok] at h
              obtain ⟨⟨cr, s₂⟩, hres, h⟩ := h
              simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              refine ⟨j, _, cr, h.1.symm, ?_, ?_⟩
              · intro ch' vs ks hj'
                rw [hj] at hj'
                cases hj'
              · intro ch' elem' envr' kr' hj'
                rw [hj] at hj'
                injection hj' with hj'
                cases hj'
                -- targets = [], envr = envr', kr = kr'
                simp only [resumeRecvDelivery, pure_eq_ok, Except.ok.injEq,
                  Prod.mk.injEq] at hres
                exact hres.1.symm
            · simp [throw, throwThe, MonadExceptOf.throw] at h
    case selectWaiter j ci =>
      cases ch
      case none => simp [applyPairing, throw, throwThe, MonadExceptOf.throw] at h
      case some loc =>
        simp only [applyPairing] at h
        cases hj : threads[j]? with
        | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
        | some pc =>
          simp only [hj] at h
          cases pc <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedSelect evs envs ks =>
            cases hev : evs[ci]? with
            | none => simp [hev, throw, throwThe, MonadExceptOf.throw] at h
            | some cl =>
              simp only [hev] at h
              cases cl <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h)
              case recvEv chv targets elem2 body =>
                simp only [bind_eq_ok] at h
                obtain ⟨⟨buf, cap, closed⟩, -, h⟩ := h
                split at h
                · simp only [bind_eq_ok] at h
                  obtain ⟨⟨cs', s₂⟩, -, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  refine ⟨j, _, cs', h.1.symm, ?_, ?_⟩
                  · intro ch' vs ks' hj'
                    rw [hj] at hj'
                    cases hj'
                  · intro ch' elem' envr' kr' hj'
                    rw [hj] at hj'
                    cases hj'
                · simp [throw, throwThe, MonadExceptOf.throw] at h
  case blockedRecv ch targets elem env k =>
    cases ct
    case opWaiter j =>
      cases ch
      case none => simp [applyPairing, throw, throwThe, MonadExceptOf.throw] at h
      case some loc =>
        simp only [applyPairing] at h
        cases hj : threads[j]? with
        | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
        | some pc =>
          simp only [hj] at h
          cases pc <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedSend ch2 vs ks =>
            simp only [bind_eq_ok] at h
            obtain ⟨⟨buf, cap, closed⟩, -, h⟩ := h
            cases hbuf : buf[0]? with
            | none =>
              simp only [hbuf, bind_eq_ok] at h
              obtain ⟨⟨cr, s₂⟩, -, h⟩ := h
              simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              refine ⟨j, _, .next ks, h.1.symm, ?_, ?_⟩
              · intro ch' vs' ks' hj'
                rw [hj] at hj'
                injection hj' with hj'
                cases hj'
                rfl
              · intro ch' elem' envr' kr' hj'
                rw [hj] at hj'
                cases hj'
            | some hd =>
              simp only [hbuf, bind_eq_ok] at h
              obtain ⟨s₁, -, ⟨cr, s₂⟩, -, h⟩ := h
              simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              refine ⟨j, _, .next ks, h.1.symm, ?_, ?_⟩
              · intro ch' vs' ks' hj'
                rw [hj] at hj'
                injection hj' with hj'
                cases hj'
                rfl
              · intro ch' elem' envr' kr' hj'
                rw [hj] at hj'
                cases hj'
    case selectWaiter j ci =>
      cases ch
      case none => simp [applyPairing, throw, throwThe, MonadExceptOf.throw] at h
      case some loc =>
        simp only [applyPairing] at h
        cases hj : threads[j]? with
        | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
        | some pc =>
          simp only [hj] at h
          cases pc <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedSelect evs envs ks =>
            cases hev : evs[ci]? with
            | none => simp [hev, throw, throwThe, MonadExceptOf.throw] at h
            | some cl =>
              simp only [hev] at h
              cases cl <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h)
              case sendEv chv vv selem body =>
                simp only [bind_eq_ok] at h
                obtain ⟨v', -, ⟨buf, cap, closed⟩, -, h⟩ := h
                cases hbuf : buf[0]? with
                | none =>
                  simp only [hbuf, bind_eq_ok] at h
                  obtain ⟨⟨cr, s₂⟩, -, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  refine ⟨j, _, .exec body envs ks, h.1.symm, ?_, ?_⟩
                  · intro ch' vs' ks' hj'
                    rw [hj] at hj'
                    cases hj'
                  · intro ch' elem' envr' kr' hj'
                    rw [hj] at hj'
                    cases hj'
                | some hd =>
                  simp only [hbuf, bind_eq_ok] at h
                  obtain ⟨s₁, -, ⟨cr, s₂⟩, -, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  refine ⟨j, _, .exec body envs ks, h.1.symm, ?_, ?_⟩
                  · intro ch' vs' ks' hj'
                    rw [hj] at hj'
                    cases hj'
                  · intro ch' elem' envr' kr' hj'
                    rw [hj] at hj'
                    cases hj'
  case blockedSelect evs env k =>
    cases hev : evs[cn]? with
    | none => simp [hev, throw, throwThe, MonadExceptOf.throw] at h
    | some cl =>
      simp only [hev] at h
      cases cl
      case recvEv chv targets elem body =>
        cases ct
        case selectWaiter j ci =>
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case opWaiter j =>
          cases hj : threads[j]? with
          | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
          | some pc =>
            simp only [hj] at h
            cases pc <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h)
            case blockedSend ch2 vs ks =>
              cases hcl : chanValueLoc chv with
              | none => simp [hcl, throw, throwThe, MonadExceptOf.throw] at h
              | some loc =>
                simp only [hcl, bind_eq_ok] at h
                obtain ⟨⟨buf, cap, closed⟩, -, h⟩ := h
                cases hbuf : buf[0]? with
                | none =>
                  simp only [hbuf, bind_eq_ok] at h
                  obtain ⟨⟨ci', s₂⟩, -, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  refine ⟨j, _, .next ks, h.1.symm, ?_, ?_⟩
                  · intro ch' vs' ks' hj'
                    rw [hj] at hj'
                    injection hj' with hj'
                    cases hj'
                    rfl
                  · intro ch' elem' envr' kr' hj'
                    rw [hj] at hj'
                    cases hj'
                | some hd =>
                  simp only [hbuf, bind_eq_ok] at h
                  obtain ⟨s₁, -, ⟨ci', s₂⟩, -, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  refine ⟨j, _, .next ks, h.1.symm, ?_, ?_⟩
                  · intro ch' vs' ks' hj'
                    rw [hj] at hj'
                    injection hj' with hj'
                    cases hj'
                    rfl
                  · intro ch' elem' envr' kr' hj'
                    rw [hj] at hj'
                    cases hj'
      case sendEv chv vv selem body =>
        cases ct
        case selectWaiter j ci =>
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case opWaiter j =>
          cases hj : threads[j]? with
          | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
          | some pc =>
            simp only [hj] at h
            cases pc <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h)
            case blockedRecv ch2 targetsr elemr envr kr =>
              cases hcl : chanValueLoc chv with
              | none => simp [hcl, throw, throwThe, MonadExceptOf.throw] at h
              | some loc =>
                simp only [hcl, bind_eq_ok] at h
                obtain ⟨⟨buf, cap, closed⟩, -, h⟩ := h
                split at h
                · simp only [bind_eq_ok] at h
                  obtain ⟨v', -, ⟨cr, s₂⟩, hres, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  refine ⟨j, _, cr, h.1.symm, ?_, ?_⟩
                  · intro ch' vs' ks' hj'
                    rw [hj] at hj'
                    cases hj'
                  · intro ch' elem' envr' kr' hj'
                    rw [hj] at hj'
                    injection hj' with hj'
                    cases hj'
                    simp only [resumeRecvDelivery, pure_eq_ok, Except.ok.injEq,
                      Prod.mk.injEq] at hres
                    exact hres.1.symm
                · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `arrivalCases` at a chan-op apply position, inverted at `.single`:
the pairing plan is `chanArrivalPlan`'s. -/
theorem arrivalCases_chanStK_single {σ : ExecState} {threads : Array Config}
    {i : Nat} {v : GoValue} {op : ChanStOp} {done : List GoValue}
    {env : LocalEnv} {k : Cont} {bc : Config} {cs : List (Nat × PairTarget)}
    (h : arrivalCases σ threads i (.retV v (.chanStK op done [] env k))
      = .ok (.single bc cs)) :
    chanArrivalPlan σ threads i op ((v :: done).reverse) env k
      = .ok (some (bc, cs)) := by
  simp only [arrivalCases] at h
  cases hp : chanArrivalPlan σ threads i op ((v :: done).reverse) env k with
  | error e => rw [hp] at h; simp [Bind.bind, Except.bind] at h
  | ok o =>
    rw [hp] at h
    cases o with
    | none => simp [Bind.bind, Except.bind, pure_eq_ok] at h
    | some pr =>
      obtain ⟨bc', cs'⟩ := pr
      simp only [Bind.bind, Except.bind] at h
      injection h with h
      injection h with h1 h2
      subst h1
      subst h2
      rfl

/-- `arrivalCases` at a chan-op apply position never yields `.multi`
(the L2 multi-ready analysis is select-only). -/
theorem arrivalCases_chanStK_not_multi {σ : ExecState}
    {threads : Array Config} {i : Nat} {v : GoValue} {op : ChanStOp}
    {done : List GoValue} {env : LocalEnv} {k : Cont}
    {os : List ArrivalOutcome}
    (h : arrivalCases σ threads i (.retV v (.chanStK op done [] env k))
      = .ok (.multi os)) : False := by
  simp only [arrivalCases] at h
  cases hp : chanArrivalPlan σ threads i op ((v :: done).reverse) env k with
  | error e => rw [hp] at h; simp [Bind.bind, Except.bind] at h
  | ok o =>
    rw [hp] at h
    cases o with
    | none => simp [Bind.bind, Except.bind, pure_eq_ok] at h
    | some pr =>
      obtain ⟨bc', cs'⟩ := pr
      simp [Bind.bind, Except.bind, pure_eq_ok] at h

/-- A parked configuration's arrival analysis is `.cellPath` (it is not
an apply position — refutes `selCommit` from parked shapes). -/
theorem arrivalCases_blocked {σ : ExecState} {threads : Array Config}
    {i : Nat} {c : Config} {an : ArrivalAnalysis}
    (hblk : isBlockedConfig c = true)
    (h : arrivalCases σ threads i c = .ok an) : an = .cellPath := by
  cases c <;> first
    | (simp [isBlockedConfig] at hblk; done)
    | exact (Except.ok.inj h).symm

/-- `chanArrivalPlan` inversion, SEND: a produced pairing plan pins the
would-block shape to `.blockedSend` over the operand channel with the
normalized value. (The plan also implies the channel is open — not
needed by the rendezvous laws, whose invariant pins it.) -/
theorem chanArrivalPlan_send_inv {σ : ExecState} {threads : Array Config}
    {i : Nat} {elem : Ty} {chv vv : GoValue} {env : LocalEnv} {k : Cont}
    {bc : Config} {cs : List (Nat × PairTarget)}
    (h : chanArrivalPlan σ threads i (.send elem) [chv, vv] env k
      = .ok (some (bc, cs))) :
    ∃ (loc : Loc) (v'' : GoValue),
      chanValueLoc chv = some loc
      ∧ normalizeValueForTy σ elem vv = .ok v''
      ∧ bc = .blockedSend (some loc) v'' k := by
  simp only [chanArrivalPlan] at h
  cases hcl : chanValueLoc chv with
  | none => rw [hcl] at h; injection h with h; cases h
  | some loc =>
    rw [hcl] at h
    split at h
    · injection h with h; cases h
    · rename_i loc' heq
      injection heq with heq
      subst heq
      split at h
      · injection h with h; cases h
      · simp only [bind_eq_ok] at h
        obtain ⟨⟨buf, cap, closed⟩, -, h⟩ := h
        split at h
        · injection h with h; cases h
        · simp only [bind_eq_ok] at h
          obtain ⟨v'', hn, h⟩ := h
          simp only [pure_eq_ok, Except.ok.injEq, Option.some.injEq,
            Prod.mk.injEq] at h
          exact ⟨loc, v'', rfl, hn, h.1.symm⟩

/-- `chanArrivalPlan` inversion, RECV: the would-block shape is
`.blockedRecv` over the operand channel with the op's targets. -/
theorem chanArrivalPlan_recv_inv {σ : ExecState} {threads : Array Config}
    {i : Nat} {targets : List Assignee} {elem : Ty} {chv : GoValue}
    {env : LocalEnv} {k : Cont} {bc : Config} {cs : List (Nat × PairTarget)}
    (h : chanArrivalPlan σ threads i (.recv targets elem) [chv] env k
      = .ok (some (bc, cs))) :
    ∃ loc : Loc, chanValueLoc chv = some loc
      ∧ bc = .blockedRecv (some loc) targets elem env k := by
  simp only [chanArrivalPlan] at h
  cases hcl : chanValueLoc chv with
  | none => rw [hcl] at h; injection h with h; cases h
  | some loc =>
    rw [hcl] at h
    split at h
    · injection h with h; cases h
    · rename_i loc' heq
      injection heq with heq
      subst heq
      split at h
      · injection h with h; cases h
      · simp only [bind_eq_ok] at h
        obtain ⟨⟨buf, cap, closed⟩, -, h⟩ := h
        split at h
        · injection h with h; cases h
        · simp only [pure_eq_ok, Except.ok.injEq, Option.some.injEq,
            Prod.mk.injEq] at h
          exact ⟨loc, rfl, h.1.symm⟩

/-- A parked SEND on the rendezvous cell (unbuffered, open, empty) is
never wake-ready: `resumeThread` refuses. -/
theorem resumeThread_rendezvous_send {σ : ExecState} {loc : Loc}
    {v : GoValue} {k : Cont} {r : Config × ExecState}
    (hload : loadLoc σ loc = .ok (.chanData #[] 0 false))
    (h : resumeThread σ (.blockedSend (some loc) v k) = .ok r) : False := by
  have hcell : chanCell σ loc = .ok (#[], 0, false) := by
    unfold chanCell
    rw [hload]
    rfl
  simp only [resumeThread] at h
  rw [hcell] at h
  simp [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- A parked RECEIVE on the rendezvous cell is never wake-ready. -/
theorem resumeThread_rendezvous_recv {σ : ExecState} {loc : Loc}
    {targets : List Assignee} {elem : Ty} {env : LocalEnv} {k : Cont}
    {r : Config × ExecState}
    (hload : loadLoc σ loc = .ok (.chanData #[] 0 false))
    (h : resumeThread σ (.blockedRecv (some loc) targets elem env k) = .ok r) :
    False := by
  have hcell : chanCell σ loc = .ok (#[], 0, false) := by
    unfold chanCell
    rw [hload]
    rfl
  simp only [resumeThread] at h
  rw [hcell] at h
  simp [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- The parked SELF-STEP (reducibility witness for the parked laws): in
any state holding an empty-buffer channel cell anywhere, every parked
configuration has a `pairRelease` step to ITSELF — a pairing between
two ∃-threads elsewhere in the pool leaves the parked thread untouched
(`ts'[j] = p`), and the direct handoff at an empty buffer preserves the
state. This is the O2 spin surfacing inside `pairRelease` (design note
§1a); the parked laws absorb it by Löb induction. -/
theorem stepDC_parked_spin {p : Config} {σ : ExecState} {loc : Loc}
    {cap : Nat} {closed : Bool}
    (hblk : isBlockedConfig p = true)
    (hload : loadLoc σ loc = .ok (.chanData #[] cap closed)) :
    StepDC p σ p σ [] := by
  have hcell : chanCell σ loc = .ok (#[], cap, closed) := by
    unfold chanCell
    rw [hload]
    rfl
  refine .pairRelease hblk
    ⟨σ, #[.blockedSend (some loc) (.bool false) .stop,
          .blockedRecv (some loc) [] (.bool) [] .stop, p],
      0, 2, .blockedSend (some loc) (.bool false) .stop,
      [(0, .opWaiter 1)], 0,
      (((#[.blockedSend (some loc) (.bool false) .stop,
          .blockedRecv (some loc) [] (.bool) [] .stop, p] : Array Config).setIfInBounds
            0 (.next .stop)).setIfInBounds 1 (.next .stop)),
      (by decide), rfl, (by omega), ?_, ?_⟩
  · show applyPairing σ _ 0 (.blockedSend (some loc) (.bool false) .stop)
      (0, .opWaiter 1) = _
    simp only [applyPairing]
    rw [show (#[Config.blockedSend (some loc) (.bool false) .stop,
        Config.blockedRecv (some loc) [] (.bool) [] .stop, p] : Array Config)[1]?
      = some (.blockedRecv (some loc) [] (.bool) [] .stop) from rfl]
    rw [hcell]
    simp [Bind.bind, Except.bind, resumeRecvDelivery, Array.isEmpty]
  · rw [Array.getElem?_setIfInBounds_ne (by omega),
      Array.getElem?_setIfInBounds_ne (by omega)]
    rfl

/-! ## The D-carrier lifting cores (ports of the sequential engines)

Each is the sequential core re-plumbed over `GoPrimStepD`, with the
decomposed rules refuted by `stepDC_shape_cases` under the two shape
side-conditions (`isBlockedConfig`/`chanSelApplyPos` false). -/

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- Resource-conditioned deterministic NON-MUTATING step core on the
D-carrier (`wp_det_step_keep`'s port): a step that reads state the
resources describe but changes nothing. -/
theorem wpD_det_step_keep {P : IProp GF} {c₀ c₁ : Config}
    (hnv : ToVal.toVal (PoolCfgD.mk c₀) = (none : Option Unit))
    (hsp : spawnPlan c₀ = none) (hsc : spawnedCont c₀ = none)
    (hblk : isBlockedConfig c₀ = false) (hpos : chanSelApplyPos c₀ = false)
    (hred : ∀ σ₁ : ExecState, σ₁.functions = GoCoreGS.prog GF →
      σ₁.methods = GoCoreGS.methods GF → σ₁.types = GoCoreGS.types GF →
      iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ₁.heap) ∗ P)
        ⊢ |==> ⌜Step c₀ σ₁ c₁ σ₁ ∧
            (∀ c' s', Step c₀ σ₁ c' s' → c' = c₁ ∧ s' = σ₁)⌝) :
    P ∗ (P -∗ WP (PoolCfgD.mk c₁) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgD.mk c₀) @ s ; E {{ Φ }} := by
  iintro ⟨HP, Hcont⟩
  iapply wp_lift_step (h := hnv)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  ihave %Hstep : ⌜Step c₀ σ₁ c₁ σ₁ ∧
      (∀ c' s', Step c₀ σ₁ c' s' → c' = c₁ ∧ s' = σ₁)⌝ $$ [Hσ HP]
  · icases (hred σ₁ hfns hmeths htypes) $$ [$Hσ $HP] with >%h
    ipureintro
    exact h
  obtain ⟨hstep, hdet⟩ := Hstep
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], PoolCfgD.mk c₁, _, [], GoPrimStepD.step (.lift (.lift hstep))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep2 Hcred
  cases Hstep2 with
  | step st =>
    rcases stepDC_shape_cases hblk hpos st with hse | ⟨kk, hkk, -⟩
    · cases hse with
      | lift sq =>
        obtain ⟨rfl, rfl⟩ := hdet _ _ sq
        imod Hclose
        imodintro
        simp only [List.map_nil, Algebra.BigOpL.bigOpL_nil]
        isplitl [Hσ]
        · isplitl [Hσ]
          · iexact Hσ
          · ipureintro
            exact ⟨hfns, hmeths, htypes, hwf⟩
        · isplitl [HP Hcont]
          · iapply Hcont $$ HP
          · itrivial
      | spawn hsp' _ =>
        rw [hsp] at hsp'
        cases hsp'
    · rw [hkk] at hsc
      simp [spawnedCont] at hsc

/-- The variable-load step on the D-carrier (`wp_eval_var`'s port). -/
theorem wpD_eval_var {id : String} {a : Addr} {cell : HeapCell}
    {env : LocalEnv} {k : Cont}
    (hres : LocalEnv.lookup env id = some (.base a)) :
    a.id ↦ cell
      ∗ (a.id ↦ cell -∗ WP (PoolCfgD.mk (.retV cell.value k)) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgD.mk (.evalE (.var id) env k)) @ s ; E {{ Φ }} := by
  iapply wpD_det_step_keep (P := iprop(a.id ↦ cell))
    (c₁ := Config.retV cell.value k) (hnv := rfl) (hsp := rfl) (hsc := rfl)
    (hblk := rfl) (hpos := rfl)
  intro σ₁ _hfns _hmeths _htypes
  iintro ⟨Hσ, Hpt⟩
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some cell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some cell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hload : loadLoc σ₁ (.base a) = .ok cell.value := by
    simp [loadLoc, hlook]
  imodintro
  ipureintro
  refine ⟨Step.evalVar hres hload, ?_⟩
  intro c' s' hst
  obtain ⟨h1, h2⟩ := step_det (by trivial) (Step.evalVar hres hload) hst
  exact ⟨h1.symm, h2.symm⟩

/-- **The ALLOCATING fork on the D-carrier** — `wpD_fork`'s sibling for
the spawn class whose `spawnStep` allocates ONE cell (a one-parameter
callee: `bindParams` allocates the param cell; no results, no decls).
This is the gen_heap-update fork variant, shipped on the D-CARRIER
(S1 audit fix round scoping): LangC's `wpC_fork` docstring recorded
the debt on the `PoolCfg` carrier, and the C-carrier allocating
variant remains unbuilt — this law discharges the CLASS on the
carrier where the arc's work continues (the LangC record is
back-annotated); the channel rendezvous exemplar is the consumer.
The child configuration is a function of the machine-chosen address
(`∀ pa` discipline), and the child's WP receives the fresh param
cell. -/
theorem wpD_fork_alloc₁ {c : Config} {cv : GoValue} {args : List GoValue}
    {k : Cont} {pcell : HeapCell} (childOf : Addr → Config)
    (hsp : spawnPlan c = some (cv, args, k))
    (hspawn : ∀ σ : ExecState, σ.functions = GoCoreGS.prog GF →
      σ.methods = GoCoreGS.methods GF → σ.types = GoCoreGS.types GF →
      spawnStep σ cv args k = .ok (.spawned k, childOf ⟨σ.nextAddr⟩,
        allocMany σ [pcell])) :
    ▷ iprop(∀ pa : Addr, pa.id ↦ pcell -∗
        WP (PoolCfgD.mk (childOf pa)) @ s ; ⊤ {{ fun _ => iprop(True) }})
      ∗ ▷ WP (PoolCfgD.mk (.spawned k)) @ s ; E {{ Φ }}
      ⊢ WP (PoolCfgD.mk c) @ s ; E {{ Φ }} := by
  iintro ⟨Hchild, Hparent⟩
  have hnv : ToVal.toVal (PoolCfgD.mk c) = (none : Option Unit) := by
    match c, hsp with
    | .retV cv' (.goCalleeK [] env k'), _ => rfl
    | .retV v (.goArgsK cv' vals [] env k'), _ => rfl
  have hblk : isBlockedConfig c = false := by
    match c, hsp with
    | .retV cv' (.goCalleeK [] env k'), _ => rfl
    | .retV v (.goArgsK cv' vals [] env k'), _ => rfl
  have hpos : chanSelApplyPos c = false := by
    match c, hsp with
    | .retV cv' (.goCalleeK [] env k'), _ => rfl
    | .retV v (.goArgsK cv' vals [] env k'), _ => rfl
  iapply wp_lift_step hnv
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  have hfresh : get? (heapToMap σ₁.heap) σ₁.nextAddr = none := hwf.fresh_get?
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨.spawned k⟩, _, [⟨childOf ⟨σ₁.nextAddr⟩⟩],
        GoPrimStepD.step (.lift (.spawn hsp (hspawn σ₁ hfns hmeths htypes)))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  have hshape : e₂ = PoolCfgD.mk (.spawned k) ∧ σ₂ = allocMany σ₁ [pcell]
      ∧ eₜ = [PoolCfgD.mk (childOf ⟨σ₁.nextAddr⟩)] := by
    cases Hstep with
    | step st =>
      rcases stepDC_shape_cases hblk hpos st with hse | ⟨k', hk, -⟩
      · cases hse with
        | lift sq => exact absurd sq (step_spawnPos_elim hsp)
        | spawn hsp' hstep' =>
          rw [hsp] at hsp'
          injection hsp' with heq
          injection heq with h1 hrest
          injection hrest with h2 h3
          subst h1
          subst h2
          subst h3
          rw [hspawn σ₁ hfns hmeths htypes] at hstep'
          injection hstep' with hp
          injection hp with hpar hrest'
          injection hrest' with hchild hσ
          subst hpar
          subst hchild
          subst hσ
          exact ⟨rfl, rfl, rfl⟩
      · rw [hk] at hsp
        cases hsp
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  simp only [allocMany]
  imod (genHeap_alloc (v := pcell) hfresh) $$ Hσ with ⟨Hσ, Hp, Htok⟩
  imod Hclose
  imodintro
  isplitl [Hσ]
  · isplitl [Hσ]
    · iapply (genHeapInterp_eqv
        (fun kk => (heapToMap_set_base σ₁.heap ⟨σ₁.nextAddr⟩ pcell kk).symm)) $$ Hσ
    · ipureintro
      exact ⟨hfns, hmeths, htypes, HeapWf.allocMany [pcell] hwf⟩
  isplitl [Hparent]
  · iexact Hparent
  · simp only [Algebra.BigOpL.bigOpL_cons, Algebra.BigOpL.bigOpL_nil]
    isplitl [Hchild Hp]
    · iapply Hchild $$ %(⟨σ₁.nextAddr⟩ : Addr) [$Hp]
    · itrivial

end

/-! ## The rendezvous-class channel laws (design note §3, exemplar
scope: the cell pinned by an Iris invariant to `chanData #[] 0 false`
— unbuffered, open, empty, never written; every reachable channel step
of the class is state-preserving) -/

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}
variable {N : Namespace} {a : Addr} {cell : HeapCell}

/-- **SEND at the apply position on a rendezvous channel.** The
outcome set (note §3): the PARK (`applyChanOp`'s cell path — cap 0,
no room, open) and the ∃-PAIRING (pure control, state unchanged —
possibly phantom, §1a). The closed-panic and buffered-enqueue branches
are refuted by the invariant's cell shape. One continuation over the
disjunction, so the caller keeps all resources in both branches. -/
theorem wpD_send_rendezvous_inv {elem : Ty} {vv v' : GoValue}
    {env : LocalEnv} {k : Cont}
    (hN : ↑N ⊆ E)
    (hcv : cell.value = .chanData #[] 0 false)
    (hnorm : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ elem vv = .ok v') :
    Iris.inv N (iprop(a.id ↦ cell))
      ∗ (∀ c' : Config,
          ⌜c' = .blockedSend (some (.base a)) v' k ∨ c' = .next k⌝ -∗
          WP (PoolCfgD.mk c') @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgD.mk (.retV vv
          (.chanStK (.send elem) [.chan ⟨some (.base a)⟩] [] env k)))
          @ s ; E {{ Φ }} := by
  iintro ⟨#Hinv, Hcont⟩
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hpins⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hpins
  imod (inv_acc hN) $$ Hinv with ⟨HI, HcloseI⟩
  imod HI with Hpt
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some cell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some cell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hload : loadLoc σ₁ (.base a) = .ok (.chanData #[] 0 false) := by
    have h := loadLoc_base_of_lookup hlook
    rw [hcv] at h
    exact h
  have hcell : chanCell σ₁ (.base a) = .ok (#[], 0, false) := by
    unfold chanCell
    rw [hload]
    rfl
  have happly : applyChanOp σ₁ (.send elem)
      ((vv :: [GoValue.chan ⟨some (.base a)⟩]).reverse) env k
      = .ok (.blockedSend (some (.base a)) v' k, σ₁) := by
    simp [applyChanOp, valueAsChan, hnorm σ₁ htypes, hcell,
      Bind.bind, Except.bind]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨.blockedSend (some (.base a)) v' k⟩, σ₁, [],
        GoPrimStepD.step (.lift (.lift (Step.chanStApply happly)))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨c₂⟩ := e₂
  have hshape : (c₂ = Config.blockedSend (some (.base a)) v' k
        ∨ c₂ = Config.next k) ∧ σ₂ = σ₁ ∧ eₜ = [] := by
    cases Hstep with
    | step st =>
      cases st with
      | lift ste =>
        cases ste with
        | lift sq =>
          cases sq with
          | chanStApply h =>
            rw [happly] at h
            injection h with h
            injection h with h1 h2
            exact ⟨.inl h1.symm, h2.symm, by simp⟩
          | chanStApplyPanic h =>
            rw [happly] at h
            cases h
        | spawn hsp' _ => simp [spawnPlan] at hsp'
      | wake hblk' _ => simp [isBlockedConfig] at hblk'
      | pairRelease hblk' _ => simp [isBlockedConfig] at hblk'
      | pairArrive hti hblc hpair hidx happ hproj =>
        rcases hpair with hs | ⟨os, sel, hm, -⟩
        · have hplan := arrivalCases_chanStK_single hs
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
            List.cons_append] at hplan
          obtain ⟨loc, v'', hclv, hn, rfl⟩ := chanArrivalPlan_send_inv hplan
          simp only [chanValueLoc, Option.some.injEq] at hclv
          subst hclv
          rw [hnorm σ₁ htypes] at hn
          injection hn with hn
          subst hn
          obtain ⟨rfl, hpi⟩ := applyPairing_sendArrive_proj hti hblc happ
          rw [hpi] at hproj
          injection hproj with hproj
          exact ⟨.inr hproj.symm, rfl, by simp⟩
        · exact (arrivalCases_chanStK_not_multi hm).elim
      | selCommit hex _ =>
        obtain ⟨th, ii, os, sel, hti, hm, -⟩ := hex
        exact (arrivalCases_chanStK_not_multi hm).elim
  obtain ⟨hc, rfl, rfl⟩ := hshape
  imod Hclose
  ihave HIc : iprop(▷ (a.id ↦ cell)) $$ [Hpt]
  · inext
    iexact Hpt
  imod HcloseI $$ HIc
  imodintro
  simp only [Algebra.BigOpL.bigOpL_nil]
  isplitl [Hσ]
  · isplitl [Hσ]
    · iexact Hσ
    · ipureintro
      exact ⟨hfns, hmeths, htypes, hwf⟩
  isplitl [Hcont]
  · iapply Hcont $$ %c₂
    ipureintro
    exact hc
  · itrivial

/-- **Zero-target RECEIVE at the apply position on a rendezvous
channel.** Outcomes: the PARK (open empty cell) and the ∃-PAIRING
(delivery of an ∃-quantified value, DISCARDED by the zero-target form —
pure control, state unchanged). Dequeue and closed-zero branches are
refuted by the invariant's cell shape. -/
theorem wpD_recv_nil_rendezvous_inv {elem : Ty} {env : LocalEnv} {k : Cont}
    (hN : ↑N ⊆ E)
    (hcv : cell.value = .chanData #[] 0 false) :
    Iris.inv N (iprop(a.id ↦ cell))
      ∗ (∀ c' : Config,
          ⌜c' = .blockedRecv (some (.base a)) [] elem env k ∨ c' = .next k⌝ -∗
          WP (PoolCfgD.mk c') @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgD.mk (.retV (.chan ⟨some (.base a)⟩)
          (.chanStK (.recv [] elem) [] [] env k))) @ s ; E {{ Φ }} := by
  iintro ⟨#Hinv, Hcont⟩
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hpins⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hpins
  imod (inv_acc hN) $$ Hinv with ⟨HI, HcloseI⟩
  imod HI with Hpt
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some cell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some cell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hload : loadLoc σ₁ (.base a) = .ok (.chanData #[] 0 false) := by
    have h := loadLoc_base_of_lookup hlook
    rw [hcv] at h
    exact h
  have hcell : chanCell σ₁ (.base a) = .ok (#[], 0, false) := by
    unfold chanCell
    rw [hload]
    rfl
  have happly : applyChanOp σ₁ (.recv [] elem)
      (((GoValue.chan ⟨some (.base a)⟩) :: ([] : List GoValue)).reverse) env k
      = .ok (.blockedRecv (some (.base a)) [] elem env k, σ₁) := by
    simp [applyChanOp, valueAsChan, hcell, Bind.bind, Except.bind]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨.blockedRecv (some (.base a)) [] elem env k⟩, σ₁, [],
        GoPrimStepD.step (.lift (.lift (Step.chanStApply happly)))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨c₂⟩ := e₂
  have hshape : (c₂ = Config.blockedRecv (some (.base a)) [] elem env k
        ∨ c₂ = Config.next k) ∧ σ₂ = σ₁ ∧ eₜ = [] := by
    cases Hstep with
    | step st =>
      cases st with
      | lift ste =>
        cases ste with
        | lift sq =>
          cases sq with
          | chanStApply h =>
            rw [happly] at h
            injection h with h
            injection h with h1 h2
            exact ⟨.inl h1.symm, h2.symm, by simp⟩
          | chanStApplyPanic h =>
            rw [happly] at h
            cases h
        | spawn hsp' _ => simp [spawnPlan] at hsp'
      | wake hblk' _ => simp [isBlockedConfig] at hblk'
      | pairRelease hblk' _ => simp [isBlockedConfig] at hblk'
      | pairArrive hti hblc hpair hidx happ hproj =>
        rcases hpair with hs | ⟨os, sel, hm, -⟩
        · have hplan := arrivalCases_chanStK_single hs
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append] at hplan
          obtain ⟨loc, hclv, rfl⟩ := chanArrivalPlan_recv_inv hplan
          simp only [chanValueLoc, Option.some.injEq] at hclv
          subst hclv
          obtain ⟨rfl, hpi⟩ :=
            applyPairing_recvArrive_nil_proj hti hblc hload happ
          rw [hpi] at hproj
          injection hproj with hproj
          exact ⟨.inr hproj.symm, rfl, by simp⟩
        · exact (arrivalCases_chanStK_not_multi hm).elim
      | selCommit hex _ =>
        obtain ⟨th, ii, os, sel, hti, hm, -⟩ := hex
        exact (arrivalCases_chanStK_not_multi hm).elim
  obtain ⟨hc, rfl, rfl⟩ := hshape
  imod Hclose
  ihave HIc : iprop(▷ (a.id ↦ cell)) $$ [Hpt]
  · inext
    iexact Hpt
  imod HcloseI $$ HIc
  imodintro
  simp only [Algebra.BigOpL.bigOpL_nil]
  isplitl [Hσ]
  · isplitl [Hσ]
    · iexact Hσ
    · ipureintro
      exact ⟨hfns, hmeths, htypes, hwf⟩
  isplitl [Hcont]
  · iapply Hcont $$ %c₂
    ipureintro
    exact hc
  · itrivial

/-- **The PARKED SENDER on a rendezvous channel.** Wake is refuted by
the invariant's cell shape (no close, no room at cap 0); what remains
is `pairRelease`, whose derived envelope has exactly two successor
classes here (`applyPairing_partner_write` proves the enumeration
over all arms): the SELF-step (`p → p`, absorbed by Löb — note §1a)
and the release to `.next k`. THE RELEASE CARRIES NO DELIVERY
INFORMATION (S1 audit fix round): `applyPairing` never reads the
PARTNER's channel and `pairRelease` ∃-quantifies the imagined pool,
so the release fires equally for a real handoff and for a wholly
PHANTOM pairing on a different channel with no partner at all
(`crossChannelSendRelease`, the tracked witness). Sound — the
successor set is complete either way — but "reached `.next k`" must
never be read as "the value was delivered"; that tie is the slice-2
protocol ghost's job. State-preserving throughout. -/
theorem wpD_blocked_send_rendezvous_inv {v' : GoValue} {k : Cont}
    (hN : ↑N ⊆ E)
    (hcv : cell.value = .chanData #[] 0 false) :
    Iris.inv N (iprop(a.id ↦ cell))
      ∗ WP (PoolCfgD.mk (.next k)) @ s ; E {{ Φ }}
      ⊢ WP (PoolCfgD.mk (.blockedSend (some (.base a)) v' k)) @ s ; E {{ Φ }} := by
  iintro ⟨#Hinv, Hcont⟩
  iloeb as IH
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hpins⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hpins
  imod (inv_acc hN) $$ Hinv with ⟨HI, HcloseI⟩
  imod HI with Hpt
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some cell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some cell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hload : loadLoc σ₁ (.base a) = .ok (.chanData #[] 0 false) := by
    have h := loadLoc_base_of_lookup hlook
    rw [hcv] at h
    exact h
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨.blockedSend (some (.base a)) v' k⟩, σ₁, [],
        GoPrimStepD.step (stepDC_parked_spin rfl hload)⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨c₂⟩ := e₂
  have hshape : (c₂ = Config.blockedSend (some (.base a)) v' k
        ∨ c₂ = Config.next k) ∧ σ₂ = σ₁ ∧ eₜ = [] := by
    cases Hstep with
    | step st =>
      cases st with
      | lift ste =>
        cases ste with
        | lift sq => cases sq
        | spawn hsp' _ => simp [spawnPlan] at hsp'
      | wake hblk' hres => exact (resumeThread_rendezvous_send hload hres).elim
      | pairArrive hti hblc hpair hidx happ hproj =>
        simp [isBlockedConfig] at hblc
      | selCommit hex _ =>
        obtain ⟨th, ii, os, sel, hti, hm, -⟩ := hex
        exact absurd (arrivalCases_blocked rfl hm) (by simp)
      | pairRelease hblk' hex =>
        obtain ⟨σ₀, th, ii, jj, bc, cs, idx, ts', hidx, hj, hij, happ, hproj⟩ := hex
        obtain ⟨j', ci', cj', hts, hsend, -⟩ := applyPairing_partner_write happ
        subst hts
        have hjlt : jj < th.size := (Array.getElem?_eq_some_iff.mp hj).1
        by_cases hjj' : jj = j'
        · subst hjj'
          have hpr : ((th.setIfInBounds ii ci').setIfInBounds jj cj')[jj]?
              = some cj' := by
            simp [Array.size_setIfInBounds, hjlt]
          rw [hpr] at hproj
          injection hproj with hproj
          have hcj := hsend _ _ _ hj
          exact ⟨.inr (hproj.symm.trans hcj), rfl, by simp⟩
        · have hpr : ((th.setIfInBounds ii ci').setIfInBounds j' cj')[jj]?
              = some (Config.blockedSend (some (.base a)) v' k) := by
            rw [Array.getElem?_setIfInBounds_ne (fun h => hjj' h.symm),
              Array.getElem?_setIfInBounds_ne hij]
            exact hj
          rw [hpr] at hproj
          injection hproj with hproj
          exact ⟨.inl hproj.symm, rfl, by simp⟩
  obtain ⟨hc, rfl, rfl⟩ := hshape
  imod Hclose
  ihave HIc : iprop(▷ (a.id ↦ cell)) $$ [Hpt]
  · inext
    iexact Hpt
  imod HcloseI $$ HIc
  imodintro
  simp only [Algebra.BigOpL.bigOpL_nil]
  isplitl [Hσ]
  · isplitl [Hσ]
    · iexact Hσ
    · ipureintro
      exact ⟨hfns, hmeths, htypes, hwf⟩
  isplitl [IH Hcont]
  · rcases hc with rfl | rfl
    · iapply IH $$ Hcont
    · iexact Hcont
  · itrivial

/-- A CLOSE apply position never pairs: `chanArrivalPlan` has no
`.close` arm (fed to `arrivalCases_chanStK_single` to refute
`pairArrive` at close applies). -/
theorem chanArrivalPlan_close {σ : ExecState} {threads : Array Config}
    {i : Nat} {chv : GoValue} {env : LocalEnv} {k : Cont} :
    chanArrivalPlan σ threads i .close [chv] env k = .ok none := rfl

/-- **CLOSE on an OWNED open channel cell** (the owned-cell law form —
note §3: close needs no invariant when the closing thread owns the
cell, the sequential-degenerate class the probe witnesses; the
invariant sibling lands with a sharing consumer). The one channel law
that WRITES the cell through the D-carrier: `closed := true`, buffer
and capacity preserved (drain-after-close is `applyChanOp`'s recv
semantics, not close's). The cell is the machine-real UNTYPED shape
(`makeChan` allocates `declaredTy := none`). No pairing branch exists
at a close apply (`chanArrivalPlan_close`) — the successor is
deterministic. -/
theorem wpD_close_owned {a : Addr} {buf : Array GoValue} {cap : Nat}
    {env : LocalEnv} {k : Cont} :
    a.id ↦ (⟨none, .chanData buf cap false⟩ : HeapCell)
      ∗ (a.id ↦ (⟨none, .chanData buf cap true⟩ : HeapCell) -∗
          WP (PoolCfgD.mk (.next k)) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgD.mk (.retV (.chan ⟨some (.base a)⟩)
          (.chanStK .close [] [] env k))) @ s ; E {{ Φ }} := by
  iintro ⟨Hpt, Hcont⟩
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hpins⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hpins
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id
      = some (⟨none, .chanData buf cap false⟩ : HeapCell)⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a)
      = some (⟨none, .chanData buf cap false⟩ : HeapCell) := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hload : loadLoc σ₁ (.base a) = .ok (.chanData buf cap false) :=
    loadLoc_base_of_lookup hlook
  have hcell : chanCell σ₁ (.base a) = .ok (buf, cap, false) := by
    unfold chanCell
    rw [hload]
    rfl
  have hstore : storeLoc σ₁ (.base a) (.chanData buf cap true)
      = .ok { σ₁ with
          heap := Heap.set σ₁.heap (.base a) (⟨none, .chanData buf cap true⟩ : HeapCell) } := by
    simp [storeLoc, hlook, coerceStoredValue, Bind.bind, Except.bind]
  have happly : applyChanOp σ₁ .close
      (((GoValue.chan ⟨some (.base a)⟩) :: ([] : List GoValue)).reverse) env k
      = .ok (.next k, { σ₁ with
          heap := Heap.set σ₁.heap (.base a) (⟨none, .chanData buf cap true⟩ : HeapCell) }) := by
    simp [applyChanOp, valueAsChan, hcell, hstore, Bind.bind, Except.bind]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨.next k⟩, _, [],
        GoPrimStepD.step (.lift (.lift (Step.chanStApply happly)))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨c₂⟩ := e₂
  have hshape : c₂ = Config.next k
      ∧ σ₂ = { σ₁ with
          heap := Heap.set σ₁.heap (.base a) (⟨none, .chanData buf cap true⟩ : HeapCell) }
      ∧ eₜ = [] := by
    cases Hstep with
    | step st =>
      cases st with
      | lift ste =>
        cases ste with
        | lift sq =>
          cases sq with
          | chanStApply h =>
            rw [happly] at h
            injection h with h
            injection h with h1 h2
            exact ⟨h1.symm, h2.symm, by simp⟩
          | chanStApplyPanic h =>
            rw [happly] at h
            cases h
        | spawn hsp' _ => simp [spawnPlan] at hsp'
      | wake hblk' _ => simp [isBlockedConfig] at hblk'
      | pairRelease hblk' _ => simp [isBlockedConfig] at hblk'
      | pairArrive hti hblc hpair hidx happ hproj =>
        rcases hpair with hs | ⟨os, sel, hm, -⟩
        · have hplan := arrivalCases_chanStK_single hs
          simp only [List.reverse_cons, List.reverse_nil,
            List.nil_append] at hplan
          rw [chanArrivalPlan_close] at hplan
          injection hplan with hplan
          cases hplan
        · exact (arrivalCases_chanStK_not_multi hm).elim
      | selCommit hex _ =>
        obtain ⟨th, ii, os, sel, hti, hm, -⟩ := hex
        exact (arrivalCases_chanStK_not_multi hm).elim
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  imod (genHeap_update (v₂ := (⟨none, .chanData buf cap true⟩ : HeapCell)))
    $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imod Hclose
  imodintro
  simp only [Algebra.BigOpL.bigOpL_nil]
  isplitl [Hσ]
  · isplitl [Hσ]
    · iapply (genHeapInterp_eqv
        (fun kk => (heapToMap_set_base σ₁.heap a
          ⟨none, .chanData buf cap true⟩ kk).symm)) $$ Hσ
    · ipureintro
      exact ⟨hfns, hmeths, htypes, hwf.set_existing hlook⟩
  isplitl [Hpt Hcont]
  · iapply Hcont $$ Hpt
  · itrivial

/-- **The PARKED zero-target RECEIVER on a rendezvous channel.** Wake
refuted (empty open cell); the `pairRelease` successors are the
SELF-step (Löb-absorbed) and `.next k` — the latter covering both a
real delivery (value discarded by the zero-target form) and a wholly
phantom release with no delivery at all (S1 audit fix round; see
`wpD_blocked_send_rendezvous_inv`'s docstring and
`crossChannelSendRelease`). -/
theorem wpD_blocked_recv_nil_rendezvous_inv {elem : Ty} {env : LocalEnv}
    {k : Cont}
    (hN : ↑N ⊆ E)
    (hcv : cell.value = .chanData #[] 0 false) :
    Iris.inv N (iprop(a.id ↦ cell))
      ∗ WP (PoolCfgD.mk (.next k)) @ s ; E {{ Φ }}
      ⊢ WP (PoolCfgD.mk (.blockedRecv (some (.base a)) [] elem env k))
          @ s ; E {{ Φ }} := by
  iintro ⟨#Hinv, Hcont⟩
  iloeb as IH
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hpins⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hpins
  imod (inv_acc hN) $$ Hinv with ⟨HI, HcloseI⟩
  imod HI with Hpt
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some cell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some cell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hload : loadLoc σ₁ (.base a) = .ok (.chanData #[] 0 false) := by
    have h := loadLoc_base_of_lookup hlook
    rw [hcv] at h
    exact h
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨.blockedRecv (some (.base a)) [] elem env k⟩, σ₁, [],
        GoPrimStepD.step (stepDC_parked_spin rfl hload)⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨c₂⟩ := e₂
  have hshape : (c₂ = Config.blockedRecv (some (.base a)) [] elem env k
        ∨ c₂ = Config.next k) ∧ σ₂ = σ₁ ∧ eₜ = [] := by
    cases Hstep with
    | step st =>
      cases st with
      | lift ste =>
        cases ste with
        | lift sq => cases sq
        | spawn hsp' _ => simp [spawnPlan] at hsp'
      | wake hblk' hres => exact (resumeThread_rendezvous_recv hload hres).elim
      | pairArrive hti hblc hpair hidx happ hproj =>
        simp [isBlockedConfig] at hblc
      | selCommit hex _ =>
        obtain ⟨th, ii, os, sel, hti, hm, -⟩ := hex
        exact absurd (arrivalCases_blocked rfl hm) (by simp)
      | pairRelease hblk' hex =>
        obtain ⟨σ₀, th, ii, jj, bc, cs, idx, ts', hidx, hj, hij, happ, hproj⟩ := hex
        obtain ⟨j', ci', cj', hts, -, hrecv⟩ := applyPairing_partner_write happ
        subst hts
        have hjlt : jj < th.size := (Array.getElem?_eq_some_iff.mp hj).1
        by_cases hjj' : jj = j'
        · subst hjj'
          have hpr : ((th.setIfInBounds ii ci').setIfInBounds jj cj')[jj]?
              = some cj' := by
            simp [Array.size_setIfInBounds, hjlt]
          rw [hpr] at hproj
          injection hproj with hproj
          have hcj := hrecv _ _ _ _ hj
          exact ⟨.inr (hproj.symm.trans hcj), rfl, by simp⟩
        · have hpr : ((th.setIfInBounds ii ci').setIfInBounds j' cj')[jj]?
              = some (Config.blockedRecv (some (.base a)) [] elem env k) := by
            rw [Array.getElem?_setIfInBounds_ne (fun h => hjj' h.symm),
              Array.getElem?_setIfInBounds_ne hij]
            exact hj
          rw [hpr] at hproj
          injection hproj with hproj
          exact ⟨.inl hproj.symm, rfl, by simp⟩
  obtain ⟨hc, rfl, rfl⟩ := hshape
  imod Hclose
  ihave HIc : iprop(▷ (a.id ↦ cell)) $$ [Hpt]
  · inext
    iexact Hpt
  imod HcloseI $$ HIc
  imodintro
  simp only [Algebra.BigOpL.bigOpL_nil]
  isplitl [Hσ]
  · isplitl [Hσ]
    · iexact Hσ
    · ipureintro
      exact ⟨hfns, hmeths, htypes, hwf⟩
  isplitl [IH Hcont]
  · rcases hc with rfl | rfl
    · iapply IH $$ Hcont
    · iexact Hcont
  · itrivial

end

end GoLean.Iris
