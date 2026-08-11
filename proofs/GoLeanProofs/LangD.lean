import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import GoLean.GoCore.MultiSound
import GoLean.GoCore.MultiStreams
import GoLeanProofs.Ghost
import GoLeanProofs.Adequacy
import GoLeanProofs.SurfaceBridge
import GoLeanProofs.LangC

/-!
# The DECOMPOSED per-thread Language (spec-parity slice 4)

The `StepM` pairing decomposition through iris-lean's one-thread-step
`Language` interface — the recorded channels-arc successor debt, built
per `docs/2026-08-10_gospecc-decomposition.md` §§3–4. `StepDC` is a
PROOF-LAYER per-thread relation (the machine is untouched): `StepEC`'s
rules (sequential lift + spawn + the `.spawned` strip) plus the
park-side rules a pairing needs — `wake` (the parked re-attempt,
`resumeThread`), `pairArrive` (the arriving side of a pairing takes its
own successor AND the pairing's whole state delta), `pairRelease` (the
parked partner takes its released config, state-preserving), and
`selCommit` (the L2-picked cell commit, per-thread invisible pick).

**The envelope is deliberately WIDER than the machine's** (design note
§3): partner existence, picks, and delivered values are ∃-quantified
inside the rules, because a per-thread rule cannot see other threads.
That is sound for this module's one consuming direction — the
SIMULATION (`stepM_erasedD`: every pool-machine step is 1–2 erased
D-Language steps) and the run erasure (`execProg_erasedD`), which feed
thread-pool adequacy. A WP proved against this Language must absorb
the wider envelope (a parked receiver may release with ANY delivered
value) — the channel WP law family + protocol layer that constrain it
are the recorded successor consumers, NOT built here (no inert
scaffolding). A `StepDC` bug can make a WP unprovable or a simulation
case fail; it can never make a false exported statement provable — the
exported judgments quantify `execProg` alone.

Intermediate Language states inside a decomposed pairing are proof
artifacts: the arriving step carries the WHOLE delta (`σ → σ''`) and
the partner's release is state-preserving at `σ''` — the §2
attribution fact of the design note is thereby not needed for the
simulation (recorded there; it shapes the future WP laws instead).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open Iris.ProgramLogic.Language.Notation
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface
open Iris.BI

namespace GoLean.Iris

/-- Per-goroutine configuration on the DECOMPOSED concurrent carrier
(a distinct one-field wrapper so this Language instance coexists with
the sequential one and slice 5's `PoolCfg`). -/
structure PoolCfgD where
  c : Config

/-- The arrival analysis produced a pairing plan `(bc, cs)` — either
the singleton analysis or an L2-picked `.pair` member of the
multi-ready analysis (the pick itself is per-thread invisible, hence
∃-quantified). -/
def PairAnalysis (σ : ExecState) (threads : Array Config) (i : Nat)
    (c : Config) (bc : Config) (cs : List (Nat × PairTarget)) : Prop :=
  arrivalCases σ threads i c = .ok (.single bc cs)
    ∨ ∃ (os : List ArrivalOutcome) (sel : Nat),
        arrivalCases σ threads i c = .ok (.multi os)
          ∧ os[sel]? = some (ArrivalOutcome.pair bc cs)

/-- The decomposed per-thread relation (module docstring). Proof
infrastructure, exactly like `Step`/`StepE`/`StepM`/`StepEC`. -/
inductive StepDC : Config → ExecState → Config → ExecState → List Config → Prop where
  /-- Sequential steps + the spawn (`StepE`), verbatim. -/
  | lift {c σ c' σ' efs} : StepE c σ c' σ' efs → StepDC c σ c' σ' efs
  /-- The post-spawn marker strip (thread-local, as in `StepEC`). -/
  | strip {k σ} : StepDC (.spawned k) σ (.next k) σ []
  /-- The parked re-attempt against the cell (`StepM.wake`'s payload —
  already per-thread: it reads only the shared state and own config). -/
  | wake {c σ c' σ'} :
      isBlockedConfig c = true →
      resumeThread σ c = .ok (c', σ') →
      StepDC c σ c' σ' []
  /-- The ARRIVING side of a pairing: the thread at the channel/select
  apply position steps to its own `applyPairing` projection carrying
  the pairing's WHOLE state delta; the partner pool and picks are
  ∃-quantified (per-thread invisibility — the wider envelope). -/
  | pairArrive {c σ} {threads : Array Config} {i : Nat} {bc : Config}
      {cs : List (Nat × PairTarget)} {idx : Nat}
      {ts' : Array Config} {σ'' : ExecState} {c' : Config} :
      threads[i]? = some c →
      isBlockedConfig c = false →
      PairAnalysis σ threads i c bc cs →
      (hidx : idx < cs.length) →
      applyPairing σ threads i bc cs[idx] = .ok (ts', σ'') →
      ts'[i]? = some c' →
      StepDC c σ c' σ'' []
  /-- The PARKED side of a pairing: a blocked config releases to its
  `applyPairing` projection, state-preserving — the delta was carried
  by the arriving step; the pairing's pre-state and everything else
  are ∃-quantified. -/
  | pairRelease {p : Config} {σ'' : ExecState} {p' : Config} :
      isBlockedConfig p = true →
      (∃ (σ₀ : ExecState) (threads : Array Config) (i j : Nat)
         (bc : Config) (cs : List (Nat × PairTarget)) (idx : Nat)
         (ts' : Array Config) (hidx : idx < cs.length),
         threads[j]? = some p ∧ i ≠ j ∧
           applyPairing σ₀ threads i bc cs[idx] = .ok (ts', σ'')
           ∧ ts'[j]? = some p') →
      StepDC p σ'' p' σ'' []
  /-- The L2-picked CELL commit of a multi-ready select arrival
  (`StepM.pickCommit`'s payload; the pick is per-thread invisible). -/
  | selCommit {c : Config} {σ : ExecState} {cl : EvClause}
      {env : LocalEnv} {k : Cont} {c' : Config} {σ' : ExecState} :
      (∃ (threads : Array Config) (i : Nat) (os : List ArrivalOutcome)
         (sel : Nat),
         threads[i]? = some c
           ∧ arrivalCases σ threads i c = .ok (.multi os)
           ∧ os[sel]? = some (.commit cl env k)) →
      commitClause σ env k cl = .ok (c', σ') →
      StepDC c σ c' σ' []

/-- A spawn position is not the terminal (feeds `val_stuck`; the
`LangC` helper, restated here — it is `private` there). -/
private theorem spawnPlanD_toVal_aux {c : Config}
    {p : GoValue × List GoValue × Cont} (h : spawnPlan c = some p) :
    (match c with
      | Config.next Cont.stop => some ()
      | _ => (none : Option Unit)) = none := by
  match c, h with
  | .retV _ (.goCalleeK [] _ _), _ => rfl
  | .retV _ (.goArgsK _ _ [] _ _), _ => rfl

instance : ToVal PoolCfgD Unit where
  toVal e := match e.c with | .next .stop => some () | _ => none
  ofVal _ := ⟨.next .stop⟩
  coe_of_toVal_eq_some {e v} h := by
    obtain ⟨c⟩ := e
    cases c with
    | next k => cases k <;> simp_all
    | _ => simp_all
  toVal_coe _ := rfl

/-- The decomposed primitive step: one goroutine's `StepDC` against the
shared state, forked children appended. -/
inductive GoPrimStepD :
    PoolCfgD × ExecState → List Unit → PoolCfgD × ExecState × List PoolCfgD → Prop where
  | step {c σ c' σ' efs} : StepDC c σ c' σ' efs →
      GoPrimStepD (⟨c⟩, σ) [] (⟨c'⟩, σ', efs.map PoolCfgD.mk)

instance : PrimStep PoolCfgD ExecState (List Unit) where
  primStep := GoPrimStepD

/-- A blocked configuration is not the terminal. -/
private theorem blocked_toVal_aux {c : Config}
    (h : isBlockedConfig c = true) :
    (match c with
      | Config.next Cont.stop => some ()
      | _ => (none : Option Unit)) = none := by
  match c, h with
  | .blockedSend _ _ _, _ => rfl
  | .blockedRecv _ _ _ _ _, _ => rfl
  | .blockedSelect _ _ _, _ => rfl
  | .blockedSync _ _ _ _, _ => rfl

/-- A non-terminal configuration's `toVal` is `none`. -/
private theorem toVal_aux_of_ne {c : Config} (h : c ≠ .next .stop) :
    (match c with
      | Config.next Cont.stop => some ()
      | _ => (none : Option Unit)) = none := by
  cases c <;> try rfl
  case next k => cases k <;> first | rfl | exact absurd rfl h

/-- The terminal's arrival analysis is `.cellPath` (it is not a
channel/select apply position). -/
private theorem arrival_terminal {σ : ExecState} {threads : Array Config}
    {i : Nat} {a : ArrivalAnalysis}
    (h : arrivalCases σ threads i (.next .stop) = .ok a) : a = .cellPath := by
  unfold arrivalCases at h
  simp only [pure_eq_ok] at h
  injection h with h
  exact h.symm

instance : Language PoolCfgD ExecState Unit Unit where
  val_stuck h := by
    cases h with
    | step st =>
      cases st with
      | lift ste =>
        cases ste with
        | lift sq => cases sq <;> rfl
        | spawn hsp hstep => exact spawnPlanD_toVal_aux hsp
      | strip => rfl
      | wake hblk _ => exact blocked_toVal_aux hblk
      | pairRelease hblk _ => exact blocked_toVal_aux hblk
      | pairArrive hti hblk hpair hidx happly hproj =>
        refine toVal_aux_of_ne ?_
        rintro rfl
        rcases hpair with hs | ⟨os, sel, hm, -⟩
        · cases arrival_terminal hs
        · cases arrival_terminal hm
      | selCommit hex _ =>
        obtain ⟨threads, i, os, sel, hti, hm, -⟩ := hex
        refine toVal_aux_of_ne ?_
        rintro rfl
        cases arrival_terminal hm

instance : Inhabited PoolCfgD := ⟨⟨.next .stop⟩⟩

/-! ## The simulation: every pool-machine step is 1–2 erased D-steps -/

/-- Shape inversion of a successful pairing: the candidate names a
partner index `j` whose pre-config is BLOCKED, and the result pool is
exactly the two-point update. (The arms are walked once; nothing else
about the arm content is needed by the simulation.) -/
theorem applyPairing_shape {s : ExecState} {threads : Array Config}
    {i : Nat} {bc : Config} {cand : Nat × PairTarget}
    {ts' : Array Config} {σ'' : ExecState}
    (h : applyPairing s threads i bc cand = .ok (ts', σ'')) :
    ∃ (j : Nat) (pc ci' cj' : Config),
      threads[j]? = some pc ∧ isBlockedConfig pc = true
        ∧ ts' = (threads.setIfInBounds i ci').setIfInBounds j cj' := by
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
          cases pc <;>
            try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedRecv ch2 targets elem2 envr kr =>
            simp only [bind_eq_ok] at h
            obtain ⟨⟨buf, cap, closed⟩, -, h⟩ := h
            split at h
            · simp only [bind_eq_ok] at h
              obtain ⟨⟨cr, s₂⟩, -, h⟩ := h
              simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              exact ⟨j, _, _, _, hj, rfl, h.1.symm⟩
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
          cases pc <;>
            try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedSelect evs envs ks =>
            cases hev : evs[ci]? with
            | none => simp [hev, throw, throwThe, MonadExceptOf.throw] at h
            | some cl =>
              simp only [hev] at h
              cases cl <;>
                try (simp [throw, throwThe, MonadExceptOf.throw] at h)
              case recvEv chv targets elem2 body =>
                simp only [bind_eq_ok] at h
                obtain ⟨⟨buf, cap, closed⟩, -, h⟩ := h
                split at h
                · simp only [bind_eq_ok] at h
                  obtain ⟨⟨cs', s₂⟩, -, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  exact ⟨j, _, _, _, hj, rfl, h.1.symm⟩
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
          cases pc <;>
            try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedSend ch2 vs ks =>
            simp only [bind_eq_ok] at h
            obtain ⟨⟨buf, cap, closed⟩, -, h⟩ := h
            cases hbuf : buf[0]? with
            | none =>
              simp only [hbuf, bind_eq_ok] at h
              obtain ⟨⟨cr, s₂⟩, -, h⟩ := h
              simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              exact ⟨j, _, _, _, hj, rfl, h.1.symm⟩
            | some hd =>
              simp only [hbuf, bind_eq_ok] at h
              obtain ⟨s₁, -, ⟨cr, s₂⟩, -, h⟩ := h
              simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              exact ⟨j, _, _, _, hj, rfl, h.1.symm⟩
    case selectWaiter j ci =>
      cases ch
      case none => simp [applyPairing, throw, throwThe, MonadExceptOf.throw] at h
      case some loc =>
        simp only [applyPairing] at h
        cases hj : threads[j]? with
        | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
        | some pc =>
          simp only [hj] at h
          cases pc <;>
            try (simp [throw, throwThe, MonadExceptOf.throw] at h)
          case blockedSelect evs envs ks =>
            cases hev : evs[ci]? with
            | none => simp [hev, throw, throwThe, MonadExceptOf.throw] at h
            | some cl =>
              simp only [hev] at h
              cases cl <;>
                try (simp [throw, throwThe, MonadExceptOf.throw] at h)
              case sendEv chv vv selem body =>
                simp only [bind_eq_ok] at h
                obtain ⟨v', -, ⟨buf, cap, closed⟩, -, h⟩ := h
                cases hbuf : buf[0]? with
                | none =>
                  simp only [hbuf, bind_eq_ok] at h
                  obtain ⟨⟨cr, s₂⟩, -, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  exact ⟨j, _, _, _, hj, rfl, h.1.symm⟩
                | some hd =>
                  simp only [hbuf, bind_eq_ok] at h
                  obtain ⟨s₁, -, ⟨cr, s₂⟩, -, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  exact ⟨j, _, _, _, hj, rfl, h.1.symm⟩
  case blockedSelect evs env k =>
    -- the catch-all pass above already unfolded `applyPairing` here
    -- (this row's original pattern binds the target as a variable)
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
            cases pc <;>
              try (simp [throw, throwThe, MonadExceptOf.throw] at h)
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
                  exact ⟨j, _, _, _, hj, rfl, h.1.symm⟩
                | some hd =>
                  simp only [hbuf, bind_eq_ok] at h
                  obtain ⟨s₁, -, ⟨ci', s₂⟩, -, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  exact ⟨j, _, _, _, hj, rfl, h.1.symm⟩
      case sendEv chv vv selem body =>
        cases ct
        case selectWaiter j ci =>
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case opWaiter j =>
          cases hj : threads[j]? with
          | none => simp [hj, throw, throwThe, MonadExceptOf.throw] at h
          | some pc =>
            simp only [hj] at h
            cases pc <;>
              try (simp [throw, throwThe, MonadExceptOf.throw] at h)
            case blockedRecv ch2 targetsr elemr envr kr =>
              cases hcl : chanValueLoc chv with
              | none => simp [hcl, throw, throwThe, MonadExceptOf.throw] at h
              | some loc =>
                simp only [hcl, bind_eq_ok] at h
                obtain ⟨⟨buf, cap, closed⟩, -, h⟩ := h
                split at h
                · simp only [bind_eq_ok] at h
                  obtain ⟨v', -, ⟨cr, s₂⟩, -, h⟩ := h
                  simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
                  exact ⟨j, _, _, _, hj, rfl, h.1.symm⟩
                · simp [throw, throwThe, MonadExceptOf.throw] at h


/-- One D-step of the thread at position `j` of a pool list, as an
erased thread-pool step (the `t₁/t₂` split mechanized once). -/
theorem poolStepD_at {l : List PoolCfgD} {j : Nat} {e e' : PoolCfgD}
    {σ σ' : ExecState} {efs : List PoolCfgD}
    (hj : l[j]? = some e)
    (hprim : GoPrimStepD (e, σ) [] (e', σ', efs)) :
    ((l, σ) : List PoolCfgD × ExecState) -·->ₜₚ (l.set j e' ++ efs, σ') := by
  have hlt : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
  have hget : l[j] = e := by
    have := (List.getElem?_eq_some_iff.mp hj).2
    exact this
  have hdec : l = l.take j ++ e :: l.drop (j + 1) := by
    rw [← hget, List.getElem_cons_drop hlt, List.take_append_drop]
  have hdec' : l.set j e' ++ efs
      = (l.take j ++ e' :: l.drop (j + 1)) ++ efs := by
    rw [List.set_eq_take_append_cons_drop]
    simp [hlt]
  refine ⟨[], ?_⟩
  have hpair : ((l, σ) : List PoolCfgD × ExecState)
      = (l.take j ++ e :: l.drop (j + 1), σ) := by rw [← hdec]
  rw [hdec', hpair]
  exact Language.Step.of_primStep hprim (t₁ := l.take j) (t₂ := l.drop (j + 1))

/-- The pool list of a `MultiConfig` on the D-carrier. -/
def poolOf (m : MultiConfig) : List PoolCfgD × ExecState :=
  (m.threads.toList.map PoolCfgD.mk, m.shared)

/-- Array-index facts lifted to the mapped pool list. -/
private theorem poolOf_get {threads : Array Config} {i : Nat} {c : Config}
    (hti : threads[i]? = some c) :
    (threads.toList.map PoolCfgD.mk)[i]? = some ⟨c⟩ := by
  simp [List.getElem?_map, Array.getElem?_toList, hti]

/-- The two-step pairing decomposition (shared by `pair`/`pickPair`):
the arriving thread's step carries the whole delta, the parked
partner's release is state-preserving. -/
theorem pair_erasedD {m : MultiConfig} {i : Nat} {c bc : Config}
    {cs : List (Nat × PairTarget)} {idx : Nat}
    {ts' : Array Config} {σ'' : ExecState} {cur : Nat}
    (hti : m.threads[i]? = some c)
    (hblc : isBlockedConfig c = false)
    (hpair : PairAnalysis m.shared m.threads i c bc cs)
    (hidx : idx < cs.length)
    (happly : applyPairing m.shared m.threads i bc cs[idx] = .ok (ts', σ'')) :
    poolOf m -·->ₜₚ* poolOf ⟨ts', σ'', cur⟩ := by
  obtain ⟨j, pc, ci0, cj0, hj, hpcblk, hts⟩ := applyPairing_shape happly
  have hilt : i < m.threads.size := (Array.getElem?_eq_some_iff.mp hti).1
  have hjlt : j < m.threads.size := (Array.getElem?_eq_some_iff.mp hj).1
  have hne : i ≠ j := by
    rintro rfl
    rw [hti] at hj
    injection hj with hj
    rw [← hj, hblc] at hpcblk
    cases hpcblk
  have hproji : ts'[i]? = some ci0 := by
    subst hts
    rw [Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
    simp [hilt]
  have hprojj : ts'[j]? = some cj0 := by
    subst hts
    simp [Array.size_setIfInBounds, hjlt]
  have hstep1 := poolStepD_at (poolOf_get hti)
    (.step (.pairArrive hti hblc hpair hidx happly hproji))
  have hj1 : ((m.threads.toList.map PoolCfgD.mk).set i ⟨ci0⟩)[j]?
      = some ⟨pc⟩ := by
    rw [List.getElem?_set_ne hne]
    exact poolOf_get hj
  have hstep2 := poolStepD_at hj1
    (.step (.pairRelease hpcblk
      ⟨m.shared, m.threads, i, j, bc, cs, idx, ts', hidx, hj, hne, happly,
        hprojj⟩))
  simp only [List.map_nil, List.append_nil] at hstep1 hstep2
  refine .head hstep1 (.tail .refl ?_)
  have hpool : poolOf ⟨ts', σ'', cur⟩
      = (((m.threads.toList.map PoolCfgD.mk).set i ⟨ci0⟩).set j ⟨cj0⟩,
          σ'') := by
    subst hts
    simp [poolOf, Array.toList_setIfInBounds, List.map_set]
  rw [hpool]
  exact hstep2

/-- **THE SIMULATION** (design note §4.1): every pool-machine step is
one or two erased D-Language steps between the corresponding pools —
`thread`/`spawned`/`wake`/`pickCommit` one step each, the two pairing
rules TWO (the arriving side carrying the whole state delta, then the
parked partner's state-preserving release). -/
theorem stepM_erasedD {m m' : MultiConfig} (h : StepM m m') :
    poolOf m -·->ₜₚ* poolOf m' := by
  cases h with
  | thread hpick hti hblc harr hstep =>
    refine .tail .refl ?_
    have hs := poolStepD_at (poolOf_get hti) (.step (.lift hstep))
    simp only [poolOf, Array.toList_append, Array.toList_setIfInBounds,
      List.map_set, List.map_append]
    exact hs
  | spawned hpick hti =>
    refine .tail .refl ?_
    have hs := poolStepD_at (poolOf_get hti) (.step (.strip (σ := m.shared)))
    simp only [List.map_nil, List.append_nil] at hs
    simp only [poolOf, Array.toList_setIfInBounds, List.map_set]
    exact hs
  | wake hpick hti hblk hres =>
    refine .tail .refl ?_
    have hs := poolStepD_at (poolOf_get hti) (.step (.wake hblk hres))
    simp only [List.map_nil, List.append_nil] at hs
    simp only [poolOf, Array.toList_setIfInBounds, List.map_set]
    exact hs
  | pickCommit hpick hti hblc hsp harr hos hcommit =>
    refine .tail .refl ?_
    have hs := poolStepD_at (poolOf_get hti)
      (.step (.selCommit ⟨_, _, _, _, hti, harr, hos⟩ hcommit))
    simp only [List.map_nil, List.append_nil] at hs
    simp only [poolOf, Array.toList_setIfInBounds, List.map_set]
    exact hs
  | pair hpick hti hblc hsp harr hidx happly =>
    exact pair_erasedD hti hblc (.inl harr) hidx happly
  | pickPair hpick hti hblc hsp harr hos hidx happly =>
    exact pair_erasedD hti hblc (.inr ⟨_, _, harr, hos⟩) hidx happly

/-! ## Run erasure: a completed `execProg` run is a D-Language trace -/

/-- `mainOutcome?` inversion at `.normal`: main's config is the
terminal and the joined state is the shared one. -/
private theorem mainOutcome_normal_inv {m : MultiConfig} {σf : ExecState}
    (h : m.mainOutcome? = some (.normal σf)) :
    m.threads[0]? = some (.next .stop) ∧ σf = m.shared := by
  unfold MultiConfig.mainOutcome? at h
  cases hti : m.threads[0]? with
  | none => rw [hti] at h; cases h
  | some c =>
    rw [hti] at h
    match c, h with
    | .next .stop, h =>
      injection h with h
      injection h with h
      exact ⟨rfl, h.symm⟩
    | .returning .stop, h => injection h with h; cases h
    | .breaking .stop, h => injection h with h; cases h
    | .continuing .stop, h => injection h with h; cases h

/-- A pool whose main is the `.normal` terminal, as a D-pool list with
the VALUE at the head. -/
private theorem poolOf_main_normal {m : MultiConfig} {σf : ExecState}
    (h : m.mainOutcome? = some (.normal σf)) :
    ∃ rest, poolOf m = (⟨.next .stop⟩ :: rest, σf) := by
  obtain ⟨hti, rfl⟩ := mainOutcome_normal_inv h
  rw [← Array.getElem?_toList] at hti
  cases hl : m.threads.toList with
  | nil => rw [hl] at hti; cases hti
  | cons c0 tail =>
    rw [hl] at hti
    injection hti with hti
    refine ⟨tail.map PoolCfgD.mk, ?_⟩
    simp [poolOf, hl, hti]

/-- **Run erasure, loop level**: every `.ok (.normal σf)` run of the
detecting pool loop is an erased D-Language trace from the pool to one
whose HEAD (main) is the terminal VALUE at the joined state — the
`raceUpdate` verdicts along the run are simply discarded (the run
completed, so each succeeded). -/
theorem execProgLoop_erasedD :
    ∀ {fuel : Nat} {m : MultiConfig} {r : RaceState} {ch ch' : Choices}
      {σf : ExecState},
      execProgLoop fuel m r ch = .ok (.normal σf, ch') →
      ∃ rest, poolOf m -·->ₜₚ* (⟨.next .stop⟩ :: rest, σf) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m r ch ch' σf h
    rw [execProgLoop_unfold] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · split at h
        · rename_i out hmain
          split at h
          all_goals (repeat split at h)
          all_goals
            first
            | (simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
               rw [h.1] at hmain
               obtain ⟨rest, hp⟩ := poolOf_main_normal hmain
               exact ⟨rest, hp ▸ .refl⟩)
            | simp [throw, throwThe, MonadExceptOf.throw] at h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel ih =>
    intro m r ch ch' σf h
    rw [execProgLoop_unfold] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · split at h
        · rename_i out hmain
          split at h
          all_goals (repeat split at h)
          all_goals
            first
            | (simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
               rw [h.1] at hmain
               obtain ⟨rest, hp⟩ := poolOf_main_normal hmain
               exact ⟨rest, hp ▸ .refl⟩)
            | (dsimp only at h
               simp only [bind_eq_ok] at h
               obtain ⟨⟨m', ch₁⟩, hsm, r', -, h⟩ := h
               obtain ⟨rest, htr⟩ := ih h
               exact ⟨rest, .trans (stepM_erasedD (stepMulti_sound hsm)) htr⟩)
            | simp [throw, throwThe, MonadExceptOf.throw] at h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · dsimp only at h
            simp only [bind_eq_ok] at h
            obtain ⟨⟨m', ch₁⟩, hsm, r', -, h⟩ := h
            obtain ⟨rest, htr⟩ := ih h
            exact ⟨rest, .trans (stepM_erasedD (stepMulti_sound hsm)) htr⟩

/-- **Run erasure** (design note §4.2): a completed `execProg` run is
an erased D-Language trace from the singleton main pool to a pool with
the terminal VALUE at the head and the joined final state. -/
theorem execProg_erasedD {fuel : Nat} {env : LocalEnv} {σ₀ : ExecState}
    {ch ch' : Choices} {prog : Stmt} {σf : ExecState}
    (h : execProg fuel env σ₀ ch prog = .ok (.normal σf, ch')) :
    ∃ rest : List PoolCfgD,
      (([⟨.exec prog env .stop⟩] : List PoolCfgD), σ₀) -·->ₜₚ*
        (⟨.next .stop⟩ :: rest, σf) := by
  obtain ⟨rest, htr⟩ := execProgLoop_erasedD h
  exact ⟨rest, htr⟩

/-! ## The Iris side: state interpretation, adequacy, and THE EXIT -/

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

/-- The D-carrier's `IrisGS`: the SAME state interpretation as the
sequential and `PoolCfg` instances (gen_heap over the shared
`ExecState` — the state type is unchanged), `forkPost = True`. -/
instance : IrisGS_gen hlc PoolCfgD GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

end

/-- **Strong adequacy with initial-heap handover over the D-Language**
(`go_heap_adequacy_own`'s pool twin — same ghost construction, the
state type is unchanged). -/
theorem goD_heap_adequacy_own {GF : BundledGFunctors} [GoCoreGpreS .hasLC GF]
    (c : PoolCfgD) (σ : ExecState)
    (Ψ : ∀ [GoCoreGS .hasLC GF], Unit → IProp GF)
    (φ : Unit → ExecState → Prop) (hσwf : HeapWf σ)
    (Hwp : ∀ [GoCoreGS .hasLC GF], GoCoreGS.prog GF = σ.functions →
      GoCoreGS.methods GF = σ.methods → GoCoreGS.types GF = σ.types →
      iprop([∗map] l ↦ cell ∈ heapToMap σ.heap, l ↦ cell)
        ⊢@{IProp GF} (WP c {{ v, Ψ v }}))
    (Hext : ∀ [GoCoreGS .hasLC GF], GoCoreGS.prog GF = σ.functions →
      GoCoreGS.methods GF = σ.methods → GoCoreGS.types GF = σ.types →
      ∀ (σ2 : ExecState) (v : Unit),
        iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ2.heap) ∗ Ψ v)
          ⊢ |==> ⌜φ v σ2⌝) :
    adequate .NotStuck c σ φ := by
  refine (adequate_alt _ c σ φ).mpr ?_
  intro t2 σ2 hreach
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
  apply wp_strong_adequacy_gen (GF := GF) (hlc := .hasLC) .NotStuck
    (Hsteps := hsteps) (numLaters := fun _ => 0)
  iintro %Hinv
  imod (genHeap_init_names (GF := GF) (heapToMap σ.heap))
    with ⟨%γh, %γm, Hσ, Hpts, Htok⟩
  letI _ : GoCoreGS .hasLC GF := ⟨⟨γh, γm⟩, σ.functions, σ.methods, σ.types⟩
  imodintro
  iexists (fun σ' _ _ _ =>
    iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ'.heap)
      ∗ ⌜σ'.functions = σ.functions ∧ σ'.methods = σ.methods
          ∧ σ'.types = σ.types ∧ HeapWf σ'⌝))
  iexists [(fun v => Ψ v)], (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  dsimp only
  isplitl [Hσ]
  · isplitl [Hσ]
    · iexact Hσ
    · ipureintro
      exact ⟨rfl, rfl, rfl, hσwf⟩
  isplitl [Hpts]
  · iapply BigSepL2.bigSepL2_singleton
    iapply (Hwp rfl rfl rfl) $$ Hpts
  iintro %es' %t2' %Heq %Hlen %HNS Hst Hwptp _
  icases BigSepL2.bigSepL2_cons_inv_right $$ Hwptp with ⟨%e', %_, %Heq', Hpost, H⟩
  subst Heq' Heq
  icases BigSepL2.bigSepL2_nil_inv_right $$ H with %Heq
  subst Heq
  icases Hst with ⟨Hgh, %Hpure⟩
  cases h : toVal e'
  · iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    grind
  · dsimp only [Option.elim_some]
    imod (Hext rfl rfl rfl σ2 _) $$ [$Hgh $Hpost] with %Hφv
    iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    grind

section

variable {types : TypeEnv} {funcs : Array Func} {methods : Array MethodInfo}
  {env₀ : LocalEnv} {P Q : HProp} {prog : Stmt}

/-- The shared adequacy core over the D-Language (`goSpec_adequate`'s
pool twin): from the WP obligation, an `adequate` fact whose φ carries
the framed native postcondition at the JOINED final state. -/
private theorem goTripleC_adequate
    (Hwp : ∀ [GoCoreGS .hasLC GoCoreS], GoCoreGS.prog GoCoreS = funcs →
      GoCoreGS.methods GoCoreS = methods → GoCoreGS.types GoCoreS = types →
      embed (GF := GoCoreS) P
        ⊢ WP (PoolCfgD.mk (.exec prog env₀ .stop)) {{ _v, embed Q }})
    {hp : Heap} {na : Nat} {hP F : Heaplet}
    (hinit : InitialSplit P hp na hP F funcs env₀ prog) :
    adequate .NotStuck (PoolCfgD.mk (.exec prog env₀ .stop))
      (ExecState.mk (types := types) (functions := funcs) (methods := methods)
        (methodSets := #[]) (heap := hp) (nextAddr := na))
      (fun _ σ2 => ∃ hQ : Heaplet,
        (∀ k, hQ.get? k = none ∨ F.get? k = none)
        ∧ Heaplet.sub hQ (heapToMap σ2.heap)
        ∧ Heaplet.sub F (heapToMap σ2.heap) ∧ sat hQ Q) := by
  refine goD_heap_adequacy_own (GF := GoCoreS) _ _
    (Ψ := fun _ => iprop(ownHeaplet F ∗ embed Q))
    (φ := fun _ σ2 => ∃ hQ : Heaplet,
      (∀ k, hQ.get? k = none ∨ F.get? k = none)
      ∧ Heaplet.sub hQ (heapToMap σ2.heap)
      ∧ Heaplet.sub F (heapToMap σ2.heap) ∧ sat hQ Q)
    hinit.heapBounded ?_ ?_
  · intro _inst hprog hmeths htypes
    have hsplit : ownHeaplet (GF := GoCoreS) (heapToMap hp)
        ⊢ embed P ∗ ownHeaplet F := by
      rw [← heapletOf_eq_heapToMap]
      refine ((BigSepM.bigSepM_eqv_of_perm
        (cover_equiv hinit.disj hinit.cover)).1).trans ?_
      exact ((ownHeaplet_union hinit.disj).1).trans
        (sep_mono (reflect P hP hinit.sat_pre) .rfl)
    exact hsplit.trans ((BI.sep_comm.1).trans
      ((sep_mono .rfl (Hwp hprog hmeths htypes)).trans wp_frame_l))
  · intro _inst _hprog _hmeths _htypes σ2 _v
    iintro ⟨Hσ, HF, HQ⟩
    icases (embed_toHeaplet Q) $$ HQ with ⟨%hQ, %hsQ, HownQ⟩
    ihave %hdisjQF := ownHeaplet_disjoint $$ [$HownQ $HF]
    ihave HU := (ownHeaplet_union hdisjQF).2 $$ [$HownQ $HF]
    ihave %hsub := ownHeaplet_sub $$ [$Hσ $HU]
    imodintro
    ipureintro
    obtain ⟨h1, h2⟩ := sub_union_split hdisjQF hsub
    exact ⟨hQ, hdisjQF, h1, h2, hsQ⟩

/-- **THE EXIT: `GoTripleC` from a D-Language WP** (design note §4.4 —
the sequential `goSpec_of_wp`'s triple half over the POOL carrier).
The pipe: run erasure (`execProg_erasedD`, consuming the pairing
simulation generically) → heap-handover adequacy → `adequate_result`
at the reached pool, whose head is main's terminal VALUE. Per-program
obligations: the WP proof against the D-Language, nothing else. The
SAFETY half (`ProgressExecC`) deliberately does NOT come from this
pipe (design note §4.5 — pool no-stuckness is silent on deadlock and
`.raceDetected` is an interpreter-loop refusal); it comes from the
pool-reachability lane, and `GoSpecC` assembles per-program. -/
theorem goTripleC_of_wpD
    (Hwp : ∀ [GoCoreGS .hasLC GoCoreS], GoCoreGS.prog GoCoreS = funcs →
      GoCoreGS.methods GoCoreS = methods → GoCoreGS.types GoCoreS = types →
      embed (GF := GoCoreS) P
        ⊢ WP (PoolCfgD.mk (.exec prog env₀ .stop)) {{ _v, embed Q }}) :
    GoTripleC types funcs methods env₀ P prog Q := by
  intro hp na hP F hinit fuel ch σf ch' hrun
  obtain ⟨rest, htr⟩ := execProg_erasedD hrun
  have hres := (goTripleC_adequate Hwp hinit).adequate_result rest σf () htr
  obtain ⟨hQ, hd, h1, h2, hs⟩ := hres
  exact ⟨hQ, hd, by rw [heapletOf_eq_heapToMap]; exact h1,
    by rw [heapletOf_eq_heapToMap]; exact h2, hs⟩

end

/-! ## The D-carrier WP laws (ports of the `wpC_*` kit, with the
decomposed rules refuted by shape side-conditions) + the WITNESS -/

/-- Is this configuration a channel/select APPLY position (the shapes
`arrivalCases` inspects)? The `wpD_*` laws refute the pairing/commit
rules with this flag. -/
def chanSelApplyPos : Config → Bool
  | .retV _ (.chanStK _ _ [] _ _) => true
  | .retV _ (.selectOpsK _ _ _ [] _ _) => true
  | _ => false

/-- Away from apply positions the arrival analysis is `.cellPath`,
whatever the pool. -/
theorem arrivalCases_of_nonApply {σ : ExecState} {threads : Array Config}
    {i : Nat} {c : Config} (h : chanSelApplyPos c = false) :
    arrivalCases σ threads i c = .ok .cellPath := by
  unfold arrivalCases
  cases c <;> try rfl
  case retV v k =>
    cases k <;> try rfl
    case chanStK op done pending env kk =>
      cases pending with
      | nil => simp [chanSelApplyPos] at h
      | cons e rest => rfl
    case selectOpsK clauses d done pending env kk =>
      cases pending with
      | nil => simp [chanSelApplyPos] at h
      | cons e rest => rfl

/-- The pairing/commit rules are silent away from apply positions and
blocked shapes (the refutation kit for the pure lifts). -/
theorem stepDC_shape_cases {c : Config} {σ : ExecState} {c' : Config}
    {σ' : ExecState} {efs : List Config}
    (hblk : isBlockedConfig c = false)
    (hpos : chanSelApplyPos c = false)
    (h : StepDC c σ c' σ' efs) :
    StepE c σ c' σ' efs ∨ (∃ k, c = .spawned k ∧ c' = .next k ∧ σ' = σ ∧ efs = []) := by
  cases h with
  | lift hs => exact .inl hs
  | strip => exact .inr ⟨_, rfl, rfl, rfl, rfl⟩
  | wake hb _ => rw [hblk] at hb; cases hb
  | pairRelease hb _ => rw [hblk] at hb; cases hb
  | pairArrive hti hb hpair hidx happly hproj =>
    rcases hpair with hs | ⟨os, sel, hm, -⟩
    · rw [arrivalCases_of_nonApply hpos] at hs
      cases hs
    · rw [arrivalCases_of_nonApply hpos] at hm
      cases hm
  | selCommit hex _ =>
    obtain ⟨threads, i, os, sel, hti, hm, -⟩ := hex
    rw [arrivalCases_of_nonApply hpos] at hm
    cases hm

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- The pure deterministic lift on the D-carrier (`wpC_pure_det`'s
port; two NEW side conditions refute the decomposed rules). -/
theorem wpD_pure_det {c c' : Config}
    (hsp : spawnPlan c = none) (hsc : spawnedCont c = none)
    (hblk : isBlockedConfig c = false) (hpos : chanSelApplyPos c = false)
    (hstep : ∀ σ : ExecState, Step c σ c' σ)
    (hdet : ∀ (σ : ExecState) (c₂ : Config) (σ₂ : ExecState),
      Step c σ c₂ σ₂ → c₂ = c' ∧ σ₂ = σ) :
    (|={E}[E]▷=> £ 1 -∗ WP (PoolCfgD.mk c') @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgD.mk c) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E) (e₂ := PoolCfgD.mk c')
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], ⟨c'⟩, σ, [], GoPrimStepD.step (.lift (.lift (hstep σ)))⟩
      · exact Language.val_stuck (GoPrimStepD.step (.lift (.lift (hstep σ))))
    )
    (Hpuredet := by
      intro σ₁ obs e₂' σ₂ eₜ' h
      cases h with
      | step st =>
        rcases stepDC_shape_cases hblk hpos st with hse | ⟨k, rfl, -⟩
        · cases hse with
          | lift sq =>
            obtain ⟨rfl, rfl⟩ := hdet _ _ _ sq
            exact ⟨rfl, rfl, rfl, rfl⟩
          | spawn hsp' _ =>
            rw [hsp] at hsp'
            cases hsp'
        · simp [spawnedCont] at hsc))
  iexact H

/-- The marker strip on the D-carrier (`wpC_spawned_strip`'s port). -/
theorem wpD_spawned_strip {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗ WP (PoolCfgD.mk (.next k)) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgD.mk (.spawned k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E) (e₂ := PoolCfgD.mk (.next k))
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], ⟨.next k⟩, σ, [], GoPrimStepD.step .strip⟩
      · rfl)
    (Hpuredet := by
      intro σ₁ obs e₂' σ₂ eₜ' h
      cases h with
      | step st =>
        rcases stepDC_shape_cases rfl rfl st with hse | ⟨k', hk, rfl, rfl, rfl⟩
        · cases hse with
          | lift sq => exact absurd sq (step_spawnedMarker_elim rfl)
          | spawn hsp' _ => cases hsp'
        · injection hk with hk
          subst hk
          exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

/-- **THE FORK RULE on the D-carrier** (`wpC_fork`'s port; the same
state-preserving spawn class). -/
theorem wpD_fork {c child : Config} {cv : GoValue} {args : List GoValue}
    {k : Cont}
    (hsp : spawnPlan c = some (cv, args, k))
    (hspawn : ∀ σ : ExecState, σ.functions = GoCoreGS.prog GF →
      σ.methods = GoCoreGS.methods GF → σ.types = GoCoreGS.types GF →
      spawnStep σ cv args k = .ok (.spawned k, child, σ)) :
    ▷ WP (PoolCfgD.mk child) @ s ; ⊤ {{ fun _ => iprop(True) }}
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
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨.spawned k⟩, σ₁, [⟨child⟩],
        GoPrimStepD.step (.lift (.spawn hsp (hspawn σ₁ hfns hmeths htypes)))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  have hshape : e₂ = PoolCfgD.mk (.spawned k) ∧ σ₂ = σ₁
      ∧ eₜ = [PoolCfgD.mk child] := by
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
  imod Hclose
  imodintro
  isplitl [Hσ]
  · isplitl [Hσ]
    · iexact Hσ
    · ipureintro
      exact ⟨hfns, hmeths, htypes, hwf⟩
  isplitl [Hparent]
  · iexact Hparent
  · simp only [Algebra.BigOpL.bigOpL_cons, Algebra.BigOpL.bigOpL_nil]
    isplitl [Hchild]
    · iexact Hchild
    · itrivial

end

/-! ## The witness: a frame-quantified `GoTripleC` on a program that
GENUINELY SPAWNS (the recorded debt's triple half — design note §4.6) -/

/-- The harness-cell pre/post the witness threads through the spawn
(the program never touches the heap, so the triple pins the cell). -/
def spawnNoopCell : HProp := .pointsTo 0 ⟨some (.int .int), .int 0 .int⟩

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

set_option maxHeartbeats 1600000 in
/-- The D-carrier walk of the spawn-noop program with the cell carried
through the fork — `wpC_spawn_noop_witness`'s port, at a REAL pre/post
(the exit consumes exactly this shape). -/
theorem wpD_spawn_noop_witness
    (hprog : GoCoreGS.prog GF = #[noopWorker])
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) spawnNoopCell
      ⊢ WP (PoolCfgD.mk (.exec spawnNoopProg [] .stop))
        {{ _v, embed (GF := GF) spawnNoopCell }} := by
  iintro HP
  -- main: goStmt entry (pure det)
  iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.goStmtEntry)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred1
  -- main: the callee literal evaluates (nullary strict op, pure det)
  iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.evalStrictNullary rfl rfl)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq
      case evalStrictNullary op v hplan happly =>
        simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
        obtain ⟨rfl, -⟩ := hplan
        rw [show applyStrictOp σ (StrictOp.funcValOf ⟨"noopWorker"⟩) []
            = .ok (GoValue.funcVal ⟨"noopWorker"⟩ [], σ) from rfl] at happly
        injection happly with hp
        injection hp with hv hσ
        subst hv
        subst hσ
        exact ⟨rfl, rfl⟩
      case evalStrictNullaryPanic op msg hplan happly =>
        simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
        obtain ⟨rfl, -⟩ := hplan
        rw [show applyStrictOp σ (StrictOp.funcValOf ⟨"noopWorker"⟩) []
            = .ok (GoValue.funcVal ⟨"noopWorker"⟩ [], σ) from rfl] at happly
        cases happly
      all_goals simp_all [strictPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred2
  -- main: THE FORK
  iapply (wpD_fork (hsp := rfl)
    (child := .exec (.seqn #[]) [] (.frame [] [] [] [] .stop false))
    (hspawn := by
      intro σ hf hm ht
      simp +decide [spawnStep, enterFrame, findFunctionIn?, noopWorker,
        dynamicDispatch?, bindParams, allocDecls, pinResultLocs,
        methodInfoByFuncId?, hf, hm, hprog, hmeths,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl []
  · -- the CHILD: empty body under its barrier frame, to the terminal
    inext
    iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.seqn)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred3
    simp only [seqCont]
    iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.seqDone)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred3b
    iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.frameFall)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [loadMany, storeMany, Pure.pure, Except.pure]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred4
    iapply (wp_value' (v := ()))
    itrivial
  · -- the PARENT: strip the marker, stop, deliver the cell
    inext
    iapply wpD_spawned_strip
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred5
    iapply (wp_value' (v := ()))
    iexact HP

end

/-- **The frame-quantified `GoTripleC` on a genuinely SPAWNING
program** — the triple half of the recorded channels-arc debt, paid
through the decomposition pipe (the exit consumed the full pairing
simulation; this program's own traces exercise the spawn/strip lane).
The SAFETY half (`ProgressExecC` at ∀-heap strength) is the
pool-reachability lane's owed first instance — recorded in the slice
build log, not silently dropped; `GoSpecC = GoTripleC ∧ ProgressExecC`
assembles when it lands. -/
theorem spawnNoopTripleC :
    GoTripleC [] #[noopWorker] #[] [] spawnNoopCell spawnNoopProg
      spawnNoopCell :=
  goTripleC_of_wpD (fun hprog hmeths _htypes =>
    wpD_spawn_noop_witness hprog hmeths)

/-- The seeded state for the witness pair below. -/
def spawnNoopSeed : ExecState :=
  { types := [], functions := #[noopWorker], methods := #[],
    heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
    nextAddr := 1 }

/-- ONE HALF of the witness pair (S4 audit round — the pair, not this
theorem alone, is the stated non-vacuity discharge): at the concrete
seeded state every premise of `spawnNoopTripleC`'s `InitialSplit`
discharges, and the triple reads back as a first-order RUN-CONDITIONED
fact — every `.normal` pool completion of the spawning program leaves
the harness cell intact. Run-conditioned readouts are the house form,
shipped WITH a completion pin (`goldenTerminates` /
`forkJoinTerminatesNormallyC` precedents); the completion half here is
`spawnNoopTerminatesNormallyC` below. Interpreter vocabulary only. -/
theorem spawnNoopReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel []
        { types := [], functions := #[noopWorker], methods := #[],
          heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
          nextAddr := 1 }
        ch spawnNoopProg = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 0 .int) := by
  intro fuel ch σf ch' hrun
  have hsat : sat (heapletOf [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)])
      spawnNoopCell := rfl
  have hsplit := InitialSplit.noFrame (P := spawnNoopCell)
    (hp := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)]) (na := 1)
    (funcs := #[noopWorker]) (env₀ := []) (prog := spawnNoopProg)
    hsat (by decide +kernel)
  have hres := spawnNoopTripleC _ 1 _ ∅ hsplit fuel ch σf ch' hrun
  obtain ⟨h, _hd, hsub, _hF, hsatQ⟩ := hres
  rw [show h = (∅ : Heaplet).insert 0 ⟨some (.int .int), .int 0 .int⟩
    from hsatQ] at hsub
  have hget := hsub 0 ⟨some (.int .int), .int 0 .int⟩ (by
    rw [heaplet_get?_eq, heaplet_insert_eq]
    exact LawfulPartialMap.get?_insert_eq rfl)
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hget
  exact loadLoc_base_of_lookup hget

/-- The completion half's kernel certificate: every schedule of the
spawning witness program completes at main's `.normal` with the cell
intact, within fuel 20. -/
theorem spawnNoopAllStreamsCert :
    allStreamsOkPool
      (fun σf => match loadLoc σf (.base ⟨0⟩) with
        | .ok (.int 0 .int) => true
        | _ => false)
      20 ⟨#[.exec spawnNoopProg [] .stop], spawnNoopSeed, 0⟩ {} = true := by
  decide +kernel

/-- THE OTHER HALF of the witness pair (S4 audit round): the seeded
completion pin — the spawning witness program COMPLETES at main's
`.normal` on every choice stream past one fuel bound (the
`forkJoinTerminatesNormallyC` idiom). Together with
`spawnNoopReadoutC` (the run-conditioned verdict) this is the stated
non-vacuity discharge for `spawnNoopTripleC`: the runs exist AND
every one satisfies the triple's readout. The ∀-HEAP safety half
(`ProgressExecC`) — the P-S4-1 debt when this pin landed — is PAID at
channel-logic slice 2 (`Specs/SpawnNoopProgress.lean`,
`spawnNoopProgressC`/`spawnNoopSpecC`); this pin is seed-concrete,
strictly weaker, and does not claim otherwise. -/
theorem spawnNoopTerminatesNormallyC :
    TerminatesNormallyC [] spawnNoopSeed spawnNoopProg := by
  refine ⟨20, fun fuel hfuel ch => ?_⟩
  obtain ⟨σf, ch', hrun, -⟩ :=
    execProgLoop_ok_of_allStreamsOkPool spawnNoopAllStreamsCert ch
  exact ⟨σf, ch', execProgLoop_mono hrun hfuel⟩

end GoLean.Iris
