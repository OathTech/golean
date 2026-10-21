import GoLean.GoCore.Prefix
import GoLean.GoCore.Equations

/-!
# The initialiser's driver against the sequential driver (backlog row 47, raft-proofs G11)

[AGENT lane core/g11-init-driver-1021] 2026-10-21. The raft-proofs campaign states its theorems
over `stepFn` through `Prefix`/`Finish` (`ExecutionStatement.lean`, `Prefix.lean`) and enters a
program through the seeded entry `runProgramSetupSeededM` (`Seed.lean`), whose package
initialisation runs `$pkginit` under `runPkgInitM` → `runInitConfig` (`StepFn.lean`): the
sequential loop `execStmtLoop` with ONE extra guard, the init-phase print refusal
`initPrintRefusal?`, consulted before the fuel match on every configuration that is neither
`.next .stop` nor blocked. `run_ok_iff` and its siblings cover `execStmtLoop` only; this module
relates the init loop to it, so that a successful initialisation IS a `Prefix` of the
initialiser's body to `.next .stop`.

Two layers:

* **Premise-free** (new): `runInitConfig_cases` — the init loop either AGREES with
  `execStmtLoop` (and no configuration reachable within the fuel is a print position) or REFUSES
  by name at a reachable print position; its corollaries `runInitConfig_ok_execStmtLoop`,
  `runInitConfig_ok_noPrint`, `runInitConfig_ok_prefix` (the consumer shape: success is a
  prefix to `.next .stop`) and the premise-free `runInitConfig_ok_iff_execStmtLoop`; for the
  wrapper, `runPkgInitM_ok_prefix` and `runPkgInitM_ok_cases` (no initialiser and the store
  untouched, or a prefix of the initialiser's body).
* **Under the no-print premise** — the G-R4 family of 2026-10-05 (`docs/2026-10-05_setup-equations.md`
  §3), retired with the relational layer on 2026-10-20 (`SetupStatement.lean`/`SetupSound.lean` at tag
  `relational/last-main-2026-10-20`) and restated here with the statements verbatim, the `_stmt`
  indirection dropped: `runInitConfig_eq_execStmtLoop`, `runInitConfig_ok_iff`,
  `runInitConfig_panic_iff`, `runInitConfig_deadlock_iff`, `runInitConfig_fuelOut_iff`,
  `runPkgInitM_some`, `runPkgInitM_ok_iff`. The equation is now a corollary of the dichotomy.

* **From one witnessed run back to the init loop** (fix round F2, the review of 2026-10-21; R8's
  converse): `prefix_det`/`prefix_det_le` (`Prefix` determinism), `applyStmtOp_print` and
  `stepFn_out_of_printOut?` (a successful step at a print position carries its bytes on the label),
  `noPrint_of_prefix_silent`, `runInitConfig_ok_of_prefix_silent`, `runPkgInitM_ok_of_prefix_silent`:
  one `Prefix` of `$pkginit`'s body to `.next .stop` within the fuel whose labels all have
  `out = []` is a successful `runPkgInitM`. The opposite direction (a successful run's labels are
  silent — a full label-form iff) would need the off-apply emptiness lemma
  `printOut? c = none → stepFn ctx s c ch = .ok (c', s', ch', l) → l.out = []`, a whole-`stepFn`
  case analysis not on main (review F3); `runInitConfig_ok_noPrint` is the config-form fact a
  successful run gives.

The init loop's one-step rewriting surface (`runInitConfig_unfold`/`_blocked`/`_nonZero`/`_refused`,
`initPrintRefusal?_zeroCost`) is public and frozen (review F5): the twins of `execStmtLoop_unfold`/
`_nonZero`/`_blocked`, the direct symbolic route under the init loop (one unfolding, one
`stepFn_eqns` rewrite, the guard by evaluation) needing no `Prefix`.

Nothing executable changes: every theorem is about the definitions of `StepFn.lean` as they stand.
Pinned in `Tests/GoCoreContract.lean` (§D) and required by the core audit (`Tests/GoCoreAudit.lean`).
-/

namespace GoLean.GoCore.ExecutionStatement

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-! ## The init loop's one-layer unfolding and its shapes -/

/-- The one-layer unfolding of `runInitConfig`, as an equation (the twin of `execStmtLoop_unfold`). -/
theorem runInitConfig_unfold (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config)
    (ch : Choices) :
    runInitConfig ctx fuel s c ch
      = (match c with
         | .next .stop => .ok (s, ch)
         | .blockedSend _ _ _ => throw .deadlock
         | .blockedRecv _ _ _ _ _ => throw .deadlock
         | .blockedSelect _ _ _ => throw .deadlock
         | .blockedSync _ _ _ _ => throw .deadlock
         | c =>
             match initPrintRefusal? c with
             | some e => throw e
             | none =>
               match fuel with
               | 0 => throw .fuelOut
               | fuel + 1 => do
                   let (c', s', choices', _) ← stepFn ctx s c ch
                   runInitConfig ctx fuel s' c' choices') := by
  rw [runInitConfig.eq_def]
  rfl

/-- The init loop at a blocked configuration is the deadlock at every fuel (no guard is consulted). -/
theorem runInitConfig_blocked {ctx : ProgramCtx} {fuel : Nat} {s : Store} {c : Config}
    {ch : Choices} (hb : Blocked c) : runInitConfig ctx fuel s c ch = .error (.terminal .deadlock) := by
  rcases hb with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
    (rw [runInitConfig_unfold]; rfl)

/-- The init loop at a non-zero-cost configuration whose guard is silent: the entry loop's own shape
— fuel-out at 0, one `stepFn` call then the init loop at `fuel + 1`. -/
theorem runInitConfig_nonZero {ctx : ProgramCtx} {fuel : Nat} {s : Store} {c : Config}
    {ch : Choices} (hz : ¬ ZeroCost c) (hp : initPrintRefusal? c = none) :
    runInitConfig ctx fuel s c ch =
      (match fuel with
       | 0 => .error .fuelOut
       | f + 1 => (stepFn ctx s c ch).bind fun r => runInitConfig ctx f r.2.1 r.1 r.2.2.1) := by
  rw [runInitConfig_unfold]
  unfold ZeroCost Blocked at hz
  split
  · exact absurd (.inl rfl) hz
  · exact absurd (.inr (.inl ⟨_, _, _, rfl⟩)) hz
  · exact absurd (.inr (.inr (.inl ⟨_, _, _, _, _, rfl⟩))) hz
  · exact absurd (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) hz
  · exact absurd (.inr (.inr (.inr (.inr ⟨_, _, _, _, rfl⟩)))) hz
  · rw [hp]
    cases fuel with
    | zero => rfl
    | succ f => simp only [Bind.bind]

/-- The init loop at a non-zero-cost configuration whose guard FIRES: the refusal, at every fuel
(the guard precedes the fuel match, so a print position reached with the fuel spent still refuses
rather than reporting exhaustion). -/
theorem runInitConfig_refused {ctx : ProgramCtx} {fuel : Nat} {s : Store} {c : Config}
    {ch : Choices} {e : Stop} (hz : ¬ ZeroCost c) (hp : initPrintRefusal? c = some e) :
    runInitConfig ctx fuel s c ch = .error e := by
  rw [runInitConfig_unfold]
  unfold ZeroCost Blocked at hz
  split
  · exact absurd (.inl rfl) hz
  · exact absurd (.inr (.inl ⟨_, _, _, rfl⟩)) hz
  · exact absurd (.inr (.inr (.inl ⟨_, _, _, _, _, rfl⟩))) hz
  · exact absurd (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) hz
  · exact absurd (.inr (.inr (.inr (.inr ⟨_, _, _, _, rfl⟩)))) hz
  · rw [hp]
    rfl

/-- The guard is silent at every zero-cost configuration (`printOut?` reads a `print` apply
position only). -/
theorem initPrintRefusal?_zeroCost {c : Config} (hz : ZeroCost c) : initPrintRefusal? c = none := by
  rcases hz with rfl | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> rfl

/-! ## The premise-free dichotomy (G11) -/

/-- **The init loop, up to the init-phase print refusal** (G11, no premise): either every
configuration reachable within the fuel is silent for the guard and the init loop IS
`execStmtLoop`, or a print position is reachable within the fuel and the init loop reports the
guard's refusal reached there. The two arms exclude each other (the first says every reachable
guard is silent, the second exhibits one that fires). -/
theorem runInitConfig_cases (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices) :
    ((∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
        Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) ∧
      runInitConfig ctx fuel s c ch = execStmtLoop ctx fuel s c ch) ∨
    (∃ (n : Nat) (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices) (e : Stop),
      n ≤ fuel ∧ Prefix ctx n s c ch ls sf cf chf ∧ ¬ ZeroCost cf ∧
        initPrintRefusal? cf = some e ∧ runInitConfig ctx fuel s c ch = .error e) := by
  induction fuel generalizing s c ch with
  | zero =>
    rcases zeroCost_cases c with rfl | hb | hz
    · left
      refine ⟨?_, by rw [runInitConfig_unfold, execStmtLoop_unfold]⟩
      intro n σ' c' ch' ls hp _
      cases hp with
      | done => rfl
      | step hs _ => exact absurd (.inl rfl) (stepFn_zeroCost_not_ok hs)
    · left
      refine ⟨?_, by rw [runInitConfig_blocked hb, execStmtLoop_blocked hb]⟩
      intro n σ' c' ch' ls hp _
      cases hp with
      | done => exact initPrintRefusal?_zeroCost (.inr hb)
      | step hs _ => exact absurd (.inr hb) (stepFn_zeroCost_not_ok hs)
    · cases hg : initPrintRefusal? c with
      | some e =>
        right
        exact ⟨0, [], s, c, ch, e, Nat.le_refl 0, .done, hz, hg, runInitConfig_refused hz hg⟩
      | none =>
        left
        refine ⟨?_, by rw [runInitConfig_nonZero hz hg, execStmtLoop_nonZero hz]⟩
        intro n σ' c' ch' ls hp hn
        cases hp with
        | done => exact hg
        | step _ _ => omega
  | succ f ih =>
    rcases zeroCost_cases c with rfl | hb | hz
    · left
      refine ⟨?_, by rw [runInitConfig_unfold, execStmtLoop_unfold]⟩
      intro n σ' c' ch' ls hp _
      cases hp with
      | done => rfl
      | step hs _ => exact absurd (.inl rfl) (stepFn_zeroCost_not_ok hs)
    · left
      refine ⟨?_, by rw [runInitConfig_blocked hb, execStmtLoop_blocked hb]⟩
      intro n σ' c' ch' ls hp _
      cases hp with
      | done => exact initPrintRefusal?_zeroCost (.inr hb)
      | step hs _ => exact absurd (.inr hb) (stepFn_zeroCost_not_ok hs)
    · cases hg : initPrintRefusal? c with
      | some e =>
        right
        exact ⟨0, [], s, c, ch, e, Nat.zero_le _, .done, hz, hg, runInitConfig_refused hz hg⟩
      | none =>
        rw [runInitConfig_nonZero hz hg, execStmtLoop_nonZero hz]
        simp only
        cases hs : stepFn ctx s c ch with
        | error e =>
          left
          refine ⟨?_, rfl⟩
          intro n σ' c' ch' ls hp _
          cases hp with
          | done => exact hg
          | step hs' _ => rw [hs] at hs'; cases hs'
        | ok r =>
          obtain ⟨c₁, s₁, ch₁, l⟩ := r
          simp only [Except.bind]
          rcases ih s₁ c₁ ch₁ with ⟨hnp, heq⟩ | ⟨n, ls, sf, cf, chf, e, hn, hp, hzf, hgf, hr⟩
          · left
            refine ⟨?_, heq⟩
            intro n σ' c' ch' ls hp hn
            cases hp with
            | done => exact hg
            | step hs' hrest =>
              rw [hs] at hs'
              cases hs'
              exact hnp _ _ _ _ _ hrest (Nat.le_of_succ_le_succ hn)
          · right
            exact ⟨n + 1, l :: ls, sf, cf, chf, e, Nat.succ_le_succ hn, .step hs hp, hzf, hgf, hr⟩

/-- A successful init run is a successful `execStmtLoop` run — no premise (a success is never
the guard's refusal). -/
theorem runInitConfig_ok_execStmtLoop {ctx : ProgramCtx} {fuel : Nat} {s sf : Store} {c : Config}
    {ch chf : Choices} (h : runInitConfig ctx fuel s c ch = .ok (sf, chf)) :
    execStmtLoop ctx fuel s c ch = .ok (sf, chf) := by
  rcases runInitConfig_cases ctx fuel s c ch with ⟨_, heq⟩ | ⟨_, _, _, _, _, _, _, _, _, _, hr⟩
  · rwa [← heq]
  · rw [h] at hr; cases hr

/-- Along a successful init run, no configuration reachable within the fuel is a print position
(the guard inspected each one). -/
theorem runInitConfig_ok_noPrint {ctx : ProgramCtx} {fuel : Nat} {s sf : Store} {c : Config}
    {ch chf : Choices} (h : runInitConfig ctx fuel s c ch = .ok (sf, chf)) :
    ∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none := by
  rcases runInitConfig_cases ctx fuel s c ch with ⟨hnp, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, hr⟩
  · exact hnp
  · rw [h] at hr; cases hr

/-- **A successful initialisation is a `Prefix`** (G11's consumer shape): a prefix of length
`n ≤ fuel` to `.next .stop` — `run_ok_iff`'s right-hand side, with no premise. -/
theorem runInitConfig_ok_prefix {ctx : ProgramCtx} {fuel : Nat} {s sf : Store} {c : Config}
    {ch chf : Choices} (h : runInitConfig ctx fuel s c ch = .ok (sf, chf)) :
    ∃ n, n ≤ fuel ∧ ∃ ls, Prefix ctx n s c ch ls sf (.next .stop) chf :=
  (run_ok_iff ctx fuel s sf c ch chf).mp (runInitConfig_ok_execStmtLoop h)

/-! ## The G-R4 family under the no-print premise (statements verbatim, 2026-10-05) -/

/-- **G-R4.** `runInitConfig` is `execStmtLoop` with ONE extra guard — the init-phase print refusal,
consulted before the fuel match on every configuration that is neither `.next .stop` nor blocked —
so under the no-print premise the two loops are EQUAL. No premise on blocked configurations: both
loops classify a blocked configuration as `.deadlock` before any guard, and `stepFn` itself throws
on one, so no `Prefix` passes through a blocked configuration. Now the first arm of
`runInitConfig_cases`, whose second arm the premise excludes. -/
theorem runInitConfig_eq_execStmtLoop {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config}
    {ch : Choices}
    (hnp : ∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n σ c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) :
    runInitConfig ctx fuel σ c ch = execStmtLoop ctx fuel σ c ch := by
  rcases runInitConfig_cases ctx fuel σ c ch with ⟨_, heq⟩ | ⟨n, ls, sf, cf, chf, e, hn, hp, _, hg, _⟩
  · exact heq
  · rw [hnp n sf cf chf ls hp hn] at hg
    cases hg

/-- The premise-free `run_ok_iff` for the init loop: success is `execStmtLoop`'s success WITH the
no-print condition on the configurations reachable within the fuel. -/
theorem runInitConfig_ok_iff_execStmtLoop (ctx : ProgramCtx) (fuel : Nat) (s sf : Store) (c : Config)
    (ch chf : Choices) :
    runInitConfig ctx fuel s c ch = .ok (sf, chf) ↔
      (execStmtLoop ctx fuel s c ch = .ok (sf, chf) ∧
        ∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
          Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) := by
  constructor
  · intro h
    exact ⟨runInitConfig_ok_execStmtLoop h, runInitConfig_ok_noPrint h⟩
  · rintro ⟨h, hnp⟩
    rw [runInitConfig_eq_execStmtLoop hnp]
    exact h

/-- Normal completion of the init loop: a prefix of length `n ≤ fuel` to `.next .stop` (cost 0). -/
theorem runInitConfig_ok_iff (ctx : ProgramCtx) (fuel : Nat) (s sf : Store) (c : Config) (ch chf : Choices)
    (hnp : ∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) :
    runInitConfig ctx fuel s c ch = .ok (sf, chf) ↔
      ∃ n, n ≤ fuel ∧ ∃ ls, Prefix ctx n s c ch ls sf (.next .stop) chf := by
  rw [runInitConfig_eq_execStmtLoop hnp]
  exact run_ok_iff ctx fuel s sf c ch chf

/-- The init loop's panic terminal (an initialiser's unrecovered panic kills the program before
`main`): prefix length plus the abort's cost 1 within the fuel; `markInitPhase` leaves it unmarked. -/
theorem runInitConfig_panic_iff (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices)
    (t : String)
    (hnp : ∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) :
    runInitConfig ctx fuel s c ch = .error (.terminal (.panic t)) ↔
      ∃ (n : Nat) (ls : List StepLabel) (sf : Store) (cf : Config) (chf ch'' : Choices)
        (rec : List PickRecord),
        n + 1 ≤ fuel ∧ Prefix ctx n s c ch ls sf cf chf ∧
          Finish ctx sf cf chf rec (.aborted t sf ch'') 1 := by
  rw [runInitConfig_eq_execStmtLoop hnp]
  exact run_panic_iff ctx fuel s c ch t

/-- The init loop's deadlock: a blocked endpoint at `n ≤ fuel` (cost 0). -/
theorem runInitConfig_deadlock_iff (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices)
    (hnp : ∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) :
    runInitConfig ctx fuel s c ch = .error (.terminal .deadlock) ↔
      ∃ n, n ≤ fuel ∧ ∃ (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
        Prefix ctx n s c ch ls sf cf chf ∧ Finish ctx sf cf chf [] (.deadlock sf chf) 0 := by
  rw [runInitConfig_eq_execStmtLoop hnp]
  exact run_deadlock_iff ctx fuel s c ch

/-- The init loop's fuel-out: the fixed tape's prefix of length exactly `fuel`, ending at a
configuration that is not zero-cost (`markInitPhase` leaves `fuelOut` unmarked — an init-phase
fuel exhaustion is indistinguishable from the subject's by design). -/
theorem runInitConfig_fuelOut_iff (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config) (ch : Choices)
    (hnp : ∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n s c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) :
    runInitConfig ctx fuel s c ch = .error .fuelOut ↔
      ∃ (ls : List StepLabel) (sf : Store) (cf : Config) (chf : Choices),
        Prefix ctx fuel s c ch ls sf cf chf ∧ ¬ ZeroCost cf := by
  rw [runInitConfig_eq_execStmtLoop hnp]
  exact run_fuelOut_iff ctx fuel s c ch

/-! ## The `runPkgInitM` wrapper

`runPkgInitM` with a `$pkginit` PRESENT, in terms of `runInitConfig` on the init configuration — the
body under a targetless barrier frame naming `$pkginit`, the empty environment. The twin of
`Equations.lean`'s `runPkgInitM_none`. -/

/-- **The wrapper equation.** With `$pkginit` found, nullary and resultless, `runPkgInitM` IS
`runInitConfig` on the init configuration, with the error re-labelled by `markInitPhase`
(`stuck`/`unsupported`/`internal` get the `package init:` prefix; `fuelOut` and the terminals pass
unmarked). -/
theorem runPkgInitM_some {ctx : ProgramCtx} {fuel : Nat} {s : Store} {ch : Choices} {initF : Func}
    (hf : findFunctionIn? ctx.functions pkgInitFuncId = some initF)
    (ha : initF.args.size = 0) (hr : initF.results.size = 0) :
    runPkgInitM ctx fuel s ch
      = (runInitConfig ctx fuel s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch).mapError
          markInitPhase := by
  simp only [runPkgInitM, hf, ha, hr, bne_self_eq_false, Bool.or_self, Bool.false_eq_true,
    ↓reduceIte]
  cases runInitConfig ctx fuel s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch <;> rfl

/-- The wrapper's SUCCESS link: `runPkgInitM` succeeds with `(s₁, ch₁)` iff `runInitConfig` on the
init configuration does (`markInitPhase` touches errors only). -/
theorem runPkgInitM_ok_iff {ctx : ProgramCtx} {fuel : Nat} {s s₁ : Store} {ch ch₁ : Choices} {initF : Func}
    (hf : findFunctionIn? ctx.functions pkgInitFuncId = some initF)
    (ha : initF.args.size = 0) (hr : initF.results.size = 0) :
    runPkgInitM ctx fuel s ch = .ok (s₁, ch₁) ↔
      runInitConfig ctx fuel s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch
        = .ok (s₁, ch₁) := by
  rw [runPkgInitM_some hf ha hr]
  cases runInitConfig ctx fuel s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch <;>
    simp [Except.mapError]

/-- A successful `runPkgInitM` with `$pkginit` present is a prefix of the initialiser's body to
`.next .stop` within the fuel (the arity premises follow from the success: a malformed
`$pkginit` refuses by name). -/
theorem runPkgInitM_ok_prefix {ctx : ProgramCtx} {fuel : Nat} {s s₁ : Store} {ch ch₁ : Choices}
    {initF : Func} (hf : findFunctionIn? ctx.functions pkgInitFuncId = some initF)
    (h : runPkgInitM ctx fuel s ch = .ok (s₁, ch₁)) :
    ∃ n, n ≤ fuel ∧ ∃ ls,
      Prefix ctx n s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch ls s₁ (.next .stop) ch₁ := by
  by_cases ha : initF.args.size = 0 <;> by_cases hr : initF.results.size = 0
  · exact runInitConfig_ok_prefix ((runPkgInitM_ok_iff hf ha hr).mp h)
  all_goals simp [runPkgInitM, hf, ha, hr, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h

/-- **The initialisation phase as a `Prefix`** (the `Seeded` reading): a successful `runPkgInitM`
either found no `$pkginit` and returned the store and tape untouched, or found it and ran its body
as a prefix to `.next .stop` within the fuel. -/
theorem runPkgInitM_ok_cases {ctx : ProgramCtx} {fuel : Nat} {s s₁ : Store} {ch ch₁ : Choices}
    (h : runPkgInitM ctx fuel s ch = .ok (s₁, ch₁)) :
    (findFunctionIn? ctx.functions pkgInitFuncId = none ∧ s₁ = s ∧ ch₁ = ch) ∨
    ∃ initF, findFunctionIn? ctx.functions pkgInitFuncId = some initF ∧
      ∃ n, n ≤ fuel ∧ ∃ ls,
        Prefix ctx n s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch ls s₁ (.next .stop) ch₁ := by
  cases hf : findFunctionIn? ctx.functions pkgInitFuncId with
  | none =>
    left
    simp [runPkgInitM, hf] at h
    exact ⟨rfl, h.1.symm, h.2.symm⟩
  | some initF =>
    right
    exact ⟨initF, rfl, runPkgInitM_ok_prefix hf h⟩


/-! ## `Prefix` determinism (fix round F2, 2026-10-21)

A general law of `Prefix` (`stepFn` is a function), homed here to keep `Prefix.lean` verbatim:
two prefixes of the same length from the same start are the same run; a shorter one is an initial
segment of a longer one. -/

/-- Two prefixes of the same length from the same start agree in labels and endpoint. -/
theorem prefix_det {ctx : ProgramCtx} {n : Nat} {s σ₁ σ₂ : Store} {c c₁ c₂ : Config}
    {ch ch₁ ch₂ : Choices} {ls ls' : List StepLabel}
    (h₁ : Prefix ctx n s c ch ls σ₁ c₁ ch₁) (h₂ : Prefix ctx n s c ch ls' σ₂ c₂ ch₂) :
    ls = ls' ∧ σ₁ = σ₂ ∧ c₁ = c₂ ∧ ch₁ = ch₂ := by
  induction h₁ generalizing ls' σ₂ c₂ ch₂ with
  | done => cases h₂; exact ⟨rfl, rfl, rfl, rfl⟩
  | step hs _ ih =>
    cases h₂ with
    | step hs' hp' =>
      rw [hs] at hs'
      cases hs'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ih hp'
      exact ⟨rfl, rfl, rfl, rfl⟩

/-- A shorter prefix from the same start is an initial segment of a longer one: the longer one's
labels extend the shorter one's, and the remainder runs from the shorter one's endpoint. -/
theorem prefix_det_le {ctx : ProgramCtx} {m n : Nat} {s σ₁ σ₂ : Store} {c c₁ c₂ : Config}
    {ch ch₁ ch₂ : Choices} {ls ls' : List StepLabel}
    (h₁ : Prefix ctx m s c ch ls σ₁ c₁ ch₁) (h₂ : Prefix ctx n s c ch ls' σ₂ c₂ ch₂) (hmn : m ≤ n) :
    ∃ ls₂, ls' = ls ++ ls₂ ∧ Prefix ctx (n - m) σ₁ c₁ ch₁ ls₂ σ₂ c₂ ch₂ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  obtain ⟨ls₁, ls₂, s₁, c₁', ch₁', rfl, hp₁, hp₂⟩ := prefix_split ctx m k s σ₂ c c₂ ch ch₂ ls' h₂
  obtain ⟨rfl, rfl, rfl, rfl⟩ := prefix_det h₁ hp₁
  exact ⟨ls₂, rfl, by rwa [Nat.add_sub_cancel_left]⟩

/-! ## From ONE witnessed run to the init loop's success (fix round F2; R8's converse)

The customer's R8 runs `$pkginit` symbolically once (a `Prefix` with concrete labels) and needs
`runPkgInitM = .ok` back, to construct the seeded store. The no-print premise of `runInitConfig_ok_iff`
quantifies over every prefix within the fuel; here it is discharged from the one run's labels: a
print position's step carries its bytes on the label (`stepFn_out_of_printOut?`, from main's
`printOut?_toList`, `retV_stmtOpK_apply` and the validate-only print apply), so a run whose labels are
all silent on `out` passes no print position, and every other prefix is an initial segment of it. -/

/-- At a `print` apply whose rendering succeeds, the apply commits nothing: the state and the
tape untouched, no pick, no trace (the print arm validates only; the bytes are the label's). -/
theorem applyStmtOp_print {ctx : ProgramCtx} {s : Store} {ch : Choices} {newline : Bool} {nt : Nat}
    {vs : List GoValue} {bytes : GoString} (h : renderPrint newline vs = .ok bytes) :
    applyStmtOp ctx s ch (.print newline) nt vs = .ok (s, ch, [], []) := by
  simp [applyStmtOp, applyStmtOp.plan, applyStmtOpCore.plan, h, Commit.withStream, Bind.bind,
    Except.bind]

/-- A successful step at a print position carries the rendered bytes on its label's `out`. -/
theorem stepFn_out_of_printOut? {ctx : ProgramCtx} {s s' : Store} {c c' : Config} {ch ch' : Choices}
    {l : StepLabel} {bytes : GoString} (hp : printOut? c = some bytes)
    (hs : stepFn ctx s c ch = .ok (c', s', ch', l)) : l.out = [bytes] := by
  unfold printOut? at hp
  split at hp
  · rename_i v newline nt done env k
    cases hr : renderPrint newline (v :: done).reverse with
    | error e => rw [hr] at hp; cases hp
    | ok b =>
      rw [hr] at hp
      cases hp
      rw [GoLean.GoCore.Equations.retV_stmtOpK_apply env k ch (applyStmtOp_print hr)] at hs
      cases hs
      simp only [stmtOpOut]
      rw [hr]
  · cases hp

/-- The guard is silent exactly off the print positions. -/
theorem initPrintRefusal?_eq_none_iff {c : Config} : initPrintRefusal? c = none ↔ printOut? c = none := by
  unfold initPrintRefusal?
  cases printOut? c <;> simp

/-- The silent-run lemma with a general endpoint (the induction's shape); the statement below
instantiates it at `.next .stop`. -/
private theorem noPrint_of_prefix_silent_aux {ctx : ProgramCtx} {n : Nat} {s sf : Store} {c cf : Config}
    {ch chf : Choices} {ls : List StepLabel} (hp : Prefix ctx n s c ch ls sf cf chf) :
    cf = .next .stop → (∀ l ∈ ls, l.out = []) →
    ∀ (m : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls' : List StepLabel),
      Prefix ctx m s c ch ls' σ' c' ch' → initPrintRefusal? c' = none := by
  induction hp with
  | done =>
    intro hcf _ m σ' c' ch' ls' hp'
    subst hcf
    cases hp' with
    | done => exact initPrintRefusal?_zeroCost (.inl rfl)
    | step hs _ => exact absurd (.inl rfl) (stepFn_zeroCost_not_ok hs)
  | @step _ _ _ _ c₀ _ _ _ _ _ l ls hs _ ih =>
    intro hcf hsil m σ' c' ch' ls' hp'
    cases hp' with
    | done =>
      rw [initPrintRefusal?_eq_none_iff]
      cases hpo : printOut? c₀ with
      | none => rfl
      | some bytes =>
        have := stepFn_out_of_printOut? hpo hs
        rw [hsil l (List.mem_cons_self ..)] at this
        cases this
    | step hs' hrest' =>
      rw [hs] at hs'
      cases hs'
      exact ih hcf (fun l' hl' => hsil l' (List.mem_cons_of_mem _ hl')) _ _ _ _ _ hrest'

/-- **The no-print premise from one silent run**: along a prefix to `.next .stop` whose labels print
nothing, no prefix from the same start (of ANY length — none passes `.next .stop`) ends at a print
position. -/
theorem noPrint_of_prefix_silent {ctx : ProgramCtx} {n : Nat} {s sf : Store} {c : Config}
    {ch chf : Choices} {ls : List StepLabel} (hp : Prefix ctx n s c ch ls sf (.next .stop) chf)
    (hsil : ∀ l ∈ ls, l.out = []) :
    ∀ (m : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls' : List StepLabel),
      Prefix ctx m s c ch ls' σ' c' ch' → initPrintRefusal? c' = none :=
  noPrint_of_prefix_silent_aux hp rfl hsil

/-- **R8's converse, one application**: a witnessed prefix to `.next .stop` within the fuel whose
labels print nothing IS a successful init run. -/
theorem runInitConfig_ok_of_prefix_silent {ctx : ProgramCtx} {fuel n : Nat} {s sf : Store}
    {c : Config} {ch chf : Choices} {ls : List StepLabel}
    (hp : Prefix ctx n s c ch ls sf (.next .stop) chf) (hn : n ≤ fuel) (hsil : ∀ l ∈ ls, l.out = []) :
    runInitConfig ctx fuel s c ch = .ok (sf, chf) :=
  (runInitConfig_ok_iff ctx fuel s sf c ch chf
    (fun m σ' c' ch' ls' hp' _ => noPrint_of_prefix_silent hp hsil m σ' c' ch' ls' hp')).mpr
    ⟨n, hn, ls, hp⟩

/-- The same through the wrapper: a witnessed silent run of `$pkginit`'s body is a successful
`runPkgInitM` — the seeded store `s₁` and the tape `ch₁` it leaves. -/
theorem runPkgInitM_ok_of_prefix_silent {ctx : ProgramCtx} {fuel n : Nat} {s s₁ : Store}
    {ch ch₁ : Choices} {initF : Func} {ls : List StepLabel}
    (hf : findFunctionIn? ctx.functions pkgInitFuncId = some initF)
    (ha : initF.args.size = 0) (hr : initF.results.size = 0)
    (hp : Prefix ctx n s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch ls s₁ (.next .stop) ch₁)
    (hn : n ≤ fuel) (hsil : ∀ l ∈ ls, l.out = []) :
    runPkgInitM ctx fuel s ch = .ok (s₁, ch₁) :=
  (runPkgInitM_ok_iff hf ha hr).mpr (runInitConfig_ok_of_prefix_silent hp hn hsil)

end GoLean.GoCore.ExecutionStatement
