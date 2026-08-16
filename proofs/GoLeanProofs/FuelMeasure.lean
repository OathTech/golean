import GoLean.GoCore.MachineSound
import GoLeanProofs.Surface

/-!
# The fuel-measure termination kit (verified-examples slice 1.5, 2026-08-12)

Symbolic (∀-input) discharge of `Terminates` — the completion-side twin
of the break-aware loop rule `wp_while_inv_break` (checkpoint ruling
2026-08-12: enumeration is banned as a proof method; every quantified
claim is symbolic in its inputs).

**Why no Iris in this half** (recorded per the same ruling): standard
Iris WP is partial-by-construction — step-indexing/Löb induction cannot
prove termination; iris-lean at our pin has no total WP (`twp`); the
Iris-world alternatives (a twp port, time credits, Transfinite Iris)
are real machinery we do not need, because our claims are about a
fuel-indexed EXECUTABLE function. So the split is exactly the
TCB-grounding principle: Iris keeps the VALUE half (the WP walk,
`GoSpec`); boring induction over the executable does COMPLETION. A twp
port stays the recorded option if termination-inside-the-logic is ever
wanted.

The kit:
* `CompletesIn fuel σ c` — completion (any terminal) within `fuel` from
  a configuration, at EVERY choice stream: `Terminates`' core, exposed
  at configuration granularity so segments compose by fuel arithmetic.
* `execStmtLoop_of_stepFnIter` — a successful `k`-step `stepFnIter`
  prefix folds into the loop: `execStmtLoop (k + f) = execStmtLoop f`
  at the reached configuration (the `execStmtLoop_step` chain, once).
* `completesIn_comp` — segment composition with a per-stream bounded
  step count (`k ≤ k₀`).
* `completesIn_measure_loop` — **the measure rule**: a state family
  `S : Nat → ExecState → Prop` (loop-head invariant indexed by the
  remaining measure), a per-iteration fuel bound (each iteration
  returns to the head in `≤ c_iter` interpreter steps with the measure
  STRICTLY decreased — `μ' ≤ μ` from `μ + 1`, so non-unit decreases
  such as gcd's `b`-value or binary search's interval width instantiate
  directly), and an exit bound at measure `0`, yield completion at
  `c_iter * μ + c_exit` — by strong induction on the measure. No Iris,
  no relation, no enumeration.

Same-commit discharge witness (non-vacuity): the fib exemplar's
symbolic termination (`Examples/Fib.lean`, `fibTerminates` — the
94-seed kernel enumeration this kit REPLACES is deleted there).
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Surface

/-- **Completion within a fuel bound from a configuration, at every
choice stream** — `Terminates`' core at configuration granularity.
"Completes" is terminal-agnostic, exactly as in `Terminates`. -/
def CompletesIn (fuel : Nat) (σ : ExecState) (c : Config) : Prop :=
  ∀ ch : Choices, ∃ (out : ExecOutcome) (ch' : Choices),
    execStmtLoop fuel σ c ch = .ok (out, ch')

/-- Fuel monotonicity, lifted. -/
theorem CompletesIn.mono {k fuel : Nat} {σ : ExecState} {c : Config}
    (hle : k ≤ fuel) (h : CompletesIn k σ c) : CompletesIn fuel σ c := by
  intro ch
  obtain ⟨out, ch', hrun⟩ := h ch
  exact ⟨out, ch', execStmtLoop_mono k fuel _ _ _ _ hle hrun⟩

/-- The definitional bridge: completion from the seeded driver
configuration is `Terminates`. -/
theorem terminates_of_completesIn {N : Nat} {env : LocalEnv}
    {σ : ExecState} {prog : Stmt}
    (h : CompletesIn N σ (.exec prog env .stop)) :
    Terminates env σ prog := by
  refine ⟨N, fun fuel hfuel ch => ?_⟩
  obtain ⟨out, ch', hrun⟩ := h ch
  exact ⟨out, ch', execStmtLoop_mono N fuel _ _ _ _ hfuel hrun⟩

/-- A successful `stepFnIter` prefix folds into the loop: `k` chained
`execStmtLoop_step`s, once and for all. -/
theorem execStmtLoop_of_stepFnIter :
    ∀ {k : Nat} {σ : ExecState} {c : Config} {ch : Choices}
      {c' : Config} {σ' : ExecState} {ch' : Choices},
      stepFnIter k σ c ch = .ok (c', σ', ch') →
      ∀ f : Nat, execStmtLoop (k + f) σ c ch = execStmtLoop f σ' c' ch' := by
  intro k
  induction k with
  | zero =>
    intro σ c ch c' σ' ch' h f
    simp only [stepFnIter, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  | succ n ih =>
    intro σ c ch c' σ' ch' h f
    simp only [stepFnIter, bind_eq_ok] at h
    obtain ⟨⟨c₁, σ₁, ch₁⟩, hstep, hrest⟩ := h
    have : n + 1 + f = (n + f) + 1 := by omega
    rw [this, execStmtLoop_step hstep]
    exact ih hrest f

/-- **Segment composition**: if from `(σ, c)` every choice stream
reaches, within a bounded number of interpreter steps, a configuration
that completes in `f`, then `(σ, c)` completes in `k₀ + f`. -/
theorem completesIn_comp {k₀ f : Nat} {σ : ExecState} {c : Config}
    (h : ∀ ch : Choices, ∃ (k : Nat) (c' : Config) (σ' : ExecState)
      (ch' : Choices), k ≤ k₀ ∧ stepFnIter k σ c ch = .ok (c', σ', ch')
        ∧ CompletesIn f σ' c') :
    CompletesIn (k₀ + f) σ c := by
  intro ch
  obtain ⟨k, c', σ', ch', hk, hstep, hrest⟩ := h ch
  obtain ⟨out, ch'', hrun⟩ := hrest ch'
  refine ⟨out, ch'', ?_⟩
  have hfold := execStmtLoop_of_stepFnIter hstep f
  exact execStmtLoop_mono (k + f) (k₀ + f) _ _ _ _ (by omega)
    (hfold.trans hrun)

/-- **The fuel-measure loop rule** — the completion-side twin of
`wp_while_inv_break` (designed as a pair; the value side keeps the
Iris invariant, this side does induction over the executable):

given a loop-head configuration `chead` and a state family
`S : Nat → ExecState → Prop` — the loop invariant indexed by the
REMAINING measure — such that

* every `S (μ+1)` state runs one iteration back to the head within
  `c_iter` interpreter steps, at every choice stream, reaching an
  `S μ'` state with `μ' ≤ μ` (STRICT decrease from `μ+1`; non-unit
  decreases — gcd's remainder, binary search's halving — instantiate
  directly), and
* every `S 0` state completes from the head within `c_exit` fuel (the
  break/exit path),

every `S μ` state completes from the head within `c_iter * μ + c_exit`
fuel. Strong induction on `μ`; no Iris, no enumeration. -/
theorem completesIn_measure_loop {c_iter c_exit : Nat} {chead : Config}
    {S : Nat → ExecState → Prop}
    (hiter : ∀ μ σ, S (μ + 1) σ → ∀ ch : Choices,
      ∃ (k : Nat) (σ' : ExecState) (ch' : Choices) (μ' : Nat),
        k ≤ c_iter ∧ μ' ≤ μ ∧
        stepFnIter k σ chead ch = .ok (chead, σ', ch') ∧ S μ' σ')
    (hexit : ∀ σ, S 0 σ → CompletesIn c_exit σ chead) :
    ∀ μ σ, S μ σ → CompletesIn (c_iter * μ + c_exit) σ chead := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro σ hS
    match μ, hS with
    | 0, hS => simpa using hexit σ hS
    | μ₁ + 1, hS =>
      intro ch
      obtain ⟨k, σ', ch', μ', hk, hμ, hstep, hS'⟩ := hiter μ₁ σ hS ch
      obtain ⟨out, ch'', hrun⟩ := ih μ' (by omega) σ' hS' ch'
      refine ⟨out, ch'', ?_⟩
      have hfold := execStmtLoop_of_stepFnIter hstep (c_iter * μ' + c_exit)
      have hmul : c_iter * μ' ≤ c_iter * μ₁ := Nat.mul_le_mul_left _ hμ
      have hdist : c_iter * (μ₁ + 1) = c_iter * μ₁ + c_iter := Nat.mul_succ _ _
      exact execStmtLoop_mono (k + (c_iter * μ' + c_exit))
        (c_iter * (μ₁ + 1) + c_exit) _ _ _ _
        (by omega) (hfold.trans hrun)

/-- Completion at the driver's own terminal: `.next .stop` is the
`.normal` completion at ANY fuel (the loop's terminal arm consumes no
fuel). -/
theorem completesIn_next_stop {f : Nat} {σ : ExecState} :
    CompletesIn f σ (.next .stop) := by
  intro ch
  refine ⟨.normal σ, ch, ?_⟩
  rw [execStmtLoop_unfold]

/-- The driver's terminal: `.next .stop` completes `.normal` at ANY
fuel (the loop's terminal arm consumes none). -/
theorem execStmtLoop_next_stop {f : Nat} {σ : ExecState} {ch : Choices} :
    execStmtLoop f σ (.next .stop) ch = .ok (.normal σ, ch) := by
  rw [execStmtLoop_unfold]

/-- **The D1 run-conditioned readout, derived from a total headline**
(verified-examples slice 2c): the ∃N completes-AND-verdict form already
determines every normal completion's final state — `execStmt` is a
function of `(fuel, ch)`, and a success is fuel-monotone with the SAME
result, so any normal completion at any fuel meets the headline's run
at `max N fuel` and inherits its σf-predicate. One lemma, so every
direct-route example ships its run-conditioned twin (`<x>_readout`)
without a second walk. -/
theorem normal_readout_of_total {env : LocalEnv} {σ : ExecState}
    {prog : Stmt} {P : ExecState → Prop}
    (h : ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel env σ ch prog = .ok (.normal σf, ch') ∧ P σf) :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execStmt fuel env σ ch prog = .ok (.normal σf, ch') → P σf := by
  intro fuel ch σf ch' hrun
  obtain ⟨N, hN⟩ := h
  obtain ⟨σf', ch'', hrun', hP⟩ := hN (max N fuel) (Nat.le_max_left _ _) ch
  have hmono := execStmt_mono (Nat.le_max_right N fuel) hrun
  rw [hmono] at hrun'
  injection hrun' with hpair
  injection hpair with hout hch
  injection hout with hσ
  exact hσ ▸ hP

/-! ### The harness-entry glue (harness ruling 2026-08-13, form note
§11): the same fold/terminal lemmas as `execStmtLoop`'s, for
`runConfig` — the loop inside the machine's native function entry
`runFunctionWithContextM`, which every harness headline states. Built
once, shared by every example's restatement. -/

/-- `runConfig`, unfolded to its match (the `execStmtLoop_unfold`
mirror). -/
theorem runConfig_unfold (fuel : Nat) (σ : ExecState) (c : Config)
    (ch : Choices) :
    runConfig fuel σ c ch
      = (match c with
         | .next .stop => .ok (σ, ch)
         | .panicked msg => throw (.panic msg)
         | .blockedSend _ _ _ => throw .deadlock
         | .blockedRecv _ _ _ _ _ => throw .deadlock
         | .blockedSelect _ _ _ => throw .deadlock
         | .blockedSync _ _ _ _ => throw .deadlock
         | c =>
             match fuel with
             | 0 => throw .fuelOut
             | fuel + 1 => do
                 let (c', σ', choices') ← stepFn σ c ch
                 runConfig fuel σ' c' choices') := by
  rw [runConfig.eq_def]
  rfl

/-- One successful step folds into `runConfig` (the
`execStmtLoop_step` mirror): `stepFn` throws on every terminal
configuration, so a successful step excludes the terminal arms. -/
theorem runConfig_step {fuel : Nat} {σ : ExecState} {c : Config}
    {ch : Choices} {c₁ : Config} {σ₁ : ExecState} {ch₁ : Choices}
    (h : stepFn σ c ch = .ok (c₁, σ₁, ch₁)) :
    runConfig (fuel + 1) σ c ch = runConfig fuel σ₁ c₁ ch₁ := by
  rw [runConfig_unfold (fuel + 1) σ c ch]
  split
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp only [Bind.bind]
    rw [h]
    rfl

/-- A successful `stepFnIter` prefix folds into `runConfig`
(`execStmtLoop_of_stepFnIter`'s mirror). -/
theorem runConfig_of_stepFnIter :
    ∀ {k : Nat} {σ : ExecState} {c : Config} {ch : Choices}
      {c' : Config} {σ' : ExecState} {ch' : Choices},
      stepFnIter k σ c ch = .ok (c', σ', ch') →
      ∀ f : Nat, runConfig (k + f) σ c ch = runConfig f σ' c' ch' := by
  intro k
  induction k with
  | zero =>
    intro σ c ch c' σ' ch' h f
    simp only [stepFnIter, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp
  | succ n ih =>
    intro σ c ch c' σ' ch' h f
    simp only [stepFnIter, bind_eq_ok] at h
    obtain ⟨⟨c₁, σ₁, ch₁⟩, hstep, hrest⟩ := h
    have : n + 1 + f = (n + f) + 1 := by omega
    rw [this, runConfig_step hstep]
    exact ih hrest f

/-- The driver terminal: `.next .stop` returns the state at ANY fuel
(the terminal arm precedes the fuel check). -/
theorem runConfig_next_stop {f : Nat} {σ : ExecState} {ch : Choices} :
    runConfig f σ (.next .stop) ch = .ok (σ, ch) := by
  rw [runConfig_unfold]

/-- A completed `runConfig` run is stable under more fuel
(`execStmtLoop_mono`'s mirror): the loop stops at the terminal before
consulting the surplus. -/
theorem runConfig_mono :
    ∀ (fuel fuel' : Nat) (σ : ExecState) (c : Config) (ch : Choices)
      (r : ExecState × Choices),
    fuel ≤ fuel' → runConfig fuel σ c ch = .ok r →
    runConfig fuel' σ c ch = .ok r := by
  intro fuel
  induction fuel with
  | zero =>
    intro fuel' σ c ch r _ h
    unfold runConfig at h ⊢
    split at h <;> simp_all
  | succ n ih =>
    intro fuel' σ c ch r hle h
    obtain ⟨m, rfl⟩ : ∃ m, fuel' = m + 1 := ⟨fuel' - 1, by omega⟩
    unfold runConfig at h ⊢
    split at h <;> try simp_all
    rw [bind_eq_ok] at h
    obtain ⟨⟨c', σ', ch'⟩, hstep, hrest⟩ := h
    rw [bind_eq_ok]
    exact ⟨(c', σ', ch'), hstep, ih _ _ _ _ r.1 r.2 (by omega) hrest⟩

/-- Fuel monotonicity of the machine's native function entry: the
prelude (size check, `bindParams`, `allocDecls`, `pinResultLocs`) and
the readback are fuel-independent; `runConfig_mono` carries the run
between them. -/
theorem runFunctionWithContextM_mono {N fuel : Nat} {types : TypeEnv}
    {functions : Array Func} {func : Func} {args : Array GoValue}
    {methods : Array MethodInfo} {ch : Choices} {r : Result}
    (hle : N ≤ fuel)
    (h : runFunctionWithContextM N types functions func args methods ch
      = .ok r) :
    runFunctionWithContextM fuel types functions func args methods ch
      = .ok r := by
  unfold runFunctionWithContextM at h ⊢
  by_cases hc : (func.args.size != args.size) = true
  · rw [if_pos hc] at h
    exact absurd h
      (by simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind])
  · rw [if_neg hc] at h ⊢
    simp only [bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h ⊢
    obtain ⟨u, hu, ⟨env, s₁⟩, hbp, ⟨frameEnv, s₂⟩, had, locs, hpin,
      ⟨sF, chF⟩, hrc, vs, hload, hres⟩ := h
    exact ⟨u, hu, (env, s₁), hbp, (frameEnv, s₂), had, locs, hpin,
      (sF, chF), runConfig_mono N fuel _ _ _ _ hle hrc, vs, hload, hres⟩

/-- **The D1 run-conditioned readout for harness headlines**: the
`.ok`-equation headline form (∃N-∀fuel≥N-∀ch, entry = `.ok r₀`)
already determines EVERY successful completion — the entry is a
function of `(fuel, ch)` and a success is fuel-monotone with the same
result, so a completion at any fuel meets the headline's run past its
bound. One lemma; every harness example gets its run-conditioned twin
(`<x>_readout`) without a second walk. -/
theorem harness_readout_of_total {types : TypeEnv}
    {functions : Array Func} {func : Func} {args : Array GoValue}
    {methods : Array MethodInfo} {r₀ : Result}
    (h : ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel types functions func args methods ch
        = .ok r₀) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runFunctionWithContextM fuel types functions func args methods ch
        = .ok r → r = r₀ := by
  intro fuel ch r hrun
  obtain ⟨N, hN⟩ := h
  have h1 := runFunctionWithContextM_mono (Nat.le_max_right N fuel) hrun
  have h2 := hN (max N fuel) (Nat.le_max_left _ _) ch
  rw [h1] at h2
  exact Except.ok.inj h2

/-- Chain two successful `stepFnIter` prefixes. -/
theorem stepFnIter_chain :
    ∀ {a : Nat} {b : Nat} {σ : ExecState} {c : Config} {ch : Choices}
      {c₁ : Config} {σ₁ : ExecState} {ch₁ : Choices}
      {c₂ : Config} {σ₂ : ExecState} {ch₂ : Choices},
      stepFnIter a σ c ch = .ok (c₁, σ₁, ch₁) →
      stepFnIter b σ₁ c₁ ch₁ = .ok (c₂, σ₂, ch₂) →
      stepFnIter (a + b) σ c ch = .ok (c₂, σ₂, ch₂) := by
  intro a
  induction a with
  | zero =>
    intro b σ c ch c₁ σ₁ ch₁ c₂ σ₂ ch₂ h₁ h₂
    simp only [stepFnIter, Except.ok.injEq, Prod.mk.injEq] at h₁
    obtain ⟨rfl, rfl, rfl⟩ := h₁
    simpa using h₂
  | succ n ih =>
    intro b σ c ch c₁ σ₁ ch₁ c₂ σ₂ ch₂ h₁ h₂
    simp only [stepFnIter, bind_eq_ok] at h₁
    obtain ⟨⟨cm, σm, chm⟩, hstep, hrest⟩ := h₁
    have : n + 1 + b = (n + b) + 1 := by omega
    rw [this]
    simp only [stepFnIter, bind_eq_ok]
    exact ⟨(cm, σm, chm), hstep, ih hrest h₂⟩

/-! ### The setup-loop iteration schema (Gallery Campaign G0 item 3a,
2026-08-15 — the P5 promotion, reopened from the scale-out ledger)

Every shipped array example proves the same strong induction for its
setup loop (and isort a second time for its rebuild loop): a loop
whose every iteration runs the SAME number of interpreter steps from
the `i`-indexed configuration/state to the `i+1`-indexed one, iterated
to `n`. The 9 shipped instances (count corrected 2026-08-16 by the
post-autonomy audit; g0.md records all nine retrofitted) each carried
the identical
`Nat.strongRecOn` + chain + `c + c·(n−(i+1)) = c·(n−i)` + exit-case
boilerplate; this is that induction stated ONCE. The per-iteration
composite stays example-local (it chains that example's raw segments)
— the schema consumes it as the `hstep` hypothesis, whose type pins
both states (the storm-diagnosis rule). Landed fixtures: the isort
setup loop and the wordcount harness setup loop, retrofitted in the
lifting commit; chartered consumers: every G1 array-setup candidate. -/

/-- **The uniform-iteration schema**: if every iteration `i < n` runs
exactly `c` interpreter steps from `(T i, C i)` to `(T (i+1), C (i+1))`
(threading the choice stream unchanged — these loops are choice-free),
then from any `i ≤ n` the loop reaches `(T n, C n)` in exactly
`c * (n - i)` steps. Induction on `n - i`; no per-example
`strongRecOn` needed. -/
theorem stepFnIter_iterate {c n : Nat} {T : Nat → ExecState}
    {C : Nat → Config}
    (hstep : ∀ i, i < n → ∀ ch : Choices,
      stepFnIter c (T i) (C i) ch = .ok (C (i + 1), T (i + 1), ch)) :
    ∀ i, i ≤ n → ∀ ch : Choices,
      stepFnIter (c * (n - i)) (T i) (C i) ch = .ok (C n, T n, ch) := by
  suffices key : ∀ μ i, μ = n - i → i ≤ n → ∀ ch : Choices,
      stepFnIter (c * (n - i)) (T i) (C i) ch = .ok (C n, T n, ch) by
    intro i hin ch
    exact key (n - i) i rfl hin ch
  intro μ
  induction μ with
  | zero =>
      intro i hμ hin ch
      have heq : i = n := by omega
      subst heq
      rw [Nat.sub_self, Nat.mul_zero]
      rfl
  | succ μ' ih =>
      intro i hμ hin ch
      have hlt : i < n := by omega
      have hc := stepFnIter_chain (hstep i hlt ch)
        (ih (i + 1) (by omega) (by omega) ch)
      have harith : c + c * (n - (i + 1)) = c * (n - i) := by
        rw [show n - i = (n - (i + 1)) + 1 from by omega, Nat.mul_succ]
        omega
      rw [harith] at hc
      exact hc

/-- **The TWO-EXIT loop schema** (WP arc s1 lift 5 — the exact shape
drafted at g1.md §Unit G1.3 "THE FINDING THIS UNIT CONTRIBUTES" and
§THE KIT-GAP LIST): the loop either ITERATES (`c` steps, index `+1`,
invariant `I` preserved), BAILS from inside the body to a terminal
satisfying `Q` (`≤ b` steps, available at any index where the
iteration does not fire), or EXITS at the test into a `Q`-terminal
(`≤ e` steps). Per the R1-closure lesson, the whole per-iteration
content enters through the ONE `hstep` hypothesis (a disjunction), the
invariant `I` threads the data the exit needs (palin's `PalinUpTo`),
and the terminal is a PREDICATE `Q` so the two exits may stop at
different (existentially quantified) states. Bound:
`c·(n−i) + max b e` — both landed shapes' `+70`-style constants are
exactly `max b e`. Replaces the surviving per-example `strongRecOn`
scaffolds. -/
theorem stepFnIter_iterate_bail {c e b n : Nat} {T : Nat → ExecState}
    {C : Nat → Config} {I : Nat → Prop}
    (Q : Config → ExecState → Prop)
    (hstep : ∀ i, i < n → I i →
      (∀ ch : Choices, ∃ (cf : Config) (Tf : ExecState), Q cf Tf ∧
        ∃ k ≤ b, stepFnIter k (T i) (C i) ch = .ok (cf, Tf, ch))
      ∨ (I (i + 1) ∧ ∀ ch : Choices,
        stepFnIter c (T i) (C i) ch = .ok (C (i + 1), T (i + 1), ch)))
    (hexit : I n → ∀ ch : Choices,
      ∃ (cf : Config) (Tf : ExecState), Q cf Tf ∧
        ∃ k ≤ e, stepFnIter k (T n) (C n) ch = .ok (cf, Tf, ch)) :
    ∀ i, i ≤ n → I i → ∀ ch : Choices,
      ∃ (cf : Config) (Tf : ExecState), Q cf Tf ∧
        ∃ k ≤ c * (n - i) + max b e,
          stepFnIter k (T i) (C i) ch = .ok (cf, Tf, ch) := by
  suffices key : ∀ μ i, μ = n - i → i ≤ n → I i → ∀ ch : Choices,
      ∃ (cf : Config) (Tf : ExecState), Q cf Tf ∧
        ∃ k ≤ c * (n - i) + max b e,
          stepFnIter k (T i) (C i) ch = .ok (cf, Tf, ch) by
    intro i hin hI ch
    exact key (n - i) i rfl hin hI ch
  intro μ
  induction μ with
  | zero =>
      intro i hμ hin hI ch
      have heq : i = n := by omega
      subst heq
      obtain ⟨cf, Tf, hQ, k, hk, hrun⟩ := hexit hI ch
      exact ⟨cf, Tf, hQ, k, by omega, hrun⟩
  | succ μ' ih =>
      intro i hμ hin hI ch
      have hlt : i < n := by omega
      rcases hstep i hlt hI with hbail | ⟨hI', hiter⟩
      · obtain ⟨cf, Tf, hQ, k, hk, hrun⟩ := hbail ch
        exact ⟨cf, Tf, hQ, k, by omega, hrun⟩
      · obtain ⟨cf, Tf, hQ, k, hk, hrun⟩ := ih (i + 1) (by omega)
          (by omega) hI' ch
        refine ⟨cf, Tf, hQ, c + k, ?_, stepFnIter_chain (hiter ch) hrun⟩
        have : c * (n - i) = c + c * (n - (i + 1)) := by
          rw [show n - i = (n - (i + 1)) + 1 from by omega, Nat.mul_succ]
          omega
        omega

/-- The iterate-then-exit composition: the schema above plus an exit
segment from `(T n, C n)` — the shape of the `∃k`-style setup loops
that absorb their exit into the loop lemma. -/
theorem stepFnIter_iterate_exit {c e n : Nat} {T : Nat → ExecState}
    {C : Nat → Config} {cf : Config} {Tf : ExecState}
    (hstep : ∀ i, i < n → ∀ ch : Choices,
      stepFnIter c (T i) (C i) ch = .ok (C (i + 1), T (i + 1), ch))
    (hexit : ∀ ch : Choices,
      stepFnIter e (T n) (C n) ch = .ok (cf, Tf, ch)) :
    ∀ i, i ≤ n → ∀ ch : Choices,
      stepFnIter (c * (n - i) + e) (T i) (C i) ch = .ok (cf, Tf, ch) :=
  fun i hin ch =>
    stepFnIter_chain (stepFnIter_iterate hstep i hin ch) (hexit ch)

end GoLean.Surface
