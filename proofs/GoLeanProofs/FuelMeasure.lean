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

end GoLean.Surface
