import GoLeanProofs.Sym.TableExt

/-!
# The symbolic-branch crossing transport (A4-U14: the U10
message-field-symbolism residual's general half)

**LINEAGE: symbolic-execution PATH-CONDITION SPLITTING at a branch
whose condition is symbolic — the founding move of the symbolic
execution classic (King 1976): a conditional that does not reduce to
a literal splits the path, each side proceeding under the branch
condition (or its negation) as a path-condition premise.** Realized
in the established transport pattern (`PickTransport`/
`SpillTransport`): the mirror QUITS `q1Branch` at
`retV v (ifK t e env k)` when `v`'s bool payload is symbolic
(`asBoolAt .q1Branch`, Mirror.lean); the crossing steps the MACHINE
at the γ-image, with the path condition entering as the
`hb : concV (symInterp ρ) v = .bool b` premise. An equation-level
side condition (the first consumer: the U10 finding's
`m.From ≠ r.id` at `send`'s self-addressed panic guard) discharges
`hb` per site — exactly how `hvote`-style range conditions discharge
norm-wraps.

State, allocator, and choice stream all RIDE THROUGH the crossing
(the machine's `ifK` arm touches none of them — StepFn.lean:335), so
the composition spine (`stepFnIter_window_pick_window` /
`stepFnIter_chain`) applies unchanged with this crossing in a pick
slot whose consumed width is zero — use `stepFnIter_chain` ∘
`stepFnIter_one` directly, as the per-site assembly prefers.

Scope (fail closed): the `ifK` continuation is the only arm — the
one censused consumer class. `whileK`/`andK`/`orK`/`boolK` symbolic
crossings are the same shape and are added ON THEIR FIRST CONSUMER;
until then the mirror keeps quitting there, visibly.
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

/-- THE BRANCH TRANSPORT: an `if` continuation at a symbolic
condition. The machine takes the arm the γ-image's bool selects;
state and stream are untouched. -/
theorem stepFn_branch_transport (ρ : Valuation) (σ : ExecState)
    {S : SymState} {v : SymValue} {t e : Stmt} {env : LocalEnv}
    {k : Cont symDom} {b : Bool} {ch : Choices}
    (hb : concV (symInterp ρ) v = .bool b) :
    stepFn (γS ρ σ S) (γC ρ (.retV v (.ifK t e env k))) ch
      = .ok (γC ρ (if b then .exec t env k else .exec e env k),
          γS ρ σ S, ch) := by
  show stepFn (γS ρ σ S)
      (.retV (concV (symInterp ρ) v)
        (.ifK t e env (concK (symInterp ρ) k))) ch = _
  rw [hb]
  cases b
  · with_unfolding_all rfl
  · with_unfolding_all rfl

/-! ## §3.3 discharge witness — the transport instantiated LIVE: the
branch condition `x₀ == 1` is genuinely symbolic (a different
valuation flips it), and at the valuation x₀ = 5 it concretizes
FALSE, so the machine takes the else arm. The premise-discharge shape
is the consumer's: an equation-level fact about the valuation
(`ρ.ints 0 ≠ 1`, here at a concrete instance) closes `hb`. -/

private def brWitρ : Valuation :=
  { ints := fun _ => 5
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem stepFn_branch_transport_witness (σ : ExecState)
    (t e : Stmt) (env : LocalEnv) (ch : Choices) (S : SymState) :
    stepFn (γS brWitρ σ S)
      (γC brWitρ (.retV (.bool (.eqI (.var 0) (.lit 1)))
        (.ifK t e env .stop))) ch
      = .ok (γC brWitρ (.exec e env .stop), γS brWitρ σ S, ch) :=
  stepFn_branch_transport brWitρ σ (b := false) (by with_unfolding_all rfl)

end GoLean.Sym
