import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# The `stepFn_eqns` rewrite set — the attribute (window packet D, 2026-10-03)

[AGENT packet D worker]. `register_simp_attr` installs its attribute at module
initialization, so the attribute must be declared in a module OTHER than the one
that uses it: this file declares it, `GoLean/GoCore/Equations.lean` tags every
per-arm `stepFn` equation with it, and a client rewrites with
`simp only [stepFn_eqns]` — never `unfold stepFn`. This module has no other
content and imports only the simp-attribute command (`Lean.Meta.Tactic.Simp.
RegisterCommand`), the one `Lean` import the equation file needs.
-/

/-- The named rewrite set of the per-arm `stepFn` equations (`GoLean/GoCore/
Equations.lean`): `simp only [stepFn_eqns]` rewrites a `stepFn` call at a known
configuration shape to its successor (or its named refusal) under the arm's
explicit operation premises. -/
register_simp_attr stepFn_eqns

/-- Close a DEFINITIONAL equation with a proof term that is NOT `rfl`-shaped (`Eq.mpr (Eq.refl _) rfl`), so
`simp` treats the lemma as a PROPOSITIONAL rewrite rather than a `dsimp` (definitional) one: a client's
proof term then RECORDS every equation it used, which is what the client gate's proof-term check reads
(a `dsimp`-rewrite by an `rfl`-theorem leaves no trace and is indistinguishable from unfolding `stepFn`).
Pre-landing round of packet D (audit F2), 2026-10-03. -/
macro "defn_eq" : tactic => `(tactic| exact Eq.mpr (Eq.refl _) rfl)
