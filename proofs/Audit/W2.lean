import GoLeanProofs.CondFor

/-!
# Audit pins: W2 — the loop-rule family, the plug rule, the init spec

Exact-axiom pins for the W2 units (clean-proof plan §W2; the W2 log
`docs/w2-prover-log.md`). Grown section-by-section as the units land;
imported by `Audit.lean` in the same commit as each landing (the
in-build gate convention, as `Audit/W1.lean`).
-/

/-! ## CondFor — the plain-for (cond-only) head schema (harvested
verbatim from campaign-arc4d @ 7fa0e04d; provenance banner in the
module). The schema, its countdown discharge witness, and the
witness's kernel cross-check at a concrete state. -/

/-- info: 'GoLean.CondFor.condFor_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.CondFor.condFor_loop

/-- info: 'GoLean.CondFor.countdown_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.CondFor.countdown_span

/-- info: 'GoLean.CondFor.cd_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.CondFor.cd_concrete
