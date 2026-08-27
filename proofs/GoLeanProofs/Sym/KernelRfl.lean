import Lean

/-!
# `kernel_rfl` — kernel-delegated reflexivity (A4-U4 slice 0)

**The measured problem** (arc-4 log, A4-U4): on MACHINE-side fixture
facts — `stepFn`/`γS` equalities over concrete-shape states — the
ELABORATOR's `with_unfolding_all rfl` defeq check is the entire cost,
and the kernel's own check of the same conversion is ≈ free. Measured
on the U3 sort leaf (`uSort_leaf_00` shape): 352 s normal build vs
359 s with `debug.skipKernelTC true` — i.e. elaborator ≈ 100%,
kernel ≈ 0. (Anchor note, 2026-08-27, pre-merge audit,
semantics-dimension L5: `uSort_leaf_00` is ARCHIVED — it died with
the fixed-trajectory-era modules and is recoverable at
`archive/callspec-era`. The measurement stands as the recorded
justification for this tactic's existence; it is simply no longer
re-runnable from the tree, so a future re-measurement needs a fresh
machine-side fixture rather than this one.) The elaborator's whnf takes a slow path through the
interpreter's `do`-notation/`Std.Range.forIn`/`Except`-bind spines
that the kernel's evaluator does not.

**What this tactic does**: for a goal `lhs = rhs`, it assigns
`Eq.refl lhs` to the goal metavariable DIRECTLY (no elaborator defeq),
so the conversion `lhs ≡ rhs` is checked exactly once — by the KERNEL
at `addDecl`.

**Trust story — nothing changes**: the kernel still typechecks the
whole theorem, exactly as it checks every `rfl` proof; no new axiom,
no native-evaluation escape, no evaluator output is trusted. The only
thing
skipped is the elaborator's REDUNDANT defeq pre-check. Fail-closed:
if `lhs` and `rhs` are not definitionally equal, the build fails
loudly at `addDecl` with a kernel typecheck error (instead of the
tactic failing — the docstring price of the speedup, stated here so
nobody debugs it blind).

Use it on machine-side fixture facts (γ-image `stepFn` steps,
projection readouts, span witnesses). Mirror-side window `rfl`s
(`symEvalWindowTB` links) do NOT need it — the elaborator is
kernel-speed on the structural mirror evaluator.
-/

namespace GoLean.Sym.KernelRfl

open Lean Elab Tactic Meta

elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  -- NO whnf on the goal type: it can itself take the slow elaborator
  -- path this tactic exists to avoid; the goal must be a SYNTACTIC
  -- equality (which every fixture fact is).
  let some (α, lhs, _rhs) := t.eq?
    | throwError "kernel_rfl: goal is not a syntactic equality{indentExpr t}"
  if t.hasExprMVar then
    throwError "kernel_rfl: goal contains metavariables (fail closed){indentExpr t}"
  let u ← getLevel α
  goal.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)

end GoLean.Sym.KernelRfl
