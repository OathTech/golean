import GoLean.GoCore.RelationalCall

/-!
# Uniform store-preserving paths

Controls and path length are independent of the store. Each actual label may
depend on it. Admission is required at traversed sources only, including the
source of a separately exposed effect; the final continuation is unrestricted.
These contracts say nothing about silence of a client observation.
-/
namespace GoLean.GoCore.Relational
open Machine

/-- The terminal and initialization guards admit this source. This alone
does not assert that a transition exists. -/
structure StepAdmission (c : Config) : Prop where
  nonterminal : c ≠ .next .stop
  initializes : initPrintRefusal? c = none

/-- A finite, pick-free path preserving each store satisfying `fact` at every
step. Unlike an equal-store endpoint run, this exposes intermediate preservation
and admission. The fact is needed only for this path, not a later effect/suffix. -/
inductive StorePath (ctx : ProgramCtx) (fact : Store → Prop) : Config → Config → Prop where
  | refl {c} : StorePath ctx fact c c
  | step {c d e}
      (transition : ∀ s, fact s → ∃ l, Transition ctx ⟨c, s⟩ l ⟨d, s⟩ ∧ l.picks = [])
      (admission : StepAdmission c)
      (rest : StorePath ctx fact d e) : StorePath ctx fact c e

theorem StorePath.trans {ctx : ProgramCtx} {fact : Store → Prop} {c d e : Config}
    (h : StorePath ctx fact c d) (g : StorePath ctx fact d e) : StorePath ctx fact c e := by
  induction h with
  | refl => exact g
  | step hs ha _ ih => exact .step hs ha (ih g)

theorem StorePath.run {ctx : ProgramCtx} {fact : Store → Prop} {c d : Config}
    (h : StorePath ctx fact c d) (s : Store) (hf : fact s) : PickFreeRun ctx ⟨c, s⟩ ⟨d, s⟩ := by
  induction h with
  | refl => exact .refl _ _
  | step hs _ _ ih =>
    obtain ⟨l, ht, hp⟩ := hs s hf
    exact (PickFreeRun.single ht hp).trans ih

theorem StorePath.weaken {ctx : ProgramCtx} {fact stronger : Store → Prop} {c d : Config}
    (h : StorePath ctx fact c d) (implies : ∀ s, stronger s → fact s) :
    StorePath ctx stronger c d := by
  induction h with
  | refl => exact .refl
  | step hs ha _ ih => exact .step (fun s hf => hs s (implies s hf)) ha ih

theorem StorePath.pure {ctx : ProgramCtx} {fact : Store → Prop} {c d : Config}
    (hs : ∀ s, Pure ctx ⟨c, s⟩ ⟨d, s⟩) (ha : StepAdmission c) : StorePath ctx fact c d :=
  .step (fun s _ => ⟨_, (hs s).1, rfl⟩) ha .refl

/-- One admitted effect, retaining its label, with no read fact assumed across
the effect. The operation relates pre/post stores and may include aliases. -/
structure StoreEffect (ctx : ProgramCtx) (operation : Store → Store → Prop)
    (before after : Config) : Prop where
  admission : StepAdmission before
  transition : ∀ s t, operation s t →
    ∃ l, Transition ctx ⟨before, s⟩ l ⟨after, t⟩ ∧ l.picks = []

/-- Operand paths uniformly over stores and saved continuations. -/
inductive OperandPaths (ctx : ProgramCtx) (fact : Store → Prop) (env : LocalEnv) :
    List Expr → List GoValue → Prop where
  | nil : OperandPaths ctx fact env [] []
  | cons {e v es vs} :
      (∀ k : Continuation, StorePath ctx fact (.evalE e env k.toMachine) (.retV v k.toMachine)) →
      OperandPaths ctx fact env es vs → OperandPaths ctx fact env (e :: es) (v :: vs)

theorem OperandPaths.values {ctx : ProgramCtx} {fact : Store → Prop} {env : LocalEnv}
    {es : List Expr} {vs : List GoValue} (h : OperandPaths ctx fact env es vs)
    (s : Store) (hf : fact s) : OperandValues ctx s env es vs := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (fun k => (he k).run s hf) ih

end GoLean.GoCore.Relational
