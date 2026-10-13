import GoLean.GoCore.Machine

/-!
# Labelled relational executions

These definitions contain neither a choice tape nor an evaluator call.
`Run` is the finite labelled closure of the semantic transition relation.
Correspondence to bounded execution lives separately in `RelationalSound`.

This foundational layer retains the core control representation; clients
should use the construct views and laws in `RelationalControl` to construct
and inspect ordinary program execution. A run records successful transitions
only: it does not assert refusal freedom or classify its endpoint.
-/

namespace GoLean.GoCore.Relational

open Machine

/-- A semantic point consists of control and mutable store. Program metadata
is a separate, fixed parameter of transitions and runs. -/
structure State where
  control : Config
  store : Store

/-- One successful semantic transition, including its complete label. -/
def Transition (ctx : ProgramCtx) (a : State) (l : StepLabel) (b : State) : Prop :=
  Step ctx a.control a.store b.control b.store l

/-- Finite labelled closure. Length is derived from the labels, so it cannot
disagree with the number of transitions. -/
inductive Run (ctx : ProgramCtx) : State → List StepLabel → State → Prop where
  | refl {a} : Run ctx a [] a
  | cons {a b c l ls} : Transition ctx a l b → Run ctx b ls c → Run ctx a (l :: ls) c

theorem Run.single {ctx : ProgramCtx} {a b : State} {l : StepLabel}
    (h : Transition ctx a l b) : Run ctx a [l] b := .cons h .refl

theorem Run.append {ctx : ProgramCtx} {a b c : State} {xs ys : List StepLabel}
    (h : Run ctx a xs b) (k : Run ctx b ys c) : Run ctx a (xs ++ ys) c := by
  induction h with
  | refl => exact k
  | cons hs _ ih => exact .cons hs (ih k)

theorem Run.split {ctx : ProgramCtx} {a c : State} {xs ys : List StepLabel}
    (h : Run ctx a (xs ++ ys) c) : ∃ b, Run ctx a xs b ∧ Run ctx b ys c := by
  induction xs generalizing a with
  | nil => exact ⟨a, .refl, h⟩
  | cons l ls ih =>
    cases h with
    | cons hs ht =>
      obtain ⟨b, hb, hc⟩ := ih ht
      exact ⟨b, .cons hs hb, hc⟩

theorem Run.erase {ctx : ProgramCtx} {a b : State} {ls : List StepLabel}
    (h : Run ctx a ls b) : Steps ctx a.control a.store b.control b.store := by
  induction h with
  | refl => exact .refl _ _
  | cons hs _ ih => exact (Steps.single hs).trans ih

/-- A property of every reachable semantic point. This alone does not say
that an endpoint is successful or that refusing alternatives are absent. -/
def Invariant (ctx : ProgramCtx) (initial : State) (P : State → Prop) : Prop :=
  ∀ ls final, Run ctx initial ls final → P final

theorem invariant_of_preserved {ctx : ProgramCtx} {a : State} {P : State → Prop}
    (initial : P a)
    (preserved : ∀ {a b l}, P a → Transition ctx a l b → P b) :
    Invariant ctx a P := by
  intro ls b h
  induction h with
  | refl => exact initial
  | cons hs _ ih => exact ih (preserved initial hs)

end GoLean.GoCore.Relational
