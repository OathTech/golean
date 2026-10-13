import GoLean.GoCore.Relational

/-! # Successful initialization and its mode boundary

Initialization permits the same successful steps but refuses printing before
consulting fuel. `Initializes` records the guard at each actual step; it does
not assume that other paths also avoid printing. Failure classification for
the entire initialization driver is not claimed by this successful carrier.
-/

namespace GoLean.GoCore.Relational

open Machine

inductive Initializes (ctx : ProgramCtx) : State → List StepLabel → Store → Prop where
  | done {s} : Initializes ctx ⟨.next .stop, s⟩ [] s
  | step {a b l ls s} : printOut? a.control = none → Transition ctx a l b →
      Initializes ctx b ls s → Initializes ctx a (l :: ls) s

def InitPrintRefusal (a : State) : Prop := ∃ bytes, printOut? a.control = some bytes

theorem Initializes.run {ctx : ProgramCtx} {a : State} {ls : List StepLabel} {s : Store}
    (h : Initializes ctx a ls s) : Run ctx a ls ⟨.next .stop, s⟩ := by
  induction h with
  | done => exact .refl
  | step _ hs _ ih => exact .cons hs ih

end GoLean.GoCore.Relational
