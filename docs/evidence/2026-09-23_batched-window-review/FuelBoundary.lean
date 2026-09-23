import GoLean.GoCore.StepFn

/-! Review witness for the distinction between zero-cost driver classification
and the cost-one abort transition. No changes to the semantic implementation. -/
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace WindowCharterReview

def ctx : ProgramCtx := ProgramCtx.ofTables #[] #[]
def abortConfig : Config := .panicking [panicEntry "review"] .stop

example : abortConfig.abort? = some (panicEntry "review", []) := rfl

theorem abort_at_zero (s : Store) (ch : Choices) :
    execStmtLoop ctx 0 s abortConfig ch = .error .fuelOut := rfl

theorem normal_at_zero (s : Store) (ch : Choices) :
    execStmtLoop ctx 0 s (.next .stop) ch = .ok (s, ch) := rfl

#eval reprStr (execStmtLoop ctx 0 {} abortConfig [])
#eval reprStr (execStmtLoop ctx 1 {} abortConfig [])

end WindowCharterReview
