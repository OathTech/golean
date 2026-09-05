import GateA1.Examples
open GoLean GoLean.GoCore GoLean.GoCore.Machine
#eval repr (recoverResult (.frame [] [] [] [] .stop false)).1
#eval repr (recoverResult (.frame [] [] [] [] (.panicResumeK [panicEntry "audit"] .stop) false)).1
#eval repr (execStmtLoop 2 { types := TypeEnv.reserved }
  (.panicking [panicEntry "audit"] (.probeK .stop)) [1])
#eval repr (runProgramPoolOutM 20 GoLean.GateA1.printPanicProgram "main.audit" #[] [])
#eval repr ((execStmtLoop 7 {} GoLean.GateA1.recoverCheck []).map (fun _ => ()))
