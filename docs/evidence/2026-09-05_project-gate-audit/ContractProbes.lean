import GoLean.GoCore.MachineSound
open GoLean GoLean.GoCore GoLean.GoCore.Machine
-- The proposed unconditional fill law must preserve this recover result.
def bareFrame : Cont := .frame [] [] [] [] .stop false
def panicFrame : Cont := .frame [] [] [] [] (.panicResumeK [panicEntry "audit"] .stop) false
#eval repr (recoverResult bareFrame).1
#eval repr (recoverResult panicFrame).1
-- Existing StateWf is address boundedness, not value typing.
def illTyped : ExecState := { heap := #[.value .bool (.int 7)] }
#eval decide (StateWf illTyped)
