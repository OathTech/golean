import GoLean.GoCore.Eval
import GoLean.GobraToIR

namespace GoLean.GobraEval

abbrev Result := GoLean.GoCore.Result

def lowerDocument (doc : GoLean.GobraJson.Document) : Except String GoLean.GoCore.Program :=
  GoLean.GobraToIR.lowerDocument doc

private def loweringError (message : String) : GoLean.GoError :=
  .unsupported s!"Gobra lowering failed: {message}"

def runFunctionMember (fuel : Nat) (member : GoLean.GobraJson.FunctionMember) (args : Array GoLean.GoValue) :
    Except GoLean.GoError Result := do
  let lowered := do
    let symbols ← GoLean.GobraToIR.buildSymbolMap #[.function member]
    GoLean.GobraToIR.lowerFunctionMember symbols member
  match lowered with
  | .ok func => GoLean.GoCore.runFunction fuel func args
  | .error err => throw (loweringError err)

def runFunction (fuel : Nat) (doc : GoLean.GobraJson.Document) (name : String) (args : Array GoLean.GoValue) :
    Except GoLean.GoError Result := do
  match lowerDocument doc with
  | .ok program => GoLean.GoCore.runNamedFunction fuel program name args
  | .error err => throw (loweringError err)

def runFunctionInts (fuel : Nat) (doc : GoLean.GobraJson.Document) (name : String) (args : Array Int) :
    Except GoLean.GoError Result := do
  match lowerDocument doc with
  | .ok program => GoLean.GoCore.runNamedFunctionInts fuel program name args
  | .error err => throw (loweringError err)

end GoLean.GobraEval
