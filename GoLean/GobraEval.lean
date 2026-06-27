import GoLean.GobraToIR

namespace GoLean.GobraEval

abbrev Result := GoLean.GoCore.Result

def lowerDocument (doc : GoLean.GobraJson.Document) : Except String GoLean.GoCore.Program :=
  GoLean.GobraToIR.lowerDocument doc

def runFunctionMember (fuel : Nat) (member : GoLean.GobraJson.FunctionMember) (args : Array GoLean.GoValue) :
    Except String Result := do
  GoLean.GoCore.runFunction fuel (← GoLean.GobraToIR.lowerFunctionMember member) args

def runFunction (fuel : Nat) (doc : GoLean.GobraJson.Document) (name : String) (args : Array GoLean.GoValue) :
    Except String Result := do
  let program ← lowerDocument doc
  GoLean.GoCore.runNamedFunction fuel program name args

def runFunctionInts (fuel : Nat) (doc : GoLean.GobraJson.Document) (name : String) (args : Array Int) :
    Except String Result := do
  let program ← lowerDocument doc
  GoLean.GoCore.runNamedFunctionInts fuel program name args

end GoLean.GobraEval
