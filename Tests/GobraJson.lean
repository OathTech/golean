import GoLean.GobraJson

namespace Tests.GobraJson

def validDocument : String :=
  "{\"schema\":{\"encoding\":\"structural-adt\",\"failClosed\":true,\"name\":\"gobra.internal\",\"version\":1},\"inputs\":[\"input.gobra\"],\"program\":{\"members\":[],\"source\":{\"origin\":{\"position\":{\"end\":null,\"file\":\"input.gobra\",\"start\":{\"column\":1,\"line\":1}},\"tag\":\"package input\"},\"tag\":\"Single\"},\"tag\":\"Program\",\"types\":[]}}"

def sourceJson : String :=
  "{\"origin\":{\"position\":{\"end\":null,\"file\":\"input.gobra\",\"start\":{\"column\":1,\"line\":1}},\"tag\":\"package input\"},\"tag\":\"Single\"}"

def functionProxyJson : String :=
  "{\"name\":\"f_F\",\"source\":" ++ sourceJson ++ ",\"tag\":\"FunctionProxy\"}"

def minimalFunctionJson : String :=
  "{\"args\":[],\"backendAnnotations\":[],\"body\":{\"tag\":\"None\"},\"name\":" ++ functionProxyJson ++
  ",\"posts\":[],\"pres\":[],\"results\":[],\"source\":" ++ sourceJson ++
  ",\"tag\":\"Function\",\"terminationMeasures\":[]}"

def documentWithMembers (members : String) : String :=
  "{\"schema\":{\"encoding\":\"structural-adt\",\"failClosed\":true,\"name\":\"gobra.internal\",\"version\":1},\"inputs\":[\"input.gobra\"],\"program\":{\"members\":" ++
  members ++ ",\"source\":" ++ sourceJson ++ ",\"tag\":\"Program\",\"types\":[]}}"

def validFunctionDocument : String :=
  documentWithMembers ("[" ++ minimalFunctionJson ++ "]")

def unknownTopLevelField : String :=
  "{\"extra\":true,\"schema\":{\"encoding\":\"structural-adt\",\"failClosed\":true,\"name\":\"gobra.internal\",\"version\":1},\"inputs\":[\"input.gobra\"],\"program\":{\"members\":[],\"source\":{\"origin\":{\"position\":{\"end\":null,\"file\":\"input.gobra\",\"start\":{\"column\":1,\"line\":1}},\"tag\":\"package input\"},\"tag\":\"Single\"},\"tag\":\"Program\",\"types\":[]}}"

def badSchemaVersion : String :=
  "{\"schema\":{\"encoding\":\"structural-adt\",\"failClosed\":true,\"name\":\"gobra.internal\",\"version\":2},\"inputs\":[\"input.gobra\"],\"program\":{\"members\":[],\"source\":{\"origin\":{\"position\":{\"end\":null,\"file\":\"input.gobra\",\"start\":{\"column\":1,\"line\":1}},\"tag\":\"package input\"},\"tag\":\"Single\"},\"tag\":\"Program\",\"types\":[]}}"

def unknownTag : String :=
  "{\"schema\":{\"encoding\":\"structural-adt\",\"failClosed\":true,\"name\":\"gobra.internal\",\"version\":1},\"inputs\":[\"input.gobra\"],\"program\":{\"members\":[],\"source\":{\"origin\":{\"position\":{\"end\":null,\"file\":\"input.gobra\",\"start\":{\"column\":1,\"line\":1}},\"tag\":\"package input\"},\"tag\":\"Single\"},\"tag\":\"SurpriseProgram\",\"types\":[]}}"

def nonIntegralNumber : String :=
  "{\"schema\":{\"encoding\":\"structural-adt\",\"failClosed\":true,\"name\":\"gobra.internal\",\"version\":1},\"inputs\":[\"input.gobra\"],\"program\":{\"members\":[1.25],\"source\":{\"origin\":{\"position\":{\"end\":null,\"file\":\"input.gobra\",\"start\":{\"column\":1,\"line\":1}},\"tag\":\"package input\"},\"tag\":\"Single\"},\"tag\":\"Program\",\"types\":[]}}"

def malformedInputs : String :=
  "{\"schema\":{\"encoding\":\"structural-adt\",\"failClosed\":true,\"name\":\"gobra.internal\",\"version\":1},\"inputs\":[1],\"program\":{\"members\":[],\"source\":{\"origin\":{\"position\":{\"end\":null,\"file\":\"input.gobra\",\"start\":{\"column\":1,\"line\":1}},\"tag\":\"package input\"},\"tag\":\"Single\"},\"tag\":\"Program\",\"types\":[]}}"

def extraExpressionField : String :=
  documentWithMembers (
    "[{\"args\":[],\"backendAnnotations\":[],\"body\":{\"tag\":\"None\"},\"name\":" ++ functionProxyJson ++
    ",\"posts\":[],\"pres\":[{\"exp\":{\"b\":true,\"extra\":0,\"source\":" ++ sourceJson ++
    ",\"tag\":\"BoolLit\"},\"source\":" ++ sourceJson ++
    ",\"tag\":\"ExprAssertion\"}],\"results\":[],\"source\":" ++ sourceJson ++
    ",\"tag\":\"Function\",\"terminationMeasures\":[]}]")

def unknownBodyStmt : String :=
  documentWithMembers (
    "[{\"args\":[],\"backendAnnotations\":[],\"body\":{\"tag\":\"Some\",\"value\":{\"decls\":[],\"postprocessing\":[],\"seqn\":{\"source\":" ++
    sourceJson ++ ",\"stmts\":[{\"source\":" ++ sourceJson ++
    ",\"tag\":\"MysteryStmt\"}],\"tag\":\"MethodBodySeqn\"},\"source\":" ++ sourceJson ++
    ",\"tag\":\"MethodBody\"}},\"name\":" ++ functionProxyJson ++
    ",\"posts\":[],\"pres\":[],\"results\":[],\"source\":" ++ sourceJson ++
    ",\"tag\":\"Function\",\"terminationMeasures\":[]}]")

def backendAnnotation : String :=
  documentWithMembers (
    "[{\"args\":[],\"backendAnnotations\":[{\"tag\":\"Annotation\"}],\"body\":{\"tag\":\"None\"},\"name\":" ++
    functionProxyJson ++ ",\"posts\":[],\"pres\":[],\"results\":[],\"source\":" ++
    sourceJson ++ ",\"tag\":\"Function\",\"terminationMeasures\":[]}]")

private def expectOk (name contents : String) : IO Bool := do
  match GoLean.GobraJson.decodeString contents with
  | .ok _ =>
      IO.println s!"ok: {name}"
      return true
  | .error err =>
      IO.eprintln s!"FAIL: {name}: expected success, got {err}"
      return false

private def expectError (name contents : String) : IO Bool := do
  match GoLean.GobraJson.decodeString contents with
  | .ok _ =>
      IO.eprintln s!"FAIL: {name}: expected failure"
      return false
  | .error _ =>
      IO.println s!"ok: {name}"
      return true

def main : IO UInt32 := do
  let mut passed := true
  passed := passed && (← expectOk "valid document" validDocument)
  passed := passed && (← expectOk "valid function document" validFunctionDocument)
  passed := passed && (← expectError "unknown top-level field" unknownTopLevelField)
  passed := passed && (← expectError "bad schema version" badSchemaVersion)
  passed := passed && (← expectError "unknown tag" unknownTag)
  passed := passed && (← expectError "non-integral number" nonIntegralNumber)
  passed := passed && (← expectError "malformed inputs" malformedInputs)
  passed := passed && (← expectError "extra expression field" extraExpressionField)
  passed := passed && (← expectError "unknown body statement" unknownBodyStmt)
  passed := passed && (← expectError "backend annotation" backendAnnotation)
  if passed then
    return 0
  else
    return 1

end Tests.GobraJson

def main : IO UInt32 :=
  Tests.GobraJson.main
