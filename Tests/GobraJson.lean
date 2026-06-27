import GoLean.GobraJson

namespace Tests.GobraJson

def validDocument : String :=
  "{\"schema\":{\"encoding\":\"structural-adt\",\"failClosed\":true,\"name\":\"gobra.internal\",\"version\":1},\"inputs\":[\"input.gobra\"],\"program\":{\"members\":[],\"source\":{\"origin\":{\"position\":{\"end\":null,\"file\":\"input.gobra\",\"start\":{\"column\":1,\"line\":1}},\"tag\":\"package input\"},\"tag\":\"Single\"},\"tag\":\"Program\",\"types\":[]}}"

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
  passed := passed && (← expectError "unknown top-level field" unknownTopLevelField)
  passed := passed && (← expectError "bad schema version" badSchemaVersion)
  passed := passed && (← expectError "unknown tag" unknownTag)
  passed := passed && (← expectError "non-integral number" nonIntegralNumber)
  passed := passed && (← expectError "malformed inputs" malformedInputs)
  if passed then
    return 0
  else
    return 1

end Tests.GobraJson

def main : IO UInt32 :=
  Tests.GobraJson.main
