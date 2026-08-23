/- Campaign Arc 2, U4 probe D (MEASUREMENT ONLY): the exercised-ARM
census — which stepFn configuration shapes the witness run actually
executes, with counts. This is what picks the fast-mirror's real arms
vs fail-closed stubs (route memo §6.7; the one-directional refinement
makes every stubbed arm's sim case vacuous).

Classification: config head + one level of payload (statement /
expression / continuation constructor; op names for strict/stmt ops).
Run:  cd proofs && GOLEAN_MEM_MAX=16G ../scripts/capped \
        lake env lean ../docs/campaign-arc2-probes/probeD-armcensus.lean
-/
import GoLeanProofs.Specs.RaftAgreement
import Std.Data.HashMap

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Examples.RaftTwin
open Std (HashMap)

abbrev Census := HashMap String Nat

def bump (c : Census) (k : String) : Census := c.insert k (c.getD k 0 + 1)

def stmtKey : Stmt → String
  | .seqn .. => "seqn" | .block .. => "block" | .breakable .. => "breakable"
  | .initialization .. => "initialization"
  | .assign .. => "assign" | .assignMany .. => "assignMany"
  | .newValue .. => "newValue" | .makeSlice .. => "makeSlice"
  | .makeMap .. => "makeMap" | .mapAssign .. => "mapAssign"
  | .mapDelete .. => "mapDelete" | .clearMap .. => "clearMap"
  | .clearSlice .. => "clearSlice" | .sortSlice .. => "sortSlice"
  | .mapLookup .. => "mapLookup" | .typeAssert .. => "typeAssert"
  | .appendSlice .. => "appendSlice" | .copySlice .. => "copySlice"
  | .call .. => "call" | .callValue .. => "callValue"
  | .deferCall .. => "deferCall"
  | .ifThenElse .. => "ifThenElse" | .while .. => "while"
  | .mapRange .. => "mapRange"
  | .returnStmt => "returnStmt" | .breakStmt => "breakStmt"
  | .continueStmt => "continueStmt" | .labeled .. => "labeled"
  | .breakTo .. => "breakTo" | .continueTo .. => "continueTo"
  | .panicStmt .. => "panicStmt" | .label .. => "label"
  | .makeChan .. => "makeChan" | .chanSend .. => "chanSend"
  | .chanRecv .. => "chanRecv" | .closeChan .. => "closeChan"
  | .selectStmt .. => "selectStmt" | .goStmt .. => "goStmt"
  | .unsupported .. => "unsupported" | .syncStmt op _ _ => s!"syncStmt {repr op}"

def exprKey : Expr → String
  | .var .. => "var" | .nil .. => "nilE" | .intLit .. => "intLit"
  | .floatLit .. => "floatLitE" | .stringLit .. => "stringLit"
  | .boolLit .. => "boolLit" | .convert .. => "convert"
  | .add .. => "add" | .sub .. => "sub" | .mul .. => "mul"
  | .div .. => "div" | .mod .. => "mod"
  | .shiftLeft .. => "shiftLeft" | .shiftRight .. => "shiftRight"
  | .bitAnd .. => "bitAnd" | .bitOr .. => "bitOr"
  | .bitXor .. => "bitXor" | .bitClear .. => "bitClear"
  | .bitNeg .. => "bitNeg" | .neg .. => "neg"
  | .eqCmp .. => "eqCmp" | .neqCmp .. => "neqCmp"
  | .atMostCmp .. => "atMostCmp" | .atLeastCmp .. => "atLeastCmp"
  | .lessCmp .. => "lessCmp" | .greaterCmp .. => "greaterCmp"
  | .and .. => "and" | .or .. => "or" | .not .. => "not"
  | .ref .. => "ref" | .funcVal .. => "funcValE" | .locLit .. => "locLit"
  | .deref .. => "deref" | .fieldGet .. => "fieldGet"
  | .fieldAddr .. => "fieldAddr" | .structLit .. => "structLit"
  | .arrayLit .. => "arrayLit" | .defaultValue .. => "defaultValueE"
  | .toInterface .. => "toInterface" | .typeAssert .. => "typeAssertE"
  | .indexGet .. => "indexGet" | .indexAddr .. => "indexAddr"
  | .mapGet .. => "mapGet" | .slice .. => "sliceE"
  | .length .. => "length" | .capacity .. => "capacity"
  | _ => "exprOther"

def contKey : Cont → String
  | .stop => "stop" | .seq .. => "seq" | .loop .. => "loopK"
  | .frame .. => "frameK"
  | .deferCalleeK .. => "deferCalleeK" | .deferArgsK .. => "deferArgsK"
  | .breakableK .. => "breakableK" | .labelK .. => "labelK"
  | .callValCalleeK .. => "callValCalleeK"
  | .callValArgsK .. => "callValArgsK"
  | .strictK op _ _ _ _ => s!"strictK {(reprStr op).replace "GoLean.GoCore.Machine.StrictOp." ""}"
  | .andK .. => "andK" | .orK .. => "orK" | .boolK .. => "boolK"
  | .ifK .. => "ifK" | .whileK .. => "whileK"
  | .callArgsK .. => "callArgsK"
  | .stmtOpK op _ _ _ _ _ => s!"stmtOpK {(reprStr op).replace "GoLean.GoCore.Machine.StmtOp." ""}"
  | .mapRangeK .. => "mapRangeK" | .mapIterK .. => "mapIterK"
  | .panicArgK .. => "panicArgK" | .panicResumeK .. => "panicResumeK"
  | .chanStK .. => "chanStK" | .selectOpsK .. => "selectOpsK"
  | .tgtOpK .. => "tgtOpK" | .rhsK .. => "rhsK"
  | .storeK .. => "storeK" | .goCalleeK .. => "goCalleeK"
  | .goArgsK .. => "goArgsK" | .syncStK .. => "syncStK"

/-- Truncate op-name keys to the head token (payload args of repr'd
ops would explode the key space). -/
def trunc (s : String) : String :=
  match s.splitOn " " with
  | a :: b :: _ => a ++ " " ++ b
  | _ => s

def configKey : Config → String
  | .exec st _ _ => "exec " ++ trunc (stmtKey st)
  | .evalE e _ _ => "evalE " ++ exprKey e
  | .retV _ k => "retV " ++ trunc (contKey k)
  | .next k => "next " ++ trunc (contKey k)
  | .breaking _ => "breaking" | .continuing _ => "continuing"
  | .returning k => "returning " ++ trunc (contKey k)
  | .breakingTo _ _ => "breakingTo" | .continuingTo _ _ => "continuingTo"
  | .panicking _ _ => "panicking" | .panicked _ => "panicked"
  | _ => "configOther"

instance : Inhabited (Except GoError (ExecState × Choices × Nat × Census)) :=
  ⟨.error .fuelOut⟩

partial def runCount (σ : ExecState) (c : Config) (ch : Choices)
    (n : Nat) (census : Census) :
    Except GoError (ExecState × Choices × Nat × Census) :=
  match c with
  | .next .stop => .ok (σ, ch, n, census)
  | .panicked msg => .error (.panic msg)
  | .blockedSend _ _ _ => .error .deadlock
  | .blockedRecv _ _ _ _ _ => .error .deadlock
  | .blockedSelect _ _ _ => .error .deadlock
  | .blockedSync _ _ _ _ => .error .deadlock
  | c =>
      match stepFn σ c ch with
      | .error e => .error e
      | .ok (c', σ', ch') => runCount σ' c' ch' (n + 1) (bump census (configKey c))

def probe : Except GoError (Nat × Result × Census) := do
  let program := twinLowered
  let func ←
    match findFunctionIn? program.funcs ⟨"twinChoiceVerdict"⟩ with
    | some f => pure f
    | none => throw (.stuck "entry not found")
  let state : ExecState :=
    { types := program.typeDefs.toList, functions := program.funcs
      methods := program.methods, methodSets := program.methodSets }
  let s₀ ← seedGlobals state program.globals
  let (s₁, ch₁, _, cen₀) ←
    match findFunctionIn? s₀.functions pkgInitFuncId with
    | none => pure (s₀, ([] : Choices), 0, ({} : Census))
    | some initF =>
        runCount s₀ (.exec initF.body [] (.frame [] [] [] [] .stop)) [] 0 {}
  let (env, s₂) ← bindParams [] s₁ func.args.toList []
  let (frameEnv, s₃) ← allocDecls env s₂ func.results.toList
  let resultLocs ← pinResultLocs frameEnv func.results.toList
  let c₀ : Config := .exec func.body frameEnv (.frame [] [] [] [] .stop)
  let (sF, _, nSubj, cen) ← runCount s₃ c₀ ch₁ 0 cen₀
  let r : Result := { values := (← loadMany sF resultLocs).toArray }
  return (nSubj, r, cen)

def report : IO Unit := do
  match probe with
  | .error e => IO.println s!"PROBE ERROR: {repr e}"
  | .ok (nSubj, r, cen) =>
    IO.println s!"subjSteps={nSubj}"
    IO.println s!"verdict={repr r.values}"
    let entries := cen.toList.toArray.qsort (fun a b => a.2 > b.2)
    IO.println s!"distinctArms={entries.size}"
    for (k, v) in entries do
      IO.println s!"{v}\t{k}"

#eval report
