/- Campaign Arc 2, probe A2 (MEASUREMENT ONLY): the defer-callee
census — closes probe A's recorded gap. Captures the deferred CALLEE's
fid at defer REGISTRATION (the `.retV (.funcVal …) (.deferCalleeK …)`
config — the callee expression is evaluated at the `defer` statement,
so every defer registration passes through this shape exactly once).
Registration count = execution count on this run (no panic-path
short-circuits: the run completes normally).

Run:  cd proofs && GOLEAN_MEM_MAX=16G ../scripts/capped \
        lake env lean ../docs/campaign-arc2-probes/probeA2-defercallees.lean
-/
import GoLeanProofs.Specs.RaftAgreement
import Std.Data.HashMap

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Examples.RaftTwin
open Std (HashMap)

abbrev Census := HashMap String Nat

def bump (c : Census) (k : String) : Census := c.insert k (c.getD k 0 + 1)

def censusOf (c : Config) (census : Census) : Census :=
  match c with
  | .retV (.funcVal fid _) (.deferCalleeK _ _ _) =>
      bump census s!"defer {fid.key}"
  | .retV v (.deferCalleeK _ _ _) =>
      bump census s!"defer NON-FUNCVAL {reprStr v |>.take 40}"
  | _ => census

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
      | .ok (c', σ', ch') => runCount σ' c' ch' (n + 1) (censusOf c census)

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
  let (s₁, ch₁, _, cenInit) ←
    match findFunctionIn? s₀.functions pkgInitFuncId with
    | none => pure (s₀, ([] : Choices), 0, ({} : Census))
    | some initF =>
        runCount s₀ (.exec initF.body [] (.frame [] [] [] [] .stop)) [] 0 {}
  let (env, s₂) ← bindParams [] s₁ func.args.toList []
  let (frameEnv, s₃) ← allocDecls env s₂ func.results.toList
  let resultLocs ← pinResultLocs frameEnv func.results.toList
  let c₀ : Config := .exec func.body frameEnv (.frame [] [] [] [] .stop)
  let (sF, _, nSubj, cen) ← runCount s₃ c₀ ch₁ 0 cenInit
  let r : Result := { values := (← loadMany sF resultLocs).toArray }
  return (nSubj, r, cen)

def report : IO Unit := do
  match probe with
  | .error e => IO.println s!"PROBE ERROR: {repr e}"
  | .ok (nSubj, r, cen) =>
    IO.println s!"subjSteps={nSubj}"
    IO.println s!"verdict={repr r.values}"
    let entries := cen.toList.toArray.qsort (fun a b => a.2 > b.2)
    IO.println s!"distinctDeferCallees={entries.size}"
    let mut total := 0
    for (k, v) in entries do
      IO.println s!"{v}\t{k}"
      total := total + v
    IO.println s!"totalDeferRegistrations={total}"

#eval report
