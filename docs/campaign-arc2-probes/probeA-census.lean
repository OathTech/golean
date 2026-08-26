/- Campaign Arc 2, probe A (MEASUREMENT ONLY — not proof-facing, not in
any build closure; lives under docs/ so no gate scans it, and `partial`
is fine here).

One compiled run of the twin from the pinned lowering that reports:
  * exact machine-step counts, init phase and subject phase separately
    (the kernel-frontier fuel: minimal completing fuel for `twinRun`
    is max(initSteps, subjSteps) + phase-terminal handling, since
    `runProgramM`'s fuel bounds each phase separately);
  * the final verdict (cross-checked against the U-c7 record
    `.ok #[int 0, int 1, int 6, int 1, int 1]` — if this probe's own
    driver loop drifted from `runConfig`, the verdict mismatch says so);
  * a call census on the default stream: distinct statically-named
    call sites entered (`Stmt.call` fids), value-call callees
    (`funcVal` fid at the `callValCalleeK` hand-off), and site counts
    for defer/go statements (recorded but not fid-resolved — honest
    gap, see the memo).

Run:  cd proofs && GOLEAN_MEM_MAX=16G ../scripts/capped \
        lake env lean ../docs/campaign-arc2-probes/probeA-census.lean
-/
import GoLeanProofs.Specs.RaftAgreement
import Std.Data.HashMap

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Examples.RaftTwin
open Std (HashMap)

abbrev Census := HashMap String Nat

def bump (c : Census) (k : String) : Census := c.insert k (c.getD k 0 + 1)

/-- Record the call-shaped configs. `Stmt.call` sites are recorded at
their `.exec` config (each dynamic execution of the site, whether the
call has arguments or not); value calls at the moment the evaluated
callee value reaches its continuation. -/
def censusOf (c : Config) (census : Census) : Census :=
  match c with
  | .exec (.call _ fid _) _ _ => bump census s!"call {fid.key}"
  | .retV (.funcVal fid _) (.callValCalleeK _ _ _ _) =>
      bump census s!"valcall {fid.key}"
  | .exec (.callValue _ _ _) _ _ => bump census "site:callValue"
  | .exec (.deferCall _ _) _ _ => bump census "site:deferCall"
  | .exec (.goStmt _ _) _ _ => bump census "site:goStmt"
  | _ => census

instance : Inhabited (Except GoError (ExecState × Choices × Nat × Census)) :=
  ⟨.error .fuelOut⟩

/-- `runConfig` without fuel, counting steps and collecting the census.
Terminal/blocked classification mirrors `runConfig` exactly. -/
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

/-- `runProgramM`'s wiring (find → arity → seed → StateWf → `$pkginit` →
bind → subject) with the fuel loop replaced by `runCount`. -/
def probe : Except GoError (Nat × Nat × Result × Census) := do
  let program := twinLowered
  let func ←
    match findFunctionIn? program.funcs ⟨"twinChoiceVerdict"⟩ with
    | some f => pure f
    | none => throw (.stuck "entry not found")
  let state : ExecState :=
    { types := program.typeDefs.toList, functions := program.funcs
      methods := program.methods, methodSets := program.methodSets }
  let s₀ ← seedGlobals state program.globals
  if StateWf s₀ then pure () else throw (.internal "StateWf refused")
  let (s₁, ch₁, nInit, cenInit) ←
    match findFunctionIn? s₀.functions pkgInitFuncId with
    | none => pure (s₀, ([] : Choices), 0, ({} : Census))
    | some initF =>
        runCount s₀ (.exec initF.body [] (.frame [] [] [] [] .stop)) [] 0 {}
  let (env, s₂) ← bindParams [] s₁ func.args.toList []
  let (frameEnv, s₃) ← allocDecls env s₂ func.results.toList
  let resultLocs ← pinResultLocs frameEnv func.results.toList
  let c₀ : Config := .exec func.body frameEnv (.frame [] [] [] [] .stop)
  let (sF, _, nSubj, cenSubj) ← runCount s₃ c₀ ch₁ 0 cenInit
  let r : Result := { values := (← loadMany sF resultLocs).toArray }
  return (nInit, nSubj, r, cenSubj)

def report : IO Unit := do
  match probe with
  | .error e => IO.println s!"PROBE ERROR: {repr e}"
  | .ok (nInit, nSubj, r, cen) =>
    IO.println s!"initSteps={nInit}"
    IO.println s!"subjSteps={nSubj}"
    IO.println s!"verdict={repr r.values}"
    let entries := cen.toList.toArray.qsort (fun a b => a.2 > b.2)
    IO.println s!"censusEntries={entries.size}"
    for (k, v) in entries do
      IO.println s!"{v}\t{k}"

#eval report
