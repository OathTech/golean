/- Campaign Arc 2, probe C (MEASUREMENT ONLY): heap length and
allocator frontier sampled every 50k subject steps — anchors the
checkpoint-segment sizing in the route memo (a kernel step's heap
traversal cost scales with the CONCRETE heap it walks; the checkpoint
literals' size scales with it too).

Run:  cd proofs && GOLEAN_MEM_MAX=16G ../scripts/capped \
        lake env lean ../docs/campaign-arc2-probes/probeC-heapgrowth.lean
-/
import GoLeanProofs.Specs.RaftAgreement

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Examples.RaftTwin

instance : Inhabited (Except GoError (ExecState × Choices × Nat × List (Nat × Nat × Nat))) :=
  ⟨.error .fuelOut⟩

/-- `runConfig` without fuel; samples `(n, heap.length, nextAddr)`
every 50,000 steps. -/
partial def runSample (σ : ExecState) (c : Config) (ch : Choices)
    (n : Nat) (acc : List (Nat × Nat × Nat)) :
    Except GoError (ExecState × Choices × Nat × List (Nat × Nat × Nat)) :=
  match c with
  | .next .stop => .ok (σ, ch, n, acc.reverse)
  | .panicked msg => .error (.panic msg)
  | .blockedSend _ _ _ => .error .deadlock
  | .blockedRecv _ _ _ _ _ => .error .deadlock
  | .blockedSelect _ _ _ => .error .deadlock
  | .blockedSync _ _ _ _ => .error .deadlock
  | c =>
      let acc := if n % 50000 == 0 then (n, σ.heap.length, σ.nextAddr) :: acc else acc
      match stepFn σ c ch with
      | .error e => .error e
      | .ok (c', σ', ch') => runSample σ' c' ch' (n + 1) acc

def probe : Except GoError (Nat × Nat × Nat × List (Nat × Nat × Nat)) := do
  let program := twinLowered
  let func ←
    match findFunctionIn? program.funcs ⟨"twinChoiceVerdict"⟩ with
    | some f => pure f
    | none => throw (.stuck "entry not found")
  let state : ExecState :=
    { types := program.typeDefs.toList, functions := program.funcs
      methods := program.methods, methodSets := program.methodSets }
  let s₀ ← seedGlobals state program.globals
  let (s₁, ch₁, _nInit, _) ←
    match findFunctionIn? s₀.functions pkgInitFuncId with
    | none => pure (s₀, ([] : Choices), 0, [])
    | some initF =>
        runSample s₀ (.exec initF.body [] (.frame [] [] [] [] .stop)) [] 0 []
  let (env, s₂) ← bindParams [] s₁ func.args.toList []
  let (frameEnv, s₃) ← allocDecls env s₂ func.results.toList
  let _ ← pinResultLocs frameEnv func.results.toList
  let c₀ : Config := .exec func.body frameEnv (.frame [] [] [] [] .stop)
  let (sF, _, nSubj, samples) ← runSample s₃ c₀ ch₁ 0 []
  return (nSubj, sF.heap.length, sF.nextAddr, samples)

def report : IO Unit := do
  match probe with
  | .error e => IO.println s!"PROBE ERROR: {repr e}"
  | .ok (nSubj, hLen, na, samples) =>
    IO.println s!"subjSteps={nSubj} finalHeapLen={hLen} finalNextAddr={na}"
    IO.println "samples (subjStep, heapLen, nextAddr):"
    for (n, h, a) in samples do
      IO.println s!"  {n}\t{h}\t{a}"

#eval report
