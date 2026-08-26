import GoLeanProofs.Specs.TwinProgram
import GoLeanProofs.Frame.ChoiceInv

/-! # SP1: the SEED-LITERAL GENERATOR (probe-only; emits
`GoLeanProofs/Specs/Raft/SeedLit.lean` or `SeedLitVar.lean`)

Walks the pinned twin (`twinLowered`, entry `twinChoiceVerdict`) with
the SHIPPED `anchorRun` (Frame/ChoiceInv) to the first
`main.twin.step` call — the post-init pre-campaign anchor — and
prints: the post-setup state literals (the closed setup link's
target), a front-sliver boundary (env FRONTN, default 300), and the
anchor state/config literals. Env PVAR="k:v,k:v" perturbs the stream
(the variant generator run); env POUT sets the output file and PFX
the definition prefix. The literal is NOT trusted from this probe:
SeedPin.lean's kernel links replay the setup + front sliver and
readout theorems pin the endpoint. -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.ChoiceErase

deriving instance Repr for GoLean.GoCore.Machine.Cont
deriving instance Repr for GoLean.GoCore.Machine.Config

def seedAnchorB : Config → Bool
  | .exec (.call _ fid _) _ _ => fid.key == "main.twin.step"
  | _ => false

def pr {α : Type} [Repr α] (x : α) : String := ((repr x).pretty 110)

partial def walkN (σ : ExecState) (c : Config) (ch : Choices) (k : Nat) :
    Except String (ExecState × Config × Choices) :=
  if k = 0 then .ok (σ, c, ch)
  else
    match stepFn σ c ch with
    | .ok (c2, σ2, ch2) => walkN σ2 c2 ch2 (k-1)
    | .error e => .error s!"{e.message.take 200}"

def parsePerturb (s : String) : List (Nat × Nat) :=
  (s.splitOn ",").filterMap (fun p =>
    match p.splitOn ":" with
    | [a, b] => match a.toNat?, b.toNat? with
      | some k, some v => some (k, v)
      | _, _ => none
    | _ => none)

def mkStreamP (ps : List (Nat × Nat)) : Choices :=
  (List.range 25000).map (fun i =>
    match ps.lookup i with | some v => v | none => 0)

partial def chunkList {α : Type} (n : Nat) (l : List α) : List (List α) :=
  if l.isEmpty then [] else l.take n :: chunkList n (l.drop n)

/-- chunk a heap into defs of ≤500 cells -/
def chunkDefs (name : String) (h : GoCore.Heap) : String := Id.run do
  let chunks := chunkList 500 h
  let mut out := ""
  let mut i := 0
  for c in chunks do
    out := out ++ s!"def {name}Chunk{i} : GoLean.GoCore.Heap :=\n  {pr c}\n\n"
    i := i + 1
  out := out ++ s!"def {name} : GoLean.GoCore.Heap :=\n  "
  if i == 0 then
    out := out ++ "[]\n\n"
  else
    out := out ++ String.intercalate " ++ " ((List.range i).map (fun j => s!"{name}Chunk{j}")) ++ "\n\n"
  return out

def go : IO Unit := do
  let pvar := (← IO.getEnv "PVAR").getD ""
  let pfx := (← IO.getEnv "PFX").getD "seed"
  let pout := (← IO.getEnv "POUT").getD "GoLeanProofs/Specs/Raft/SeedLit.lean"
  let frontN := ((← IO.getEnv "FRONTN").bind String.toNat?).getD 300
  let perturbs := parsePerturb pvar
  let stream := mkStreamP perturbs
  match runProgramSetupM 20000 GoLean.Examples.RaftTwin.twinLowered
      "twinChoiceVerdict" #[] stream with
  | .error e => IO.println s!"SETUP ERROR: {e.message.take 300}"
  | .ok (c₀, s₃, _, ch₁) =>
      IO.println s!"setup: heap={s₃.heap.length} na={s₃.nextAddr}"
      -- the anchored run via the SHIPPED runner
      match anchorRun seedAnchorB 200000 0 s₃ c₀ ch₁ with
      | none => IO.println "ANCHOR RUN FAILED"
      | some (nA, σA, cA, chA) =>
          let consumed := ch₁.length - chA.length
          IO.println s!"anchor: steps={nA} na={σA.nextAddr} heap={σA.heap.length} consumed={consumed}"
          -- front sliver boundary (canonical-generator only)
          match walkN s₃ c₀ ch₁ frontN with
          | .error e => IO.println s!"front sliver failed: {e}"
          | .ok (σF, cF, chF) =>
              let consumedF := ch₁.length - chF.length
              IO.println s!"front@{frontN}: na={σF.nextAddr} heap={σF.heap.length} consumedF={consumedF}"
              let mut out := "import GoLeanProofs.Specs.TwinProgram\nimport GoLean.GoCore.StepFn\n\n"
              out := out ++ s!"/-! # {pfx}-literals — GENERATED (SP1; generator\n"
              out := out ++ "`artifacts/probe/SeedLitGen.lean` — DO NOT EDIT BY HAND).\n\n"
              out := out ++ s!"The twin's POST-INIT PRE-CAMPAIGN state: runProgramSetupM +\n"
              out := out ++ s!"{nA} steps to the first `main.twin.step` call config, stream\n"
              out := out ++ (if perturbs.isEmpty then "CANONICAL (all zeros)"
                             else s!"PERTURBED at positions {pr perturbs} (zeros elsewhere)")
              out := out ++ s!", {consumed} choices consumed.\n"
              out := out ++ "Trust: the literal is generator-computed (compiled stepFn);\n"
              out := out ++ "SeedPin.lean's kernel links pin the setup segment and the front\n"
              out := out ++ "sliver, and its readout theorems pin the endpoint content —\n"
              out := out ++ "see its docstring for exactly what is and is not kernel-checked. -/\n\n"
              out := out ++ "namespace GoLean.RaftSeam\n\n"
              out := out ++ "open GoLean.GoCore GoLean.GoCore.Machine\n\n"
              out := out ++ "set_option maxRecDepth 8000000\n\n"
              if perturbs.isEmpty then
                -- setup + front only in the canonical file
                out := out ++ s!"def {pfx}SetupNa : Nat := {s₃.nextAddr}\n\n"
                out := out ++ s!"def {pfx}SetupHeap : GoLean.GoCore.Heap :=\n  {pr s₃.heap}\n\n"
                out := out ++ s!"def {pfx}SetupC : GoLean.GoCore.Machine.Config :=\n  {pr c₀}\n\n"
                out := out ++ s!"def {pfx}FrontN : Nat := {frontN}\n\n"
                out := out ++ s!"def {pfx}FrontNa : Nat := {σF.nextAddr}\n\n"
                out := out ++ s!"def {pfx}FrontConsumed : Nat := {consumedF}\n\n"
                out := out ++ chunkDefs s!"{pfx}FrontHeap" σF.heap
                out := out ++ s!"def {pfx}FrontC : GoLean.GoCore.Machine.Config :=\n  {pr cF}\n\n"
              else
                out := out ++ s!"def {pfx}Perturbs : List (Nat × Nat) := {pr perturbs}\n\n"
              out := out ++ s!"def {pfx}Steps : Nat := {nA}\n\n"
              out := out ++ s!"def {pfx}Consumed : Nat := {consumed}\n\n"
              out := out ++ s!"def {pfx}Na : Nat := {σA.nextAddr}\n\n"
              out := out ++ chunkDefs s!"{pfx}Heap" σA.heap
              out := out ++ s!"def {pfx}C : GoLean.GoCore.Machine.Config :=\n  {pr cA}\n\n"
              out := out ++ "end GoLean.RaftSeam\n"
              IO.FS.writeFile pout out
              IO.println s!"written {pout}: {out.length} chars"
              -- consistency probes: canonical form stats via the SHIPPED canonState
              let roots := ((List.range s₃.nextAddr).map
                (fun a => GoValue.addr (.base ⟨a⟩))) ++ [GoValue.addr (.base ⟨121⟩)]
              let σAs : ExecState := { σA with heap := σA.heap }
              let cf := canonState σAs roots
              IO.println s!"canon: roots={cf.roots.length} cells={cf.cells.length} flags={pr cf.flags}"

#eval go
