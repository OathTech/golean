import GoLean.GoCore
import GoLean.NativeToIR
import GoLean.StrictJsonParse

-- [AGENT] seeded-heap design probe (2026-10-09): a hand-seeded store (two-phase: zero cells, then
-- stores) threaded through the EXISTING bindParams/allocDecls/pinResultLocs/runConfig. No code change.
open GoLean GoLean.GoCore GoLean.GoCore.Machine

def loadProgram (path : System.FilePath) : IO Program := do
  let bytes ← IO.FS.readBinFile path
  match GoLean.StrictJson.parseBytes bytes GoLean.StrictJson.wireNestingDepth with
  | .error e => throw (IO.userError e)
  | .ok json =>
    match GoLean.NativeToIR.decodeProgram json with
    | .error e => throw (IO.userError e)
    | .ok p => pure p

/-- cells = (declared type, value with seed-relative refs ALREADY resolved against base b). -/
def seededRun (p : Program) (name : String) (cells : Nat → Array (Ty × GoValue))
    (args : Nat → Array GoValue) (checkWf : Bool := true) :
    Except Stop (Nat × Array GoValue × Array GoValue × Bool) := do
  let pctx : ProgramCtx := ⟨p⟩
  let some func := findFunctionIn? p.funcs ⟨name⟩ | throw (.stuck s!"no func {name}")
  let s₀ ← seedGlobals pctx {} p.globals
  let (s₁, ch₁) ← runPkgInitM pctx 1000000 s₀ []
  let b := s₁.heap.size
  let cs := cells b
  let mut s := s₁
  let mut locs : Array Loc := #[]
  for (ty, _) in cs do
    let z ← defaultValue pctx ty
    let (l, s') := s.allocCell (.value ty z)
    locs := locs.push l
    s := s'
  for (l, c) in locs.zip cs do
    s ← storeLoc pctx s l c.2
  if checkWf then
    if StateWf pctx s then pure () else throw (.internal "seeded state ill-formed")
  let (env, s₂) ← bindParams pctx [] s func.args.toList (args b).toList
  let wfAfterBind := decide (StateWf pctx s₂)
  let (frameEnv, s₃) ← allocDecls pctx env s₂ func.results.toList
  let resultLocs ← pinResultLocs frameEnv func.results.toList
  let c₀ : Config := .exec func.body frameEnv (.frame [] [] [] [] .stop func.id)
  let (sF, _) ← runConfig pctx 1000000 s₃ c₀ ch₁
  let results ← loadMany pctx sF resultLocs
  let finals ← locs.mapM (loadLoc pctx sF)
  return (b, results.toArray, finals, wfAfterBind)

def ref (b k : Nat) : GoValue := .addr (.base ⟨b + k⟩)

def main1 : IO Unit := do
  let p ← loadProgram "/home/dev/projects/golean/.tmp/seed-probe/p0b-wire.json"
  IO.println s!"globals={p.globals.size} funcs={p.funcs.size} types={p.typeDefs.size}"
  IO.println s!"typeDefs keys: {p.typeDefs.map (·.1.key)}"
  -- 1. inc(p *int): cell0 : int = 41, arg ref 0 → cell0 = 42
  IO.println s!"inc: {repr (seededRun p "inc" (fun _ => #[(.int .int, .int 41 .int)]) (fun b => #[ref b 0]))}"
  -- 2. addNaive ALIASED: one [2]int cell = [5,7]; both args ref 0 → [12,19]
  IO.println s!"addNaive aliased: {repr (seededRun p "addNaive"
    (fun _ => #[(.array 2 (.int .int), .array #[.int 5 .int, .int 7 .int])]) (fun b => #[ref b 0, ref b 0]))}"
  -- 3. addNaive DISTINCT: two cells → [12,12],[5,7]
  IO.println s!"addNaive distinct: {repr (seededRun p "addNaive"
    (fun _ => #[(.array 2 (.int .int), .array #[.int 5 .int, .int 7 .int]),
                (.array 2 (.int .int), .array #[.int 5 .int, .int 7 .int])]) (fun b => #[ref b 0, ref b 1]))}"
  -- 4. sum2 CYCLIC: Node{2, &c1}, Node{3, &c0}; arg ref 0 → result 5
  let nodeIdx := (p.typeDefs.lookupName? ⟨"main.Node"⟩).map (·.1)
  IO.println s!"main.Node idx = {repr nodeIdx}"
  match nodeIdx with
  | some idx =>
    IO.println s!"sum2 cyclic: {repr (seededRun p "sum2"
      (fun b => #[(.defined idx, .struct ⟨"main.Node"⟩ #[("v", .int 2 .int), ("next", ref b 1)]),
                  (.defined idx, .struct ⟨"main.Node"⟩ #[("v", .int 3 .int), ("next", ref b 0)])])
      (fun b => #[ref b 0]))}"
  | none => IO.println "no main.Node"
  -- 5. DANGLING ref through bindParams (no seed cells; arg = .base 99): today's gap
  IO.println s!"dangling (wf check off): {repr (seededRun p "inc" (fun _ => #[]) (fun _ => #[.addr (.base ⟨99⟩)]) false)}"
  -- 6. an .int at a *int param passes bindParams (normalizer catch-all); where does it fail?
  IO.println s!"int-at-pointer: {repr (seededRun p "inc" (fun _ => #[]) (fun _ => #[.int 5 .int]) false)}"
  -- 7. a ref to the WRONG cell type: cell0 : bool, arg ref 0 at *int
  IO.println s!"bool cell at *int: {repr (seededRun p "inc" (fun _ => #[(.bool, .bool true)]) (fun b => #[ref b 0]))}"

/-- bind ONLY (no run): does the entry store stay StateWf with a dangling address argument? -/
def bindOnly (p : Program) (name : String) (args : Array GoValue) : Except Stop (Nat × Bool × Bool) := do
  let pctx : ProgramCtx := ⟨p⟩
  let some func := findFunctionIn? p.funcs ⟨name⟩ | throw (.stuck s!"no func {name}")
  let s₀ ← seedGlobals pctx {} p.globals
  let (s₁, _) ← runPkgInitM pctx 1000000 s₀ []
  let (_, s₂) ← bindParams pctx [] s₁ func.args.toList args.toList
  return (s₂.heap.size, decide (StateWf pctx s₁), decide (StateWf pctx s₂))

def main2 : IO Unit := do
  let p ← loadProgram "/home/dev/projects/golean/.tmp/seed-probe/p0b-wire.json"
  IO.println s!"bindOnly dangling .base 99 at *int: (heap size, wf before, wf after) = {repr (bindOnly p "inc" #[.addr (.base ⟨99⟩)])}"
  IO.println s!"bindOnly .int 5 at *int: {repr (bindOnly p "inc" #[.int 5 .int])}"

def main : IO Unit := do
  main1
  main2
