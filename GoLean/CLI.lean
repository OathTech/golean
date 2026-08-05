import GoLean.GoCore
import GoLean.NativeToIR
import GoLean.StrictJson
import Lean.Data.Json

namespace GoLean.CLI

open System
open Lean

private def observationSchema : String :=
  "golean-observation-v1"

structure RunArgs where
  input : Option FilePath := none
  functionName : Option String := none
  args : Array Int := #[]
  /-- Fuel counts MACHINE STEPS (reshape S3, 2026-07-23; previously
  while-back-edges + call entries only), so the default is retuned upward.
  No corpus case or script pins `--fuel`; the tracked baseline gates the
  retune. -/
  fuel : Nat := 10000000
  /-- Nondeterminism oracle: the choice stream consumed at nondeterministic
  points (map iteration order, append capacity). Empty is the canonical
  default. The harness runs the same program under several sequences to check
  observation invariance. -/
  choices : List Nat := []
  deriving Repr

private def usage : String :=
  "usage:\n" ++
  "  golean native-json-run --input <file> --function <name> [--arg-int <n> ...] [--fuel <n>] [--choices <n,n,...>]\n" ++
  "  golean observation-eq --left <json> --right <json>\n" ++
  "  golean coverage-observations --input <file> --function <name> [--arg-int <n> ...] [--fuel <n>]\n" ++
  "      [--max-width <B>] [--max-sites <D>] [--cap <N>] [--work-cap <W>]\n"

private def absoluteFrom (base : FilePath) (path : FilePath) : FilePath :=
  if path.isRelative then (base / path).normalize else path.normalize

private def parseObservationEqArgs : List String → Option String → Option String →
    Except String (String × String)
  | [], some left, some right => .ok (left, right)
  | [], _, _ => .error s!"missing --left <json> or --right <json>\n{usage}"
  | "--left" :: json :: rest, none, right => parseObservationEqArgs rest (some json) right
  | "--left" :: _ :: _, some _, _ => .error s!"duplicate --left\n{usage}"
  | "--right" :: json :: rest, left, none => parseObservationEqArgs rest left (some json)
  | "--right" :: _ :: _, _, some _ => .error s!"duplicate --right\n{usage}"
  | flag :: _, _, _ => .error s!"unknown or incomplete option: {flag}\n{usage}"

private def parseJsonInt (path value : String) : Except String Int := do
  GoLean.StrictJson.int path (← Json.parse value)

private def parseJsonNat (path value : String) : Except String Nat := do
  let value ← parseJsonInt path value
  if value < 0 then
    throw s!"{path}: expected nonnegative integer, got {value}"
  return value.toNat

private def parseRunArgs : List String → RunArgs → Except String RunArgs
  | [], cfg => .ok cfg
  | "--input" :: path :: rest, cfg =>
      parseRunArgs rest { cfg with input := some (FilePath.mk path) }
  | "--function" :: name :: rest, cfg =>
      parseRunArgs rest { cfg with functionName := some name }
  | "--arg-int" :: value :: rest, cfg => do
      parseRunArgs rest { cfg with args := cfg.args.push (← parseJsonInt "--arg-int" value) }
  | "--fuel" :: value :: rest, cfg => do
      parseRunArgs rest { cfg with fuel := (← parseJsonNat "--fuel" value) }
  | "--choices" :: value :: rest, cfg => do
      let parts := (value.splitOn ",").filter (fun s => !s.isEmpty)
      let choices ← parts.mapM (fun s => parseJsonNat "--choices" s)
      parseRunArgs rest { cfg with choices }
  | flag :: _, _ => .error s!"unknown or incomplete option: {flag}\n{usage}"

/-- The OBSERVATION channel renders type names the way Go's
`reflect.Type.Name()` does — WITHOUT the package qualifier — while
`TypeId` keys are package-qualified for identity (interfaces campaign,
2026-07-30: cross-package identity + Go-exact panic messages need the
qualifier; the observation comparator needs it stripped). -/
private def unqualifiedTypeName (typeId : TypeId) : String :=
  match typeId.key.splitOn "." with
  | [] => typeId.key
  | parts => parts.getLast!

private def locJson : Loc → Json
  | .base addr => Json.mkObj [("tag", Json.str "addr"), ("id", Lean.toJson addr.id)]
  | .field base typeId fieldName =>
      Json.mkObj [
        ("tag", Json.str "fieldAddr"),
        ("base", locJson base),
        ("typeName", Json.str (unqualifiedTypeName typeId)),
        ("fieldName", Json.str fieldName)
      ]
  | .index base index =>
      Json.mkObj [
        ("tag", Json.str "indexAddr"),
        ("base", locJson base),
        ("index", Lean.toJson index)
      ]

private partial def goValueJson : GoValue → Json
  | .unit => Json.mkObj [("tag", Json.str "unit")]
  | .bool value => Json.mkObj [("tag", Json.str "bool"), ("value", Lean.toJson value)]
  | .int value _ => Json.mkObj [("tag", Json.str "int"), ("value", Lean.toJson value)]
  | .string value => Json.mkObj [("tag", Json.str "string"), ("bytes", Lean.toJson value.byteNats)]
  | .addr loc => locJson loc
  | .nil => Json.mkObj [("tag", Json.str "nil")]
  -- Func values are not observable in Go (not comparable, not printable),
  -- so the observation channel reports identity only; a case whose OUTPUT
  -- is a func value is outside the differential's comparable surface.
  | .funcVal fid _ =>
      Json.mkObj [("tag", Json.str "func"), ("id", Json.str fid.key)]
  | .interface dynamic value =>
      Json.mkObj [
        ("tag", Json.str "interface"),
        ("dynamic", Json.str dynamic.dynamicName),
        ("value", goValueJson value)
      ]
  | .struct typeId fields =>
      Json.mkObj [
        ("tag", Json.str "struct"),
        ("typeName", Json.str (unqualifiedTypeName typeId)),
        ("fields", Json.arr (fields.map (fun (name, value) =>
          Json.mkObj [("name", Json.str name), ("value", goValueJson value)])))
      ]
  | .array values =>
      Json.mkObj [
        ("tag", Json.str "array"),
        ("values", Json.arr (values.map goValueJson))
      ]
  | .slice value =>
      Json.mkObj [
        ("tag", Json.str "slice"),
        ("base", match value.base with
          | some loc => locJson loc
          | none => Json.null),
        ("offset", Lean.toJson value.offset),
        ("len", Lean.toJson value.len),
        ("cap", Lean.toJson value.cap)
      ]
  | .map value =>
      Json.mkObj [
        ("tag", Json.str "map"),
        ("base", match value.base with
          | some loc => locJson loc
          | none => Json.null)
      ]
  | .mapData entries =>
      Json.mkObj [
        ("tag", Json.str "mapData"),
        ("entries", Json.arr (entries.map (fun (key, value) =>
          Json.mkObj [
            ("key", goValueJson key),
            ("value", goValueJson value)
          ])))
      ]

private def runJson : GoLean.GoCore.Result → Json
  | { values } =>
      Json.mkObj [
        ("schema", Json.str observationSchema),
        ("status", Json.str "ok"),
        ("values", Json.arr (values.map goValueJson))
      ]

private def errorJson (error : GoError) : Json :=
  Json.mkObj [
    ("schema", Json.str observationSchema),
    ("status", Json.str error.status),
    ("message", Json.str error.message)
  ]

private def cliErrorJson (message : String) : Json :=
  Json.mkObj [
    ("schema", Json.str observationSchema),
    ("status", Json.str "error"),
    ("message", Json.str message)
  ]

private partial def decodeLocObservation (path : String) (json : Json) : Except String Unit := do
  let obj ← StrictJson.obj path json
  let tag ← StrictJson.string s!"{path}.tag" (← StrictJson.field path obj "tag")
  match tag with
  | "addr" =>
      StrictJson.requireExactKeys path obj ["id", "tag"]
      let _ ← StrictJson.nat s!"{path}.id" (← StrictJson.field path obj "id")
      pure ()
  | "fieldAddr" =>
      StrictJson.requireExactKeys path obj ["base", "fieldName", "tag", "typeName"]
      decodeLocObservation s!"{path}.base" (← StrictJson.field path obj "base")
      let _ ← StrictJson.string s!"{path}.typeName" (← StrictJson.field path obj "typeName")
      let _ ← StrictJson.string s!"{path}.fieldName" (← StrictJson.field path obj "fieldName")
      pure ()
  | "indexAddr" =>
      StrictJson.requireExactKeys path obj ["base", "index", "tag"]
      decodeLocObservation s!"{path}.base" (← StrictJson.field path obj "base")
      let _ ← StrictJson.int s!"{path}.index" (← StrictJson.field path obj "index")
      pure ()
  | other =>
      throw s!"{path}.tag: unknown location tag {repr other}"

private def decodeOptionalLoc (path : String) (json : Json) : Except String Unit :=
  match json with
  | .null => pure ()
  | other => decodeLocObservation path other

private partial def decodeGoValueObservation (path : String) (json : Json) : Except String Unit := do
  let obj ← StrictJson.obj path json
  let tag ← StrictJson.string s!"{path}.tag" (← StrictJson.field path obj "tag")
  match tag with
  | "unit" =>
      StrictJson.requireExactKeys path obj ["tag"]
  | "bool" =>
      StrictJson.requireExactKeys path obj ["tag", "value"]
      let _ ← StrictJson.bool s!"{path}.value" (← StrictJson.field path obj "value")
      pure ()
  | "int" =>
      StrictJson.requireExactKeys path obj ["tag", "value"]
      let _ ← StrictJson.int s!"{path}.value" (← StrictJson.field path obj "value")
      pure ()
  | "string" =>
      StrictJson.requireExactKeys path obj ["bytes", "tag"]
      let bytes ← StrictJson.array s!"{path}.bytes" (← StrictJson.field path obj "bytes")
      let _ ← StrictJson.mapArrayIdx bytes (fun i byte => do
        let _ ← StrictJson.nat s!"{path}.bytes[{i}]" byte
        pure ())
      pure ()
  | "nil" =>
      StrictJson.requireExactKeys path obj ["tag"]
  | "interface" =>
      StrictJson.requireExactKeys path obj ["dynamic", "tag", "value"]
      let _ ← StrictJson.string s!"{path}.dynamic" (← StrictJson.field path obj "dynamic")
      decodeGoValueObservation s!"{path}.value" (← StrictJson.field path obj "value")
  | "addr" | "fieldAddr" | "indexAddr" =>
      decodeLocObservation path json
  | "struct" =>
      StrictJson.requireExactKeys path obj ["fields", "tag", "typeName"]
      let _ ← StrictJson.string s!"{path}.typeName" (← StrictJson.field path obj "typeName")
      let fields ← StrictJson.array s!"{path}.fields" (← StrictJson.field path obj "fields")
      let _ ← StrictJson.mapArrayIdx fields (fun i fieldJson => do
        let fieldObj ← StrictJson.obj s!"{path}.fields[{i}]" fieldJson
        StrictJson.requireExactKeys s!"{path}.fields[{i}]" fieldObj ["name", "value"]
        let _ ← StrictJson.string s!"{path}.fields[{i}].name" (← StrictJson.field s!"{path}.fields[{i}]" fieldObj "name")
        decodeGoValueObservation s!"{path}.fields[{i}].value" (← StrictJson.field s!"{path}.fields[{i}]" fieldObj "value"))
      pure ()
  | "array" =>
      StrictJson.requireExactKeys path obj ["tag", "values"]
      let values ← StrictJson.array s!"{path}.values" (← StrictJson.field path obj "values")
      let _ ← StrictJson.mapArrayIdx values (fun i value => do
        decodeGoValueObservation s!"{path}.values[{i}]" value)
      pure ()
  | "slice" =>
      StrictJson.requireExactKeys path obj ["base", "cap", "len", "offset", "tag"]
      decodeOptionalLoc s!"{path}.base" (← StrictJson.field path obj "base")
      let _ ← StrictJson.nat s!"{path}.offset" (← StrictJson.field path obj "offset")
      let _ ← StrictJson.nat s!"{path}.len" (← StrictJson.field path obj "len")
      let _ ← StrictJson.nat s!"{path}.cap" (← StrictJson.field path obj "cap")
      pure ()
  | "map" =>
      StrictJson.requireExactKeys path obj ["base", "tag"]
      decodeOptionalLoc s!"{path}.base" (← StrictJson.field path obj "base")
  | "mapData" =>
      StrictJson.requireExactKeys path obj ["entries", "tag"]
      let entries ← StrictJson.array s!"{path}.entries" (← StrictJson.field path obj "entries")
      let _ ← StrictJson.mapArrayIdx entries (fun i entryJson => do
        let entryObj ← StrictJson.obj s!"{path}.entries[{i}]" entryJson
        StrictJson.requireExactKeys s!"{path}.entries[{i}]" entryObj ["key", "value"]
        decodeGoValueObservation s!"{path}.entries[{i}].key" (← StrictJson.field s!"{path}.entries[{i}]" entryObj "key")
        decodeGoValueObservation s!"{path}.entries[{i}].value" (← StrictJson.field s!"{path}.entries[{i}]" entryObj "value"))
      pure ()
  | other =>
      throw s!"{path}.tag: unknown Go observation value tag {repr other}"

private def decodeObservation (path raw : String) : Except String Json := do
  let json ← Json.parse raw
  let obj ← StrictJson.obj path json
  let schema ← StrictJson.string s!"{path}.schema" (← StrictJson.field path obj "schema")
  if schema != observationSchema then
    throw s!"{path}.schema: expected {repr observationSchema}, got {repr schema}"
  let status ← StrictJson.string s!"{path}.status" (← StrictJson.field path obj "status")
  match status with
  | "ok" =>
      StrictJson.requireExactKeys path obj ["schema", "status", "values"]
      let values ← StrictJson.array s!"{path}.values" (← StrictJson.field path obj "values")
      let _ ← StrictJson.mapArrayIdx values (fun i value => do
        decodeGoValueObservation s!"{path}.values[{i}]" value)
      return json
  | "panic" | "unsupported" | "stuck" | "error" | "fuel-out" =>
      StrictJson.requireExactKeys path obj ["message", "schema", "status"]
      let _ ← StrictJson.string s!"{path}.message" (← StrictJson.field path obj "message")
      return json
  | other =>
      throw s!"{path}.status: unknown observation status {repr other}"

private def runObservationEq (args : List String) : IO UInt32 := do
  match parseObservationEqArgs args none none with
  | .error err =>
      IO.eprintln err
      return 2
  | .ok (leftRaw, rightRaw) =>
      match decodeObservation "left" leftRaw, decodeObservation "right" rightRaw with
      | .error err, _ =>
          IO.eprintln err
          return 2
      | _, .error err =>
          IO.eprintln err
          return 2
      | .ok left, .ok right =>
          if left == right then
            return 0
          else
            IO.eprintln s!"left:  {left.compress}"
            IO.eprintln s!"right: {right.compress}"
            return 1

private def runNativeJsonRun (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  match parseRunArgs args {} with
  | .error err =>
      IO.eprintln err
      return 2
  | .ok cfg =>
      match cfg.input, cfg.functionName with
      | some input, some functionName =>
          let input := absoluteFrom cwd input
          let contents ← IO.FS.readFile input
          match Lean.Json.parse contents with
          | .error err =>
              IO.println (cliErrorJson s!"{input}: JSON parse error: {err}").compress
              return 1
          | .ok json =>
              match GoLean.NativeToIR.decodeProgram json with
              | .error err =>
                  IO.println (cliErrorJson s!"{input}: {err}").compress
                  return 1
              | .ok program =>
                  -- Reshape S3 flip (2026-07-23): the machine interpreter
                  -- (iterated stepFn) is the executable; the big-step
                  -- interpreter is deleted at S4.
                  match GoLean.GoCore.Machine.runNamedFunctionIntsM cfg.fuel program functionName cfg.args cfg.choices with
                  | .ok result =>
                      IO.println (runJson result).compress
                      return 0
                  | .error err =>
                      IO.println (errorJson err).compress
                      return 1
      | _, _ =>
          IO.eprintln s!"provide --input <file> and --function <name>\n{usage}"
          return 2

/-! ## `coverage-observations` — the membership lane's machine-side enumerator

CLI layer ONLY (arc slice 3, `docs/2026-08-04_membership-lane-design.md`):
the semantic core is reused verbatim (`stepFn` iterated exactly as
`runConfig` iterates it; the entry wiring mirrors
`runFunctionWithContextM`). For a case whose observable genuinely depends
on the `Choices` stream, this enumerates the DISTINCT observations over
all stream prefixes on alphabet `[0, B)` to consumption depth `D`,
deduplicating canonical observation JSON.

Coverage argument: `Choices.consume` takes each pick modulo the site's
bound, so `[0, B)` at every position covers every behavior PROVIDED
`B ≥` every site's bound reached in the case. The enumerator cannot read
a site's bound, so `B` is per-case metadata certified by the case author;
the ALIAS GUARD cross-checks it cheaply (probe picks `≥ B`: if the
enumeration is complete, EVERY stream's observation is in the set, so a
probe landing outside the set proves `B` too small — fail closed). Depth
`D`, the observation cap `N`, and the work cap all fail LOUD, never
truncate silently. -/

structure EnumArgs where
  input : Option FilePath := none
  functionName : Option String := none
  args : Array Int := #[]
  fuel : Nat := 10000000
  /-- `B`: the pick alphabet is `[0, B)` at every consumption site. Must be
  `≥` every site's bound in the case (per-case metadata; default 16 covers
  append's 8 and small maps). -/
  maxWidth : Nat := 16
  /-- `D`: maximum consumption sites per run. A run consuming more fails
  loud — it is never silently truncated to a prefix. -/
  maxSites : Nat := 8
  /-- `N`: cap on the DISTINCT observation set. Exceeding it fails loud —
  such a case is too wide for enumeration (needs a per-case predicate,
  out of scope per the design note). -/
  cap : Nat := 64
  /-- Work cap on total machine runs (exploration + alias probes): the
  `B^D` blowup guard. Exceeding it fails loud. -/
  workCap : Nat := 200000
  deriving Repr

private def parseEnumArgs : List String → EnumArgs → Except String EnumArgs
  | [], cfg => .ok cfg
  | "--input" :: path :: rest, cfg =>
      parseEnumArgs rest { cfg with input := some (FilePath.mk path) }
  | "--function" :: name :: rest, cfg =>
      parseEnumArgs rest { cfg with functionName := some name }
  | "--arg-int" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with args := cfg.args.push (← parseJsonInt "--arg-int" value) }
  | "--fuel" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with fuel := (← parseJsonNat "--fuel" value) }
  | "--max-width" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with maxWidth := (← parseJsonNat "--max-width" value) }
  | "--max-sites" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with maxSites := (← parseJsonNat "--max-sites" value) }
  | "--cap" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with cap := (← parseJsonNat "--cap" value) }
  | "--work-cap" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with workCap := (← parseJsonNat "--work-cap" value) }
  | flag :: _, _ => .error s!"unknown or incomplete option: {flag}\n{usage}"

private def renderGoError (err : GoError) : String :=
  s!"{err.status}: {err.message}"

/-- Mirror of `runFunctionWithContextM`'s entry wiring, split out so every
enumeration run restarts from the SAME initial state and configuration
(all values are pure). -/
private def enumSetup (program : GoCore.Program) (name : String)
    (args : Array GoValue) :
    Except GoError (GoCore.ExecState × GoCore.Machine.Config × List Loc) := do
  let func ←
    match GoCore.findFunctionIn? program.funcs ⟨name⟩ with
    | some func => pure func
    | none => throw (.stuck s!"GoCore function not found: {name}")
  let state : GoCore.ExecState :=
    { types := program.typeDefs.toList, functions := program.funcs
      methods := program.methods }
  if func.args.size != args.size then
    throw (.stuck s!"expected {func.args.size} argument(s), got {args.size}")
  let (env, s₁) ← GoCore.Machine.bindParams [] state func.args.toList args.toList
  let (frameEnv, s₂) ← GoCore.Machine.allocDecls env s₁ func.results.toList
  let resultLocs ← GoCore.Machine.pinResultLocs frameEnv func.results.toList
  let c₀ : GoCore.Machine.Config := .exec func.body frameEnv (.frame [] [] [] .stop)
  return (s₂, c₀, resultLocs)

/-- One machine run to a terminal configuration: the observation JSON plus
the LEFTOVER choice stream. `Choices.consume` pops exactly one element
while the stream is non-empty (exhaustion consumes nothing and yields the
default 0), so `provided − |leftover|` is the exact number of consumption
sites reached whenever the leftover is non-empty — the enumerator's
consumption meter. Terminal handling mirrors `runConfig` exactly, except
the panic terminal KEEPS the stream (its observation is a member too)
instead of throwing it away; all other `GoError`s (stuck, unsupported,
internal, fuel-out) propagate and the enumeration fails loud on them. -/
private def enumRun (resultLocs : List Loc) :
    Nat → GoCore.ExecState → GoCore.Machine.Config → GoCore.Choices →
    Except GoError (Json × GoCore.Choices)
  | _, σ, .next .stop, choices =>
      return (runJson { values := (← GoCore.Machine.loadMany σ resultLocs).toArray }, choices)
  | _, _, .panicked msg, choices => return (errorJson (.panic msg), choices)
  | 0, _, _, _ => throw .fuelOut
  | fuel + 1, σ, c, choices => do
      let (c', σ', choices') ← GoCore.Machine.stepFn σ c choices
      enumRun resultLocs fuel σ' c' choices'

private structure EnumOutcome where
  /-- Distinct observations (canonical `Json`, deduplicated by structural
  equality — the same equality `observation-eq` decides). -/
  observations : Array Json := #[]
  /-- Complete pick assignments (one per explored leaf; exact consumption
  = length). The alias guard probes these. -/
  leaves : Array (Array Nat) := #[]
  runs : Nat := 0

/-- Depth-first exploration of the choice tree over prefixes on `[0, B)`.
Invariant on every frontier entry `p`: the run's first `|p|` consumption
sites exist and consume exactly `p` (established by the parent's probe).
Each pop runs the machine once with stream `p ++ [0]` — the probe pick:
a leftover of exactly one element proves the run finished consuming `|p|`
sites (record the observation; `p` is a complete assignment), an empty
leftover proves a site exists at depth `|p|` (extend with every pick in
`[0, B)`). Fuel is the work cap: decrements once per run, fails loud at
zero with the frontier non-empty. -/
private def exploreLoop (resultLocs : List Loc) (runFuel : Nat)
    (σ₀ : GoCore.ExecState) (c₀ : GoCore.Machine.Config)
    (width sites cap : Nat) :
    Nat → List (Array Nat) → EnumOutcome → Except String EnumOutcome
  | _, [], out => .ok out
  | 0, _ :: _, out =>
      .error s!"work cap exceeded after {out.runs} run(s) with prefixes still unexplored — raise --work-cap or narrow the case"
  | work + 1, p :: rest, out => do
      let stream := p.toList ++ [0]
      match enumRun resultLocs runFuel σ₀ c₀ stream with
      | .error err =>
          .error s!"machine run failed under pick prefix {p.toList} — cannot certify the observation set: {renderGoError err}"
      | .ok (obs, leftover) =>
          let out := { out with runs := out.runs + 1 }
          if leftover.length ≥ 1 then
            -- Probe untouched: `p` is a complete assignment.
            let observations :=
              if out.observations.contains obs then out.observations
              else out.observations.push obs
            if observations.size > cap then
              .error s!"observation cap N={cap} exceeded — the case is too wide for enumeration (design note: needs a per-case predicate)"
            else
              exploreLoop resultLocs runFuel σ₀ c₀ width sites cap work rest
                { out with observations, leaves := out.leaves.push p }
          else
            -- Probe consumed: a site exists at depth |p|.
            if p.size + 1 > sites then
              .error s!"run consumes more than --max-sites {sites} choice site(s) — raise the case's sites bound (never truncated silently)"
            else
              let children := (List.range width).map (fun b => p.push b)
              exploreLoop resultLocs runFuel σ₀ c₀ width sites cap work
                (children ++ rest) out

/-- The alias guard: for every explored complete assignment and every pick
position, re-run with that pick bumped by `B`. If the enumeration is
complete (`B ≥` every site's bound), every stream's observation — probe
streams included — lies in the enumerated set; an observation outside it
proves `B` is smaller than some site's bound, so coverage is NOT
certified and the enumeration fails closed. (The converse does not hold —
an aliased bound can escape one probe — so this is the design note's
cheap cross-check on the per-case `B` metadata, not a proof.) -/
private def aliasProbeLoop (resultLocs : List Loc) (runFuel : Nat)
    (σ₀ : GoCore.ExecState) (c₀ : GoCore.Machine.Config) (width : Nat)
    (observations : Array Json) :
    Nat → List (List Nat) → Nat → Except String Nat
  | _, [], probes => .ok probes
  | 0, _ :: _, probes =>
      .error s!"work cap exceeded during alias probes (after {probes} probe(s)) — raise --work-cap"
  | work + 1, stream :: rest, probes => do
      match enumRun resultLocs runFuel σ₀ c₀ stream with
      | .error err =>
          .error s!"alias-guard probe {stream} failed — cannot certify coverage at width B={width}: {renderGoError err}"
      | .ok (obs, _) =>
          if observations.contains obs then
            aliasProbeLoop resultLocs runFuel σ₀ c₀ width observations work rest (probes + 1)
          else
            .error s!"alias guard: probe pick ≥ B (stream {stream}) produced an observation OUTSIDE the enumerated set — width B={width} is smaller than some consumption site's bound; raise the case's width metadata. Probe observation: {obs.compress}"

private def runCoverageObservations (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  match parseEnumArgs args {} with
  | .error err =>
      IO.eprintln err
      return 2
  | .ok cfg =>
      match cfg.input, cfg.functionName with
      | some input, some functionName =>
          if cfg.maxWidth < 1 then
            IO.eprintln "coverage-observations: --max-width must be >= 1 (an empty pick alphabet explores nothing)"
            return 2
          let input := absoluteFrom cwd input
          let contents ← IO.FS.readFile input
          match Lean.Json.parse contents with
          | .error err =>
              IO.eprintln s!"coverage-observations: {input}: JSON parse error: {err}"
              return 1
          | .ok json =>
              match GoLean.NativeToIR.decodeProgram json with
              | .error err =>
                  IO.eprintln s!"coverage-observations: {input}: {err}"
                  return 1
              | .ok program =>
                  match enumSetup program functionName (cfg.args.map GoValue.int) with
                  | .error err =>
                      IO.eprintln s!"coverage-observations: setup failed: {renderGoError err}"
                      return 1
                  | .ok (σ₀, c₀, resultLocs) =>
                      match exploreLoop resultLocs cfg.fuel σ₀ c₀
                          cfg.maxWidth cfg.maxSites cfg.cap (cfg.workCap + 1) [#[]] {} with
                      | .error err =>
                          IO.eprintln s!"coverage-observations: {err}"
                          return 1
                      | .ok out =>
                          let probeStreams : List (List Nat) :=
                            out.leaves.toList.flatMap (fun p =>
                              (List.range p.size).map (fun i =>
                                (p.set! i (p[i]! + cfg.maxWidth)).toList))
                          let workLeft := cfg.workCap + 1 - out.runs
                          match aliasProbeLoop resultLocs cfg.fuel σ₀ c₀
                              cfg.maxWidth out.observations workLeft probeStreams 0 with
                          | .error err =>
                              IO.eprintln s!"coverage-observations: {err}"
                              return 1
                          | .ok probes =>
                              let lines :=
                                (out.observations.map (·.compress)).qsort (· < ·)
                              for line in lines do
                                IO.println line
                              IO.eprintln s!"coverage-observations: observations={out.observations.size} runs={out.runs} probes={probes} width={cfg.maxWidth} sites={cfg.maxSites} leaves={out.leaves.size}"
                              return 0
      | _, _ =>
          IO.eprintln s!"provide --input <file> and --function <name>\n{usage}"
          return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] | ["-h"] =>
      IO.println usage
      return 0
  | "native-json-run" :: rest => runNativeJsonRun rest
  | "observation-eq" :: rest => runObservationEq rest
  | "coverage-observations" :: rest => runCoverageObservations rest
  | [] =>
      IO.println usage
      return 0
  | cmd :: _ =>
      IO.eprintln s!"unknown command: {cmd}\n{usage}"
      return 2

end GoLean.CLI
