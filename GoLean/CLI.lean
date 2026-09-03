import GoLean.GoCore
import GoLean.EnumDedup
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
  "  golean coverage-observations --input <file> --function <name> [--arg-int <n> ...] [--fuel <n>] [--engine dedup]\n" ++
  "      [--max-width <B>] [--max-sites <D>] [--cap <N>] [--work-cap <W>] [--expect-status <ok|panic|ok,panic|race>]
      [--allow-nonterm <per-branch-fuel>] [--backedge <full|k>]\n"

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

-- The OBSERVATION channel renders type names the way Go's
-- `reflect.Type.Name()` does — WITHOUT the leading package qualifier —
-- while `TypeId` keys stay package-qualified for identity (interfaces
-- campaign, 2026-07-30). The renderer is `TypeId.unqualified`
-- (`GoCore/Value.lean`), THE one copy of the stripping logic: a private
-- duplicate here predated the generics slice's leading-strip fix and
-- kept truncating mangled instantiation keys after Value.lean was fixed
-- (BUG-013, pinned by generics/instantiated-type-assert/name — the
-- uncoupled-copy drift class).

private def locJson : Loc → Json
  | .base addr => Json.mkObj [("tag", Json.str "addr"), ("id", Lean.toJson addr.id)]
  | .field base typeId fieldName =>
      Json.mkObj [
        ("tag", Json.str "fieldAddr"),
        ("base", locJson base),
        ("typeName", Json.str typeId.unqualified),
        ("fieldName", Json.str fieldName)
      ]
  | .index base index =>
      Json.mkObj [
        ("tag", Json.str "indexAddr"),
        ("base", locJson base),
        ("index", Lean.toJson index)
      ]

/-- Canonicalize a float observation's bit pattern (floats design note
§5): NaN payloads/signs are platform- and path-dependent in real Go and
unobservable in the language proper, so BOTH encoders (this one and the
Go harness) map any NaN to the canonical quiet NaN before emission.
Signed zero is NOT canonicalized (Go distinguishes it via `1/z`). If
`math.Float64bits` ever enters the supported surface, payload
propagation becomes observable and this decision must be revisited
(then: fail closed on NaN-payload-observing programs). -/
private def canonFloatObsBits (kind : GoCore.FloatKind) (bits : Nat) : Nat :=
  match kind with
  | .float64 =>
      if (bits >>> 52) &&& 0x7FF == 0x7FF && bits &&& ((1 <<< 52) - 1) != 0 then
        GoCore.FloatBits.nan64
      else bits
  | .float32 =>
      if (bits >>> 23) &&& 0xFF == 0xFF && bits &&& ((1 <<< 23) - 1) != 0 then
        GoCore.FloatBits.nan32
      else bits

private partial def goValueJson : GoValue → Json
  | .unit => Json.mkObj [("tag", Json.str "unit")]
  | .bool value => Json.mkObj [("tag", Json.str "bool"), ("value", Lean.toJson value)]
  -- Kind-carrying integer observation (grossmith hunt F15, spec-parity
  -- s1): the kind (and with it the width/signedness) is part of the
  -- observation, symmetrically with the Go harness's reflect kind — a
  -- kind-defaulting bug landing on the RIGHT numeric value (the
  -- BUG-042/043 family) was invisible to the value-only shape. The
  -- value carries no defined-type identity (an `IntKind` only), so none
  -- is emitted; defined-type identity over ints stays observable only
  -- through interface boxes (`dynamic`), on both sides alike. An
  -- `.unbounded` kind renders its name and FAILS the decoder below —
  -- no wire program can produce one at runtime (fail closed, never a
  -- silent default).
  | .int value kind =>
      Json.mkObj [
        ("tag", Json.str "int"),
        ("kind", Json.str kind.name),
        ("value", Lean.toJson value)
      ]
  -- Bit patterns, never decimal strings (note §5): equality is bit-exact
  -- modulo the NaN canonicalization above; Go's shortest-representation
  -- printing stays outside the trust surface.
  | .float bits kind =>
      Json.mkObj [
        ("tag", Json.str "float"),
        ("kind", Json.str kind.name),
        ("bits", Lean.toJson (canonFloatObsBits kind bits))
      ]
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
      -- `reflect.Type.Name()` returns "" for any NON-DEFINED type
      -- (reflect/type.go); the canonical anonymous empty struct is the
      -- one unnamed struct TypeId the wire mints (`emptyStructName`,
      -- tools/nativefrontend/wire.go), so it renders as "" — the
      -- internal key "struct{}" leaked verbatim before (BUG-019,
      -- arc-final audit F7, 2026-08-06). Named empty structs are
      -- defined types and keep their names.
      Json.mkObj [
        ("tag", Json.str "struct"),
        ("typeName", Json.str (if typeId.key == "struct{}" then "" else typeId.unqualified)),
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
  -- Entry-identity stamps (B1) are runtime-internal identity and are
  -- projected AWAY here: the observation shape is the entry list as
  -- before (no wire change).
  | .mapData entries _ =>
      Json.mkObj [
        ("tag", Json.str "mapData"),
        ("entries", Json.arr (entries.map (fun (_, key, value) =>
          Json.mkObj [
            ("key", goValueJson key),
            ("value", goValueJson value)
          ])))
      ]
  -- Channel observations mirror the map shape (reference identity). The
  -- Go harness FAILS CLOSED on a channel-typed result (reflect.Chan is
  -- an unsupported observation kind there), so a case whose OUTPUT is a
  -- raw channel is outside the differential's comparable surface — this
  -- arm keeps the machine side total and diagnosable.
  | .chan value =>
      Json.mkObj [
        ("tag", Json.str "chan"),
        ("base", match value.base with
          | some loc => locJson loc
          | none => Json.null)
      ]
  | .chanData buf capacity closed =>
      Json.mkObj [
        ("tag", Json.str "chanData"),
        ("buf", Json.arr (buf.map goValueJson)),
        ("cap", Lean.toJson capacity),
        ("closed", Lean.toJson closed)
      ]
  -- Sync primitive state (spec-parity slice 2): a subject RETURNING a
  -- sync struct is copy-class misuse with no Go-side counterpart shape
  -- (the harness reflects it as an opaque struct) — the tag is emitted
  -- so the mismatch is a VISIBLE red, never a false pass. No corpus
  -- case observes one; the machine-internal repr is diagnostic only.
  | .syncData p =>
      Json.mkObj [("tag", Json.str "syncData"), ("state", Json.str s!"{repr p}")]

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
      -- Kind-carrying shape (F15, the float arm's discipline): exact
      -- keys, kind restricted to the ten concrete integer kinds, value
      -- range-checked per the kind's width/signedness — fail closed on
      -- anything else. `uintptr` is deliberately ABSENT: the frontend
      -- maps uintptr to uint64 (`intKindOfName`), so the machine could
      -- never emit it and a Go-side uintptr observation must refuse
      -- here rather than alias into uint64.
      StrictJson.requireExactKeys path obj ["kind", "tag", "value"]
      let kind ← StrictJson.string s!"{path}.kind" (← StrictJson.field path obj "kind")
      let value ← StrictJson.int s!"{path}.value" (← StrictJson.field path obj "value")
      let (bits, signed) ← match kind with
        | "int" => pure (64, true)
        | "uint" => pure (64, false)
        | "int8" => pure (8, true)
        | "uint8" => pure (8, false)
        | "int16" => pure (16, true)
        | "uint16" => pure (16, false)
        | "int32" => pure (32, true)
        | "uint32" => pure (32, false)
        | "int64" => pure (64, true)
        | "uint64" => pure (64, false)
        | other => throw s!"{path}.kind: unknown integer kind {repr other}"
      let inRange :=
        if signed then
          -(2 ^ (bits - 1) : Int) ≤ value && value < 2 ^ (bits - 1)
        else
          0 ≤ value && value < (2 ^ bits : Int)
      if !inRange then
        throw s!"{path}.value: {value} out of range for {kind}"
      pure ()
  | "float" =>
      -- Bit-pattern observation (floats note §5/§7): exact keys, kind
      -- restricted to the two float kinds, bits range-checked per kind —
      -- fail closed on anything else.
      StrictJson.requireExactKeys path obj ["bits", "kind", "tag"]
      let kind ← StrictJson.string s!"{path}.kind" (← StrictJson.field path obj "kind")
      let bits ← StrictJson.nat s!"{path}.bits" (← StrictJson.field path obj "bits")
      let width ← match kind with
        | "float64" => pure 64
        | "float32" => pure 32
        | other => throw s!"{path}.kind: unknown float kind {repr other}"
      if bits ≥ 2 ^ width then
        throw s!"{path}.bits: {bits} out of range for {kind}"
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

/-- Non-`private` so the eval tests can pin the fail-closed decode
discipline for the kind-carrying integer shape (F15) — the enumSetup
precedent. -/
def decodeObservation (path raw : String) : Except String Json := do
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
  -- "fatal" (spec-parity slice 2): gc's unrecoverable runtime-throw
  -- class (`GoError.fatal` — the sync misuse fatals), message-carrying
  -- like deadlock/race.
  | "panic" | "unsupported" | "stuck" | "error" | "fuel-out" | "deadlock" | "race"
  | "fatal" =>
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
                  -- interpreter is deleted at S4. Since the init slice the
                  -- entry is the whole-PROGRAM driver: seed globals, run
                  -- $pkginit, then the subject. Since the channels arc
                  -- slice 2 the subject phase runs on the THREAD POOL
                  -- (`runProgramPoolM`) — identical to the sequential
                  -- driver on programs that never spawn
                  -- (`execProg_single_eq_execStmt` + the full-corpus
                  -- bit-identity check), and the only driver on which
                  -- `go` statements run.
                  match GoLean.GoCore.Machine.runProgramPoolIntsM cfg.fuel program functionName cfg.args cfg.choices with
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
what is REUSED from the semantic core is `stepFn` — every machine step is
the machine's own — plus, since the init slice, `seedGlobals` (globals
seeding is stream-independent setup shared with `runProgramM`). What is
COPIED (not shared) is the driver layer: `enumSetup`/`enumRunProgram`
hand-mirror `runProgramM`'s wiring (subject lookup, `$pkginit` shape
check, per-stream init-then-subject composition — init consumes choices,
so it runs per enumerated stream) and `enumPoolRun`/`enumInitRun`
hand-mirror `execProgLoop`'s / `runConfig`'s terminal handling (audit
F5/F7, 2026-08-05; the subject phase moved to the POOL mirror at the
channels arc's slice 4, reusing `stepMulti`/`raceUpdate` verbatim so
the scheduler/waiter/select sites and the detector are the machine's
own).
Rationale updated at the arc-final audit (F16, 2026-08-06): the original
clause "a shared helper would touch GoCore, which stays bit-identical"
was the MEMBERSHIP SLICE's constraint (that slice touched zero GoCore
files) and is false as a standing fact — later slices changed GoCore
freely. The standing rationale is a POLICY: the membership lane
deliberately adds no driver helper to GoCore (the lane is CLI-layer
tooling; GoCore carries only what the semantics needs), and the copies
are pinned instead. The copies
are PINNED two ways: the driver-agreement
eval tests in `Tests/GoCoreEval.lean` (the `native-json-run` engine's
observation must be a member of the enumerated set, per consumption-site
class), and the harness's per-case coupling check in
`scripts/diff-coverage` (`native-json-run --choices <s>` ∈ enumerated
set for every membership case, several streams, every differential run).
Drift between the copies and the originals breaks those pins loudly.

For a case whose observable genuinely depends on the `Choices` stream,
this enumerates the DISTINCT observations over the whole choice tree,
deduplicating canonical observation JSON.

Coverage argument — the certification claim, stated honestly.
[SUPERSEDED at the channels arc's slice 4 (S4 audit correction — the
paragraph here described the retired uniform-width engine: alphabet
`[0, B)` at every position, "the enumerator CANNOT read a site's
bound", the author-asserted width PRECONDITION, and the `+B/+2B+1/+4B+3`
offset ladder; all four are false of the shipped engine). The current
claim:] `Choices.consumeAt` (the tagged consumption combinator — W3.2
stage A; each site names its `ChoiceSite` census row) takes each pick
modulo the site's bound, and
the stepwise engine below explores exactly `[0, bound)` at each site,
with every bound COMPUTED by the consumption accountant
(`stepNeeds`/`stepNeedsSeq`) from the machine's own analysis functions
— the design note's once-deferred "mechanical bound certification",
taken at slice 4 without touching GoCore. The per-case `width` is a
MECHANICALLY-CHECKED CAP (a computed bound above it fails loud —
F2a's discipline made exact), no longer the precondition the
certification rests on. The certification's residual trust is the
ACCOUNTANT itself (a hand-mirrored copy), guarded three ways: the
per-site alias ladder (raw picks `b`, `2b+1`, `4b+3` at each
discovered site's computed bound, replayed through the REAL semantics
— an under-counted bound's escaping residue refutes it, with the
recorded qualifier that the ladder replays an all-defaults suffix, so
a residue whose distinguishing behavior needs a later non-default
pick can still alias into the set); the TWO-SIDED sentinel drift
alarm on every step (S4 audit: over-supplied picks AND a missed
consumption site both fail loud — the sentinel-suffixed step must
return the sentinel exactly); and the external driver-agreement /
coupling pins above. Depth `D`, the observation cap `N`, and
the work cap all fail LOUD, never truncate silently.

THE ACCOUNTANT-EXHAUSTIVENESS INVENTORY (a standing LOCKSTEP
obligation, the Race.lean-inventory mold: a new `Choices.consumeAt`
call site in the semantic core MUST add its `ChoiceSite` constructor
and policy row (State.lean — the census as code, exhaustiveness-checked),
its `stepNeeds`/`stepNeedsSeq` arm, AND its row here; the sentinel
alarm is the executable check).
The semantic core's consume sites and their accountant arms:
1. `stepMulti`'s boundary scheduling pick (Multi.lean, the slot-menu
   length at a boundary with ≥ 2 menu entries — the L1 site, stage C's
   `postOp` site at an `.opDone` completion marker, and stage D's
   `backEdge` site at the loop re-entry shapes: same
   `Choices.consumeAtE c.boundarySite` call, menu from `schedSlots`,
   current-first at postOp/backEdge) → `stepNeeds`' boundary arm
   (which mirrors `schedSlots`, never bare `runnableIdxs`). The DFS
   additionally applies the per-site ENUMERATION mode at backEdge
   consults (stage D §5d: `--backedge full|k`, fail-loud when
   undeclared; capped occurrences counted and printed).
2. `arrivalPlan`'s L2 arrival pick (Multi.lean, `os.length` at a
   `.multi` analysis) → `stepNeeds`' `.multi` arm.
3. `stepThread`'s L4 waiter pick (Multi.lean, `cs.length` at a
   multi-candidate pairing) → `stepNeeds`' `.single`/`.multi`-pair
   arms (`cs.length` when > 1).
4. `stepFn`'s mapIterK pick-next (StepFn.lean, `remaining.size`) →
   the `.next (.mapIterK …)` arm of both accountants.
5. `applyStmtOp`'s appendSlice spill capacity (Machine.lean,
   `appendSpillWidth oldCap newLen`) → the `.stmtOpK (.appendSlice)`
   apply arm of both accountants (operand analysis mirrored).
6. `applySelect`'s L2 select pick (Machine.lean, `commits.length` at
   a `.picks` core outcome) → the `.selectOpsK` apply arm of both
   accountants (via the same `applySelectCore`).
Non-consuming by signature (no arm needed): `resumeThread`,
`spawnStep`, `commitClause`, `applyPairing`, the `.opDone` strip,
`raceUpdate` (stage B: it folds the step's emitted `StepEvent` and
takes NO stream at all — the old consumption replication is deleted),
and —
spec-parity slice 2 — `applySyncOp` and the sync wake path: the sync
registry entry adds NEW BOUNDARIES to `Config.atBoundary` (row 1's
L1 bound reuses the machine's `runnableIdxs`/`atBoundary` directly,
so the accountant tracks them with no new arm) but ZERO new consume
sites (the envelope statement at `applySyncOp`: acquisition order
among contenders is entirely L1 latitude).

Machine-side status discipline (audit F1; CORRECTED at the arc-final
audit F8, 2026-08-08): a member whose status is outside the case's
DECLARED STATUS SET fails the enumeration loudly — a machine that
panics under streams Go can never realize must fail the case, not bury
the panic in unexhibited metadata. The original claim ("a member whose
status differs is by construction a machine bug, not an envelope
point") was FALSE: gc itself realizes status-diverse envelopes — a
leaked goroutine with an observable effect legitimately spans
`ok` and `panic` (the D6 main-exit latitude, BUG-044's window) — so
`--expect-status` now takes a comma-separated SET (e.g. `ok,panic`),
and only membership outside the set is a machine bug. `race` stays a
singleton (lane d's every-path-refuses claim admits no value members). -/

structure EnumArgs where
  input : Option FilePath := none
  functionName : Option String := none
  args : Array Int := #[]
  fuel : Nat := 10000000
  /-- `B`: the mechanically-checked CAP on every consumption site's
  COMPUTED bound (slice 4 — the engine explores `[0, bound)` per site;
  a bound above `B` fails loud). Per-case metadata; default 16 covers
  small maps and small pools, but NOT the append spill since the F2
  envelope widening — its bound is `appendSpillWidth oldCap newLen`,
  at least 32; a case observing a spill must assert its width. -/
  maxWidth : Nat := 16
  /-- `D`: maximum consumption sites per run. A run consuming more fails
  loud — it is never silently truncated to a prefix. -/
  maxSites : Nat := 8
  /-- `N`: cap on the DISTINCT observation set. Exceeding it fails loud —
  such a case is too wide for enumeration (needs a per-case predicate,
  out of scope per the design note). -/
  cap : Nat := 64
  /-- Work cap on exploration MACHINE STEPS + alias-probe RUNS (the
  unit changed from whole runs at slice 4's stepwise engine — shared
  prefixes execute once): the blowup guard. Exceeding it fails loud
  (audit F8's discipline carried over). -/
  workCap : Nat := 200000
  /-- Expected observation status SET (comma-separated `ok`/`panic`, or
  the singleton `race` — lane d's full-strength claim: EVERY enumerated
  path refuses, so it combines with nothing): every enumerated member
  must carry a status IN the set, else the enumeration fails loud
  (audit F1; SET-valued since the arc-final audit F8 — gc realizes
  status-diverse envelopes via the main-exit window, BUG-044, so
  `ok,panic` is a legitimate declaration, and only a member OUTSIDE
  the declared set is a machine bug). `none` skips the check (bare
  CLI exploration). -/
  expectStatus : Option (List String) := none
  /-- `--allow-nonterm N` (stage D §5d): per-branch pool fuel N with
  fuel-exhausted branches counted as `nonterm`, never members. -/
  allowNonterm : Option Nat := none
  /-- `--backedge full` or `--backedge <k>` (stage D §5d): the backEdge
  per-site enumeration mode; absent = a bound ≥ 2 backEdge consult
  fails loud. -/
  backedgeMode : Option (Option Nat) := none
  /-- `--engine dedup` (POR slice, design note 2026-08-21): certify via
  the state-graph dedup engine + the VERIFIED certificate checker
  (`checkCert_slowObs`) instead of the DFS. The claim standard rises:
  the printed set provably equals `SlowObs` (the ∃-fuel ∃-stream image
  of `execProgLoop`); the accountant/sentinel/alias-ladder heuristics
  do not apply on this path. Refused shapes (a `$pkginit` phase, L2
  `.multi` arrivals, consuming selects, mapIter, append spills) fail
  loud — such a row stays on the DFS. -/
  engine : Option String := none
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
  | "--allow-nonterm" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with allowNonterm := some (← parseJsonNat "--allow-nonterm" value) }
  | "--backedge" :: value :: rest, cfg => do
      if value == "full" then
        parseEnumArgs rest { cfg with backedgeMode := some none }
      else
        parseEnumArgs rest { cfg with backedgeMode := some (some (← parseJsonNat "--backedge" value)) }
  | "--engine" :: value :: rest, cfg =>
      if value == "dedup" then
        parseEnumArgs rest { cfg with engine := some value }
      else
        .error s!"unknown --engine (only dedup): {value}\n{usage}"
  | "--expect-status" :: value :: rest, cfg =>
      let parts := (value.splitOn ",").filter (· ≠ "")
      if parts.isEmpty then
        .error s!"--expect-status needs at least one status, got {value}\n{usage}"
      else if !parts.all (fun p => p == "ok" || p == "panic" || p == "race") then
        .error s!"--expect-status entries must be ok, panic, or race, got {value}\n{usage}"
      else if parts.contains "race" && parts.length > 1 then
        .error s!"--expect-status race combines with nothing (lane d claims EVERY path refuses), got {value}\n{usage}"
      else if parts.eraseDups.length != parts.length then
        .error s!"--expect-status has duplicate entries: {value}\n{usage}"
      else
        parseEnumArgs rest { cfg with expectStatus := some parts }
  | flag :: _, _ => .error s!"unknown or incomplete option: {flag}\n{usage}"

private def renderGoError (err : GoError) : String :=
  s!"{err.status}: {err.message}"

/-- The per-run-invariant half of the enumeration driver: subject lookup,
arity check, global seeding, and the `$pkginit` lookup/shape check — a
mirror of `runProgramM`'s pre-stream wiring (the seeding itself is the
SHARED `GoCore.Machine.seedGlobals`, which is stream-independent; the
stream-consuming phases live in `enumRunProgram`, run per stream).
Non-`private` so the driver-agreement eval tests can pin the copy
against the original (audit F5). -/
structure EnumProgram where
  /-- Globals-seeded initial state (pre-`$pkginit`). -/
  σ₀ : GoCore.ExecState
  /-- The `$pkginit` body, when the program has one — run PER STREAM
  (its choice consumption is part of the run; init slice,
  `docs/2026-08-05_init-design.md`). -/
  initBody? : Option GoCore.Stmt
  func : GoCore.Func
  args : Array GoValue

def enumSetup (program : GoCore.Program) (name : String)
    (args : Array GoValue) : Except GoError EnumProgram := do
  -- Pre-init step ORDER (find → arity → seed → init-shape) is shared
  -- verbatim with `runProgramM` (audit response 2026-08-05, C6:
  -- divergent orders gave divergent fail-closed errors on the
  -- arity+init-failure intersection; pinned by the driver-agreement
  -- eval test on the wrong-arity shape).
  let func ←
    match GoCore.findFunctionIn? program.funcs ⟨name⟩ with
    | some func => pure func
    | none => throw (.stuck s!"GoCore function not found: {name}")
  if func.args.size != args.size then
    throw (.stuck s!"expected {func.args.size} argument(s), got {args.size}")
  let state : GoCore.ExecState :=
    { types := program.typeDefs.toList, functions := program.funcs
      methods := program.methods, methodSets := program.methodSets }
  let σ₀ ← GoCore.Machine.seedGlobals state program.globals
  -- Defense-in-depth behind the decoder's globaladdr bound check
  -- (audit response, C1): mirror of `runProgramM`'s post-seed assert.
  if GoCore.Machine.StateWf σ₀ then pure () else
    throw (.internal "seeded state ill-formed: a location in a global cell or function body dangles beyond the allocator bound")
  let initBody? ←
    match GoCore.findFunctionIn? program.funcs GoCore.pkgInitFuncId with
    | none => pure none
    | some initF =>
        if initF.args.size != 0 || initF.results.size != 0 then
          throw (.stuck s!"malformed {GoCore.pkgInitFuncId.key}: expected no parameters and no results")
        else pure (some initF.body)
  return { σ₀, initBody?, func, args }

/-- One machine run to a program terminal: the observation JSON plus
the LEFTOVER choice stream. `Choices.consume` pops exactly one element
while the stream is non-empty (exhaustion consumes nothing and yields the
default 0), so `provided − |leftover|` is the exact number of consumption
sites reached whenever the leftover is non-empty — the enumerator's
consumption meter.

THE POOL MIRROR (channels arc slice 4): the subject phase runs on the
THREAD POOL, exactly like `native-json-run`'s `runProgramPoolM` — this
loop hand-mirrors `execProgLoop`'s terminal-classification order
(any-goroutine panic abort, main's terminal, the all-asleep deadlock
state, all BEFORE the fuel check) while REUSING the machine's own
`stepMulti` and `raceUpdate` verbatim, so every pool step, every
consumption site (L1 scheduler, L4 waiter pick, L2 select pick,
mapIter, append spill), and the race detector are the machine's own.
Member statuses: `"ok"` (main `.normal`, readout at the pinned result
locations), `"panic"` (any goroutine's unrecovered panic — the stream
is KEPT: the panic is a member), and — lane d — `"race"` (the
detector's refusal, also a member with its stream: for a racy case
EVERY enumerated path must carry it, which `--expect-status race`
enforces; under any other expectation a race member fails the status
discipline loudly). All other `GoError`s (stuck, unsupported,
internal, fuel-out, and `deadlock` — a deadlocking member still has
no membership handling) propagate and the enumeration fails loud.
Returns (status, observation, leftover); non-`private` so the
driver-agreement eval tests can pin it against the originals it
mirrors (audit F5). -/
def enumPoolRun (resultLocs : List Loc) :
    Nat → GoCore.Machine.MultiConfig → GoCore.Machine.RaceState →
    GoCore.Choices → Except GoError (String × Json × GoCore.Choices)
  | fuel, m, r, choices =>
      if m.threads.isEmpty then
        throw (.internal "thread pool without a main goroutine")
      else
        match m.panicMsg? with
        | some msg => return ("panic", errorJson (.panic msg), choices)
        | none =>
            match m.mainOutcome? with
            | some (.normal σf) =>
                -- THE MAIN-EXIT WINDOW (L5, BUG-044) — `execProgLoop`'s
                -- bound-2 site, mirrored: with runnable goroutines left,
                -- pick 0 exits now, pick 1 takes one more pool step.
                (match GoCore.Machine.runnableIdxs m.shared m.threads with
                | [] =>
                    return ("ok", runJson
                      { values := (← GoCore.Machine.loadMany σf resultLocs).toArray },
                      choices)
                | _ :: _ =>
                    let (pick, choices₁) :=
                      GoCore.Choices.consumeAt .l5ExitWindow 2 choices
                    if pick == 0 then
                      return ("ok", runJson
                        { values := (← GoCore.Machine.loadMany σf resultLocs).toArray },
                        choices₁)
                    else
                      match fuel with
                      | 0 => throw .fuelOut
                      | fuel + 1 => do
                          let (m', choices', ev) ← GoCore.Machine.stepMulti m choices₁
                          match GoCore.Machine.raceUpdate m.shared m.threads ev m' r with
                          | .error .raceDetected =>
                              return ("race", errorJson .raceDetected, choices')
                          | .error e => throw e
                          | .ok r' => enumPoolRun resultLocs fuel m' r' choices')
            | some _ => throw (.internal "main terminal outside its barrier frame")
            | none =>
                if (GoCore.Machine.runnableIdxs m.shared m.threads).isEmpty then
                  throw .deadlock
                else
                  match fuel with
                  | 0 => throw .fuelOut
                  | fuel + 1 => do
                      let (m', choices', ev) ← GoCore.Machine.stepMulti m choices
                      match GoCore.Machine.raceUpdate m.shared m.threads ev m' r with
                      | .error .raceDetected =>
                          return ("race", errorJson .raceDetected, choices')
                      | .error e => throw e
                      | .ok r' => enumPoolRun resultLocs fuel m' r' choices'

/-- The `$pkginit` phase of an enumeration run (init slice):
`runConfig`-mirroring terminal handling, but returning the FINAL STATE
(the subject runs from it) instead of a result observation. A panic terminal is the run's
observation (a panicking initializer aborts the program before the
subject), reported with the leftover stream like any panic member. -/
def enumInitRun :
    Nat → GoCore.ExecState → GoCore.Machine.Config → GoCore.Choices →
    Except GoError (Sum (GoCore.ExecState × GoCore.Choices) (String × GoCore.Choices))
  | _, σ, .next .stop, choices => return .inl (σ, choices)
  | _, _, .panicked msg, choices => return .inr (msg, choices)
  | _, _, .blockedSend _ _ _, _ => throw .deadlock
  | _, _, .blockedRecv _ _ _ _ _, _ => throw .deadlock
  | _, _, .blockedSelect _ _ _, _ => throw .deadlock
  | 0, _, _, _ => throw .fuelOut
  | fuel + 1, σ, c, choices => do
      let (c', σ', choices') ← GoCore.Machine.stepFn σ c choices
      enumInitRun fuel σ' c' choices'

/-- One whole-PROGRAM enumeration run under one stream: `$pkginit` (when
present) consumes from the stream first, then the subject entry wiring
(the `runProgramM` mirror — `bindParams`/`allocDecls`/`pinResultLocs`
are deterministic and choice-free, but the post-init STATE they extend
can differ per stream, so they run here, per stream, not in setup) and
the subject itself on the leftover. The returned leftover is the
composite run's — init sites and subject sites are all sites of the
run, which is what the explore loop's probe semantics count. -/
def enumRunProgram (ep : EnumProgram) (runFuel : Nat)
    (stream : GoCore.Choices) : Except GoError (String × Json × GoCore.Choices) := do
  let (σ₁, choices₁) ←
    match ep.initBody? with
    | none => pure (ep.σ₀, stream)
    | some body =>
        -- Diagnostic errors carry the `package init:` phase marker,
        -- mirroring `runPkgInitM` (audit response 2026-08-05, C6); the
        -- panic member's message stays unmarked (Go-observable).
        match enumInitRun runFuel ep.σ₀
            (.exec body [] (.frame [] [] [] [] .stop)) stream with
        | .error e => throw (GoCore.Machine.markInitPhase e)
        | .ok (.inl r) => pure r
        | .ok (.inr (msg, leftover)) => return ("panic", errorJson (.panic msg), leftover)
  let (env, s₂) ← GoCore.Machine.bindParams [] σ₁ ep.func.args.toList ep.args.toList
  let (frameEnv, s₃) ← GoCore.Machine.allocDecls env s₂ ep.func.results.toList
  let resultLocs ← GoCore.Machine.pinResultLocs frameEnv ep.func.results.toList
  -- The subject runs on the POOL (slice 4), mirroring `runProgramPoolM`:
  -- a fresh one-thread pool over the initialized state, race detector
  -- armed from empty.
  enumPoolRun resultLocs runFuel
    ⟨#[.exec ep.func.body frameEnv (.frame [] [] [] [] .stop)], s₃, 0⟩ {} choices₁

/-- The observation `native-json-run` prints for a driver result — public
so the driver-agreement eval tests compare the two drivers on the SAME
canonical JSON (audit F5). -/
def observationOfRun : Except GoError GoCore.Result → Json
  | .ok result => runJson result
  | .error err => errorJson err

structure EnumOutcome where
  /-- Distinct observations (canonical `Json`, deduplicated by structural
  equality — the same equality `observation-eq` decides). -/
  observations : Array Json := #[]
  /-- Machine steps taken across the exploration tree (pool steps in the
  subject phase, `stepFn` steps in the `$pkginit` phase; shared prefixes
  counted ONCE — the stepwise engine's work meter). -/
  steps : Nat := 0
  /-- Alias-ladder probe RUNS performed (the bound accountant's
  cross-check; each is a full root-replay). -/
  probes : Nat := 0
  /-- Observations of the alias-ladder probe runs (deduplicated). The
  final certification check requires every one to be a member of
  `observations`; an escapee refutes the computed site bounds. -/
  probeObservations : Array Json := #[]
  /-- Consumption sites discovered (tree nodes drawing a pick). -/
  sitesSeen : Nat := 0
  /-- Complete leaves (terminal paths) explored. -/
  leaves : Nat := 0
  /-- Maximum picks consumed along any single path. -/
  maxDepth : Nat := 0
  /-- Branches that exhausted the per-branch step budget under an
  explicit `--allow-nonterm` (W3.2 stage D §5d): COUNTED, never an
  observation member, never green-contributing — membership means
  "oracle observation ∈ TERMINATING members". Without the flag a
  fuel-out branch stays a loud failure (fail-closed default). -/
  nonterm : Nat := 0
  /-- backEdge scheduling sites explored CAPPED (canonical slot + k
  anti-progress slots) rather than exhaustively — the per-site
  enumeration mode (stage D §5d). Nonzero means the certified tree is
  the capped one; the count prints into the run record so the claim
  states exactly which tree it certified. -/
  backedgeCapped : Nat := 0

/-! ## The stepwise pool explorer (channels arc slice 4)

The membership enumerator's engine, rebuilt for the POOL: the prior
whole-run frontier explored alphabet `[0, B)` at EVERY site under one
author-asserted width `B`, which is intractable at scheduler scale
(a 3-goroutine litmus case has ~15 consumption sites of bound 2-3, and
uniform width-3 exploration wastes `3/2` per bound-2 site — a ~300×
blowup — while the per-leaf alias ladder multiplied the probe count by
path length). The rebuilt engine explores STEPWISE with MACHINE-COMPUTED
per-site bounds:

* **`stepNeeds` — the consumption ACCOUNTANT** (a CLI-layer mirror of
  exactly the consumption decision points of one `stepMulti` call,
  REUSING the machine's own analysis functions — `runnableIdxs`,
  `arrivalCases`, `applySelectCore`, `appendSpillWidth` — so every
  BOUND is computed by the same code the semantics consumes with; only
  the dispatch skeleton is mirrored). Given the picks supplied for the
  next pool step it answers: `none` — the step consumes nothing
  further — or `some b` — the step's next draw is a SITE of bound `b`.
  This realizes the membership design's deferred "mechanical bound
  certification" WITHOUT touching GoCore (the deferral's stated
  concern): the hook is a CLI copy, pinned like every driver copy —
  by the driver-agreement eval tests and the harness's per-case
  coupling check — plus the two in-engine cross-checks below.
* **The author width is now a mechanically-checked CAP**: a site whose
  computed bound exceeds the case's `width` fails the enumeration loud
  ("width assertion refuted mechanically") — the F2a discipline, now
  exact at every explored site instead of heuristic.
* **The alias ladder is retargeted at the ACCOUNTANT**: for each
  discovered site of computed bound `b`, three full root-replays probe
  raw picks `b`, `2b+1`, `4b+3` at that position (offsets ≡ 0 mod `b`
  only if `b` is the true bound — the de-aligned upper rungs survive
  divisor coincidences, delta-review T1). A probe observation outside
  the enumerated set refutes the computed bound. HONEST SCOPE (S4
  audit): the probe stream ends at the probed position, so every
  later site takes the empty-stream default 0 — the probe exhibits
  only the ALL-DEFAULTS leaf of the bumped branch, and an escaping
  residue whose distinguishing behavior needs a later non-default
  pick can still alias into the set (demonstrated on schedLenHandoff:
  node [1,1], branch subtree {110} with the divergent 100 one
  non-default pick deeper). The old per-leaf suffix multiplicity
  carried that refutation power and was NOT pure redundancy; the
  primary check on the accountant is the driver-agreement /
  coupling pins plus the sentinel drift alarm, with the ladder as
  the heuristic magnitude cross-check. Probes run
  through `enumRunProgram` — the REAL semantics end to end, empty-tail
  defaults included — so a probe is never itself accountant-derived.
* **DFS with shared prefixes**: work is counted in machine STEPS over
  the distinct-behavior tree (a shared prefix executes once), with the
  established fail-loud caps carried over: `--max-sites` (picks per
  path), `--cap` (distinct observations), `--work-cap` (steps +
  probes; NOTE the unit changed from whole runs to steps — per-case
  `work` params recalibrated in the same change).

Member statuses and the status discipline (audit F1) are unchanged;
`"race"` members (the detector's refusal) join for lane d — a racy
case enumerates under `--expect-status race`, so EVERY path must
refuse. Deadlock members still fail loud (no membership handling). -/

/-- The consumption accountant (docstring above): walks the consumption
decision points of ONE `stepMulti` call over the supplied pick vector.
`none` = the vector suffices (the real `stepMulti` will draw only from
it); `some b` = the step's next draw would exceed the vector — a site
of bound `b` at this position. Errors and non-consuming refusals
return `none` (the real step surfaces them). -/
def stepNeeds (m : GoCore.Machine.MultiConfig) (picks : GoCore.Choices) :
    Option Nat :=
  match m.threads[m.cur]? with
  | none => none
  | some c₀ =>
    -- Site: the boundary scheduling pick (l1Sched, or stage C's
    -- postOp — the marker's own site; consumed only when the slot
    -- MENU has ≥ 2 entries). The mirror indexes the same menu the
    -- machine does (`schedSlots` — issuer-first at postOp), never
    -- bare `runnableIdxs`: the slot→goroutine mapping is part of the
    -- decision being mirrored.
    let menu := GoCore.Machine.schedSlots m.shared m.threads m.cur
      c₀.boundarySite
    let l1 : Option (Nat × GoCore.Choices) :=
      if c₀.atBoundary then
        match menu with
        | [] => none  -- all asleep: classified before stepping
        | [j] => some (j, picks)
        | rs =>
            match picks with
            | [] => none  -- signal handled below via the sentinel
            | p :: rest =>
                match rs[p % rs.length]? with
                | some j => some (j, rest)
                | none => none
      else some (m.cur, picks)
    match c₀.atBoundary, menu, picks with
    | true, _ :: _ :: _, [] => some menu.length
    | _, _, _ =>
      match l1 with
      | none => none
      | some (i, ch) =>
        match m.threads[i]? with
        | none => none
        | some c =>
          if GoCore.Machine.isBlockedConfig c then none
          else if (GoCore.Machine.opDoneInner c).isSome then none
          else
            match GoCore.Machine.spawnPlan c with
            | some _ => none
            | none =>
              match GoCore.Machine.arrivalCases m.shared m.threads i c with
              | .error _ => none
              | .ok (.single _ cs) =>
                  if cs.length ≤ 1 then none
                  else match ch with
                    | [] => some cs.length
                    | _ :: _ => none
              | .ok (.multi os) =>
                  (match ch with
                  | [] => some os.length
                  | p :: rest =>
                      match os[p % os.length]? with
                      | some (.pair _ cs) =>
                          if cs.length ≤ 1 then none
                          else match rest with
                            | [] => some cs.length
                            | _ :: _ => none
                      | _ => none)
              | .ok .cellPath =>
                  -- The sequential machine's own sites, per shape.
                  match c with
                  | .next (.mapIterK _ _ keyTy valTy _ base produced start _ _) =>
                      -- BUG-005 (L): the pick width is candidates + the
                      -- stop slot, computed from the STATE with the
                      -- machine's own analysis functions (never a
                      -- hand-copied bound).
                      (match GoCore.Machine.mapIterCandidates m.shared
                          keyTy valTy base produced with
                      | .error _ => none
                      | .ok cands =>
                          if cands.isEmpty then none
                          else
                            let mand := GoCore.Machine.mapIterMandatoryRemains
                              cands start
                            match ch with
                            | [] => some (cands.size
                                + (if mand then 0 else 1))
                            | _ :: _ => none)
                  | .retV v (.selectOpsK clauses default? done [] env k) =>
                      (match GoCore.Machine.applySelectCore m.shared clauses
                          default? ((v :: done).reverse) env k with
                      | .ok (.picks commits) =>
                          (match ch with
                          | [] => some commits.length
                          | _ :: _ => none)
                      | _ => none)
                  | .retV v (.stmtOpK (.appendSlice _) _ done [] _ _) =>
                      -- The spill's capacity site (bound mirrors
                      -- `applyStmtOp`'s appendSlice arm verbatim).
                      (match (v :: done).reverse with
                      | [_, sliceV, elemsV] =>
                          (match GoCore.valueAsSlice sliceV,
                              GoCore.valueAsSlice elemsV with
                          | .ok slice, .ok elems =>
                              let newLen := slice.len + elems.len
                              if newLen ≤ slice.cap then none
                              else match ch with
                                | [] => some
                                    (GoCore.appendSpillWidth slice.cap newLen)
                                | _ :: _ => none
                          | _, _ => none)
                      | _ => none)
                  | _ => none

/-- The SEQUENTIAL accountant for the `$pkginit` phase (one `stepFn`
step consumes at most one pick): `some b` iff this configuration's next
step draws a pick, with bound `b`. -/
def stepNeedsSeq (σ : GoCore.ExecState) (c : GoCore.Machine.Config) :
    Option Nat :=
  match c with
  | .next (.mapIterK _ _ keyTy valTy _ base produced start _ _) =>
      (match GoCore.Machine.mapIterCandidates σ keyTy valTy base produced with
      | .error _ => none
      | .ok cands =>
          if cands.isEmpty then none
          else
            let mand := GoCore.Machine.mapIterMandatoryRemains cands start
            some (cands.size + (if mand then 0 else 1)))
  | .retV v (.selectOpsK clauses default? done [] env k) =>
      (match GoCore.Machine.applySelectCore σ clauses default?
          ((v :: done).reverse) env k with
      | .ok (.picks commits) => some commits.length
      | _ => none)
  | .retV v (.stmtOpK (.appendSlice _) _ done [] _ _) =>
      (match (v :: done).reverse with
      | [_, sliceV, elemsV] =>
          (match GoCore.valueAsSlice sliceV, GoCore.valueAsSlice elemsV with
          | .ok slice, .ok elems =>
              let newLen := slice.len + elems.len
              if newLen ≤ slice.cap then none
              else some (GoCore.appendSpillWidth slice.cap newLen)
          | _, _ => none)
      | _ => none)
  | _ => none

/-- Exploration context (invariant across the tree). -/
structure ExpCtx where
  ep : EnumProgram
  runFuel : Nat
  width : Nat
  sites : Nat
  cap : Nat
  workCap : Nat
  expectStatus : Option (List String)
  /-- `some N` = `--allow-nonterm N`: per-branch pool fuel N, with
  fuel-exhausted branches counted into `EnumOutcome.nonterm` instead of
  failing the enumeration (stage D §5d — the wedge family's honest
  divergent branches). `none` = the fail-closed default. -/
  allowNonterm : Option Nat := none
  /-- backEdge per-site enumeration mode (stage D §5d): `none` =
  UNDECLARED — a bound ≥ 2 backEdge consult fails loud (a row must say
  which tree it certifies); `some none` = `--backedge full`
  (exhaustive); `some (some k)` = `--backedge k` (canonical slot 0
  plus the first k anti-progress slots per occurrence; the alias
  ladder is SKIPPED at capped occurrences — a capped site's width is
  deliberately un-certified, and `backedgeCapped` prints it). -/
  backedgeMode : Option (Option Nat) := none

/-- Record one terminal leaf: status discipline (audit F1; SET-valued
since the arc-final audit F8 — see `EnumArgs.expectStatus`), observation
dedup, cap check. -/
def recordLeaf (ctx : ExpCtx) (out : EnumOutcome) (path : List Nat)
    (status : String) (obs : Json) (depth : Nat) :
    Except String EnumOutcome := do
  if ctx.expectStatus.any (fun ss => !ss.contains status) then
    .error s!"machine-side status divergence: member under pick assignment {path.reverse} has status {status}, outside the case's declared status set {ctx.expectStatus.getD []} — a member Go may never realize is a machine bug; a genuinely Go-realizable status belongs in the declared set (status-diverse envelopes declare e.g. ok,panic — audit F8). Member: {obs.compress}"
  else
    let observations :=
      if out.observations.contains obs then out.observations
      else out.observations.push obs
    if observations.size > ctx.cap then
      .error s!"observation cap N={ctx.cap} exceeded — the case is too wide for enumeration (design note: needs a per-case predicate)"
    else
      .ok { out with
            observations := observations
            leaves := out.leaves + 1
            maxDepth := max out.maxDepth depth }

/-- One alias-ladder probe set for a site of computed bound `b` at path
position `path` (reversed picks so far): three full ROOT-replays through
`enumRunProgram` — the real semantics — at raw picks `b`, `2b+1`,
`4b+3`, observations collected for the final membership check. A probe
whose RUN fails still fails the enumeration loud — but as the MEMBER
failure it is (audit F15: under a correct bound every rung reduces
modulo the bound onto an in-bound member already in the DFS tree, so
an errored probe run is an ordinary member-class failure — e.g. a
deadlocking or fuel-exhausting member — and is NOT evidence against
the computed bound; the bound-refutation criterion is the OTHER check,
a probe observation outside the enumerated set, CLI's certification
check in `explore`).
Scope: the probe stream is prefix-only — later sites take the
empty-stream default — so each rung exhibits the bumped branch's
all-defaults leaf only (the engine docstring's HONEST SCOPE note). -/
def probeSite (ctx : ExpCtx) (out : EnumOutcome) (path : List Nat)
    (bound : Nat) : Except String EnumOutcome := do
  let prefixPicks := path.reverse
  let mut o := out
  for d in [bound, 2 * bound + 1, 4 * bound + 3] do
    match enumRunProgram ctx.ep ctx.runFuel (prefixPicks ++ [d]) with
    | .error .fuelOut =>
        if ctx.allowNonterm.isSome then
          -- The rung aliased onto a divergent branch — the same class
          -- the DFS counts into `nonterm` under the explicit flag; it
          -- yields no observation, so it cannot escape the membership
          -- check either. Counted as a probe run (work accounting).
          o := { o with probes := o.probes + 1 }
        else
          throw s!"alias-guard probe {prefixPicks ++ [d]} failed: the probed member's run errored — {renderGoError GoError.fuelOut}. Under a correct bound this rung aliases onto an in-bound member, so this is a member-class failure (e.g. a deadlocking or fuel-out member, which has no membership handling), NOT evidence against the computed bound {bound} (audit F15; a bound refutation is a probe OBSERVATION outside the enumerated set)"
    | .error err =>
        throw s!"alias-guard probe {prefixPicks ++ [d]} failed: the probed member's run errored — {renderGoError err}. Under a correct bound this rung aliases onto an in-bound member, so this is a member-class failure (e.g. a deadlocking or fuel-out member, which has no membership handling), NOT evidence against the computed bound {bound} (audit F15; a bound refutation is a probe OBSERVATION outside the enumerated set)"
    | .ok (_, obs, _) =>
        let pset :=
          if o.probeObservations.contains obs then o.probeObservations
          else o.probeObservations.push obs
        o := { o with probes := o.probes + 1, probeObservations := pset }
  if o.probes > ctx.workCap then
    throw s!"work cap exceeded during alias probes ({o.probes} probe run(s)) — raise --work-cap"
  return o

/-- Branch a discovered site: width cap (mechanical F2a check), sites
cap, per-pick recursion via `k`. -/
def branchSite (ctx : ExpCtx) (out : EnumOutcome) (path : List Nat)
    (bound : Nat) (depth : Nat)
    (k : EnumOutcome → Nat → Except String EnumOutcome) :
    Except String EnumOutcome := do
  if bound > ctx.width then
    .error s!"site bound {bound} exceeds the case's width {ctx.width} — the width assertion is REFUTED (mechanically, at pick position {depth}); raise the case's width metadata"
  else if depth + 1 > ctx.sites then
    .error s!"run consumes more than --max-sites {ctx.sites} choice site(s) — raise the case's sites bound (never truncated silently)"
  else do
    let out ← probeSite ctx { out with sitesSeen := out.sitesSeen + 1 }
      path bound
    let mut o := out
    for b in List.range bound do
      o ← k o b
    return o

/-- A branch that exhausted its per-branch budget under
`--allow-nonterm`: counted, pruned, never a member (stage D §5d). -/
def recordNonterm (out : EnumOutcome) : Except String EnumOutcome :=
  .ok { out with nonterm := out.nonterm + 1 }

mutual

/-- DFS over the POOL phase from a mid-run state. `path` is the picks
consumed so far, REVERSED (a snoc list); `stepPicks` the picks fed to
the in-progress pool step (reversed); `fuel` the remaining per-path
pool-step budget. Terminal classification mirrors `enumPoolRun`
(panic/main/deadlock before the fuel check); each completed step goes
through the REAL `stepMulti` + `raceUpdate`. -/
partial def poolDFS (ctx : ExpCtx) (out : EnumOutcome) (path : List Nat)
    (resultLocs : List Loc)
    (fuel : Nat) (m : GoCore.Machine.MultiConfig)
    (r : GoCore.Machine.RaceState) : Except String EnumOutcome := do
  if out.steps + out.probes > ctx.workCap then
    .error s!"work cap exceeded after {out.steps} step(s) + {out.probes} probe(s) with subtrees still unexplored — raise --work-cap or narrow the case"
  else if m.threads.isEmpty then
    .error "thread pool without a main goroutine"
  else
    match m.panicMsg? with
    | some msg =>
        recordLeaf ctx out path "panic" (errorJson (.panic msg)) path.length
    | none =>
      match m.mainOutcome? with
      | some (.normal σf) =>
          let exitLeaf : EnumOutcome → List Nat → Except String EnumOutcome :=
            fun o p =>
              match GoCore.Machine.loadMany σf resultLocs with
              | .error e =>
                  .error s!"result readout failed at a terminal: {renderGoError e}"
              | .ok vals =>
                  recordLeaf ctx o p "ok"
                    (runJson { values := vals.toArray }) p.length
          (match GoCore.Machine.runnableIdxs m.shared m.threads with
          | [] => exitLeaf out path
          | _ :: _ =>
              -- THE MAIN-EXIT WINDOW (L5, BUG-044): a bound-2 site —
              -- pick 0 exits with main's readout, pick 1 takes one more
              -- pool step (mirrors `enumPoolRun`/`execProgLoop`).
              branchSite ctx out path 2 path.length fun o b =>
                if b == 0 then exitLeaf o (b :: path)
                else
                  match fuel with
                  | 0 =>
                      if ctx.allowNonterm.isSome then recordNonterm o
                      else .error "per-path fuel exhausted (raise --fuel)"
                  | fuel' + 1 =>
                      poolStepDFS ctx o (b :: path) resultLocs fuel' m r [])
      | some _ => .error "main terminal outside its barrier frame"
      | none =>
        if (GoCore.Machine.runnableIdxs m.shared m.threads).isEmpty then
          .error s!"deadlock member under pick assignment {path.reverse} — deadlocking members have no membership handling (fail loud, per the design)"
        else
          match fuel with
          | 0 =>
              if ctx.allowNonterm.isSome then recordNonterm out
              else .error "per-path fuel exhausted (raise --fuel)"
          | fuel' + 1 => poolStepDFS ctx out path resultLocs fuel' m r []

/-- Feed picks to the CURRENT pool step until the accountant says the
vector suffices, branching at each reported site; then take the step
through the real `stepMulti` + `raceUpdate`. -/
partial def poolStepDFS (ctx : ExpCtx) (out : EnumOutcome) (path : List Nat)
    (resultLocs : List Loc) (fuel : Nat)
    (m : GoCore.Machine.MultiConfig) (r : GoCore.Machine.RaceState)
    (stepPicks : List Nat) : Except String EnumOutcome := do
  let picks := stepPicks.reverse
  -- Is THIS consumption the boundary scheduling consult of a backEdge
  -- site? (First consumption of the step at a boundary config whose
  -- site is backEdge — the reported bound is then the slot-menu
  -- length; stage D §5d's per-site enumeration mode applies.)
  let backEdgeSched :=
    stepPicks.isEmpty &&
    (match m.threads[m.cur]? with
     | some c => c.atBoundary && c.boundarySite == .backEdge
         -- The consult CONSUMES (and the mode applies) only when the
         -- slot menu has ≥ 2 entries; at a singleton menu the step's
         -- first consumption is an ordinary data pick (e.g. the
         -- mapIter pick at a single-goroutine `.mapIterK` re-entry),
         -- which branches exhaustively as always.
         && 2 ≤ (GoCore.Machine.schedSlots m.shared m.threads m.cur
              c.boundarySite).length
     | none => false)
  match stepNeeds m picks with
  | some bound =>
      if backEdgeSched then
        match ctx.backedgeMode with
        | none =>
            .error s!"backEdge scheduling site of bound {bound} under pick assignment {path.reverse} — the row must DECLARE its back-edge tree: backedge=<k> (capped: canonical slot + k anti-progress slots per occurrence) or backedge=full (exhaustive; loop-length-exponential) — stage D §5d, never a silent prune"
        | some none =>
            branchSite ctx out path bound path.length fun o b =>
              poolStepDFS ctx o (b :: path) resultLocs fuel m r (b :: stepPicks)
        | some (some kcap) =>
            -- Capped: slots [0 .. min kcap (bound-1)]; the alias
            -- ladder is SKIPPED (a capped occurrence's width is
            -- deliberately un-certified — `backedgeCapped` records
            -- it); the width/sites disciplines still apply.
            if bound > ctx.width then
              .error s!"site bound {bound} exceeds the case's width {ctx.width} — the width assertion is REFUTED (mechanically, at pick position {path.length}); raise the case's width metadata"
            else if path.length + 1 > ctx.sites then
              .error s!"run consumes more than --max-sites {ctx.sites} choice site(s) — raise the case's sites bound (never truncated silently)"
            else do
              let explored := min (kcap + 1) bound
              let out :=
                { out with
                  sitesSeen := out.sitesSeen + 1
                  backedgeCapped :=
                    out.backedgeCapped + (if explored < bound then 1 else 0) }
              let mut o := out
              for b in List.range explored do
                o ← poolStepDFS ctx o (b :: path) resultLocs fuel m r
                  (b :: stepPicks)
              return o
      else
        branchSite ctx out path bound path.length fun o b =>
          poolStepDFS ctx o (b :: path) resultLocs fuel m r (b :: stepPicks)
  | none =>
      -- TWO-SIDED drift alarm (S4 audit): run the step with ONE
      -- SENTINEL pick appended and require the sentinel to survive as
      -- the exact leftover. Over-supply (accountant said the picks
      -- were needed, the machine consumed fewer) leaves extra picks
      -- beside the sentinel; UNDER-supply (a consumption site the
      -- accountant MISSED — previously silent, because
      -- `Choices.consume` defaults to 0 on an exhausted stream)
      -- swallows the sentinel. Both fail loud. The sentinel is never
      -- consulted when it survives, so `m'` is exactly the
      -- sentinel-free step's result.
      match GoCore.Machine.stepMulti m (picks ++ [0]) with
      | .error e =>
          .error s!"machine step failed under pick assignment {path.reverse} — cannot certify the observation set: {renderGoError e}"
      | .ok (m', leftover, ev) =>
          if leftover != [0] then
            .error s!"consumption accountant drift under {path.reverse}: sentinel-suffixed step left {leftover} (expected the sentinel alone) — the accountant {if leftover.isEmpty then "MISSED a consumption site (the machine drew the sentinel)" else "over-counted (supplied picks went unconsumed)"}; driver-copy drift, cannot certify"
          else
            match GoCore.Machine.raceUpdate m.shared m.threads ev m' r with
            | .error .raceDetected =>
                recordLeaf ctx { out with steps := out.steps + 1 } path
                  "race" (errorJson .raceDetected) path.length
            | .error e =>
                .error s!"race-detector update failed: {renderGoError e}"
            | .ok r' =>
                poolDFS ctx { out with steps := out.steps + 1 } path
                  resultLocs fuel m' r'

end

/-- The per-branch subject entry (`enumRunProgram`'s wiring, per init
branch): bind params, allocate results, pin locations, seed the
one-thread pool with the detector armed. -/
partial def subjectEntry (ctx : ExpCtx) (out : EnumOutcome) (path : List Nat)
    (σ : GoCore.ExecState) : Except String EnumOutcome := do
  match GoCore.Machine.bindParams [] σ ctx.ep.func.args.toList
      ctx.ep.args.toList with
  | .error e => .error s!"subject entry failed: {renderGoError e}"
  | .ok (env, s₂) =>
    match GoCore.Machine.allocDecls env s₂ ctx.ep.func.results.toList with
    | .error e => .error s!"subject entry failed: {renderGoError e}"
    | .ok (frameEnv, s₃) =>
      match GoCore.Machine.pinResultLocs frameEnv ctx.ep.func.results.toList with
      | .error e => .error s!"subject entry failed: {renderGoError e}"
      | .ok resultLocs =>
          poolDFS ctx out path resultLocs ctx.runFuel
            ⟨#[.exec ctx.ep.func.body frameEnv (.frame [] [] [] [] .stop)], s₃, 0⟩
            {}

/-- DFS over the `$pkginit` phase (sequential, one pick per step at
most); on the init terminal, wire the subject entry (per branch — the
post-init state differs per path) and hand off to the pool DFS. A
panicking initializer is the run's (panic) member. -/
partial def initDFS (ctx : ExpCtx) (out : EnumOutcome) (path : List Nat)
    (fuel : Nat) (σ : GoCore.ExecState) (c : GoCore.Machine.Config) :
    Except String EnumOutcome := do
  if out.steps + out.probes > ctx.workCap then
    .error s!"work cap exceeded after {out.steps} step(s) + {out.probes} probe(s) with subtrees still unexplored — raise --work-cap or narrow the case"
  else
    match c with
    | .next .stop => subjectEntry ctx out path σ
    | .panicked msg =>
        recordLeaf ctx out path "panic" (errorJson (.panic msg)) path.length
    | .blockedSend _ _ _ => .error "package init deadlocked (fail loud)"
    | .blockedRecv _ _ _ _ _ => .error "package init deadlocked (fail loud)"
    | .blockedSelect _ _ _ => .error "package init deadlocked (fail loud)"
    | c =>
      match fuel with
      | 0 => .error "per-path fuel exhausted in package init (raise --fuel)"
      | fuel' + 1 =>
        match stepNeedsSeq σ c with
        | some bound =>
            -- Sentinel-suffixed like the pool path: the branch pick
            -- must be consumed AND nothing more (a sequential step
            -- draws at most one pick — checked, not assumed).
            branchSite ctx out path bound path.length fun o b =>
              match GoCore.Machine.stepFn σ c [b, 0] with
              | .error e =>
                  .error s!"package init step failed under {(b :: path).reverse}: {renderGoError e}"
              | .ok (c', σ', leftover) =>
                  if leftover != [0] then
                    .error s!"consumption accountant drift in package init under {(b :: path).reverse}: sentinel-suffixed step left {leftover} (expected the sentinel alone) — driver-copy drift"
                  else
                    initDFS ctx { o with steps := o.steps + 1 } (b :: path)
                      fuel' σ' c'
        | none =>
            -- TWO-SIDED here too (S4 audit): the sentinel must survive
            -- a step the accountant called non-consuming.
            match GoCore.Machine.stepFn σ c [0] with
            | .error e =>
                .error s!"package init failed under {path.reverse}: {renderGoError (GoCore.Machine.markInitPhase e)}"
            | .ok (c', σ', leftover) =>
                if leftover != [0] then
                  .error s!"consumption accountant drift in package init under {path.reverse}: a step the accountant called non-consuming drew the sentinel — driver-copy drift"
                else
                  initDFS ctx { out with steps := out.steps + 1 } path fuel' σ' c'

/-- The engine's entry: explore from the seeded state (init phase when
present, then the pool subject per branch), then run the certification
check — every alias-probe observation must be a member. -/
def explore (ep : EnumProgram) (runFuel width sites cap workCap : Nat)
    (expectStatus : Option (List String))
    (allowNonterm : Option Nat := none)
    (backedgeMode : Option (Option Nat) := none) :
    Except String EnumOutcome := do
  -- `--allow-nonterm N` is the PER-BRANCH budget: it replaces the run
  -- fuel, so divergent branches are pruned-and-counted at N instead of
  -- burning the default 10M each (stage D §5d).
  let runFuel := allowNonterm.getD runFuel
  let ctx : ExpCtx :=
    { ep, runFuel, width, sites, cap, workCap, expectStatus,
      allowNonterm, backedgeMode }
  let out ←
    match ep.initBody? with
    | none => subjectEntry ctx {} [] ep.σ₀
    | some body =>
        initDFS ctx {} [] runFuel ep.σ₀
          (.exec body [] (.frame [] [] [] [] .stop))
  -- THE CERTIFICATION CHECK: probe observations ⊆ enumerated set.
  for pobs in out.probeObservations do
    if !out.observations.contains pobs then
      throw s!"alias guard: a probe pick ≥ the computed site bound produced an observation OUTSIDE the enumerated set — the bound accountant (or the case's width assertion) is REFUTED; cannot certify. Probe observation: {pobs.compress}"
  return out

/-- The dedup-engine path (POR slice, `docs/2026-08-21_w32-por-design.md`):
build the state-graph certificate (untrusted engine), run THE VERIFIED
CHECKER, and only then print the set — the printed lines are backed by
`checkCert_slowObs` (member set = `SlowObs`, the ∃-fuel ∃-stream image
of the unmodified `execProgLoop`). The DFS lane's accountant/sentinel/
alias-ladder heuristics do not apply here; the trust boundary is the
checker plus the compiled-code trust every differential artifact
already carries. -/
def runDedupObservations (ep : EnumProgram) (cfg : EnumArgs) : IO UInt32 := do
  if ep.initBody?.isSome then
    IO.eprintln "coverage-observations: --engine dedup does not support a $pkginit phase (refused fail-closed; use the DFS engine)"
    return 1
  -- Refuse, never ignore: nonterm accounting under dedup is an open
  -- ruling (M-9) — a certificate is silent about divergent branches,
  -- so accepting the flag here would answer M-9 silently (launch
  -- audit D3-F-3; previously the flag was dropped without a word).
  if cfg.allowNonterm.isSome then
    IO.eprintln "coverage-observations: --engine dedup does not support --allow-nonterm (refused fail-closed pending the M-9 ruling; use the DFS engine)"
    return 1
  match GoCore.Machine.bindParams [] ep.σ₀ ep.func.args.toList ep.args.toList with
  | .error e =>
      IO.eprintln s!"coverage-observations: subject entry failed: {renderGoError e}"
      return 1
  | .ok (env, s₂) =>
  match GoCore.Machine.allocDecls env s₂ ep.func.results.toList with
  | .error e =>
      IO.eprintln s!"coverage-observations: subject entry failed: {renderGoError e}"
      return 1
  | .ok (frameEnv, s₃) =>
  match GoCore.Machine.pinResultLocs frameEnv ep.func.results.toList with
  | .error e =>
      IO.eprintln s!"coverage-observations: subject entry failed: {renderGoError e}"
      return 1
  | .ok resultLocs =>
    let m₀ : GoCore.Machine.MultiConfig :=
      ⟨#[.exec ep.func.body frameEnv (.frame [] [] [] [] .stop)], s₃, 0⟩
    let r₀ : GoCore.Machine.RaceState := {}
    match EnumDedup.buildCert resultLocs m₀ r₀ cfg.workCap with
    | .error err =>
        IO.eprintln s!"coverage-observations: dedup engine: {err}"
        return 1
    | .ok (cert, stats) =>
      -- THE VERIFIED CHECKER — the certification boundary. A refusal
      -- here is fail-closed: engine bug, eqb fuel exhaustion, or a
      -- fragment mismatch; never a silently-narrower set.
      if !GoCore.Machine.checkCert GoCore.Machine.dedupNodeEqb
          resultLocs m₀ r₀ cert then
        IO.eprintln "coverage-observations: dedup certificate REFUSED by the verified checker — cannot certify (engine bug or fragment mismatch)"
        return 1
      let statusOf : GoCore.Machine.Obs → String := fun o =>
        match o with
        | .ok _ => "ok"
        | .panic _ => "panic"
        | .race => "race"
      let obsJson : GoCore.Machine.Obs → Json := fun o =>
        match o with
        | .ok vs => runJson { values := vs.toArray }
        | .panic msg => errorJson (.panic msg)
        | .race => errorJson .raceDetected
      -- status discipline (audit F1/F8), unchanged in meaning
      for t in cert.members do
        if cfg.expectStatus.any (fun ss => !ss.contains (statusOf t.1)) then
          IO.eprintln s!"coverage-observations: machine-side status divergence: certified member has status {statusOf t.1}, outside the case's declared status set {cfg.expectStatus.getD []} — a member Go may never realize is a machine bug. Member: {(obsJson t.1).compress}"
          return 1
      let lines := (cert.members.map (fun t => (obsJson t.1).compress)).qsort (· < ·)
      for line in lines do
        IO.println line
      IO.eprintln s!"coverage-observations: observations={cert.members.size} steps={stats.edges} probes=0 sites={stats.nodes} leaves=0 maxdepth=0 width={cfg.maxWidth} engine=dedup nodes={stats.nodes} edges={stats.edges} dedupHits={stats.dedupHits} certified=checkCert"
      return 0

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
                  | .ok ep =>
                      match cfg.engine with
                      | some _ => runDedupObservations ep cfg
                      | none =>
                      match explore ep cfg.fuel
                          cfg.maxWidth cfg.maxSites cfg.cap cfg.workCap
                          cfg.expectStatus cfg.allowNonterm
                          cfg.backedgeMode with
                      | .error err =>
                          IO.eprintln s!"coverage-observations: {err}"
                          return 1
                      | .ok out =>
                          let lines :=
                            (out.observations.map (·.compress)).qsort (· < ·)
                          for line in lines do
                            IO.println line
                          -- Stage D §5d: the mode + counters print
                          -- into the record so a certified-set claim
                          -- states exactly which tree it certified.
                          let modeStr :=
                            match cfg.backedgeMode with
                            | none => ""
                            | some none => " backedge=full"
                            | some (some k) => s!" backedge={k} backedgeCapped={out.backedgeCapped}"
                          let ntStr :=
                            match cfg.allowNonterm with
                            | none => ""
                            | some n => s!" allow-nonterm={n} nonterm={out.nonterm}"
                          IO.eprintln s!"coverage-observations: observations={out.observations.size} steps={out.steps} probes={out.probes} sites={out.sitesSeen} leaves={out.leaves} maxdepth={out.maxDepth} width={cfg.maxWidth}{modeStr}{ntStr}"
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
