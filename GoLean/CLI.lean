import GoLean.GoCore
import GoLean.EnumDedup
import GoLean.NativeToIR
import GoLean.StrictJson
import GoLean.StrictJsonParse
import GoLean.SeedFile
import Lean.Data.Json

namespace GoLean.CLI

open System
open Lean

private def observationSchema : String :=
  "golean-observation-v1"

/-- One command-line ENTRY argument of `native-json-run`, in command-line
order: `--arg-int <n>` and `--arg-bool <true|false>` interleave freely and
bind the entry function's parameters POSITIONALLY in the order given
(gc-verified's request, [USER] Mike 2026-10-07 agreed, relayed). Each is
checked against its parameter's type before any step runs
(`entryArgValues`): a mismatch refuses by name.

The seeded-heap entry (slice B, 2026-10-12; design
`docs/2026-10-09_seeded-heap-design.md` §6, [USER] Mike 2026-10-12 agreed
to the two strategic questions, relayed) adds `--arg-ref
k(.f|[i])*` and `--arg-nil`: a reference into the `--seed` file's cells
and a nil pointer. Both exist ONLY with `--seed` on `native-json-run`
(`entrySeedArgs`); without it they are a usage error, and the enumerator
refuses them by name (design D6, v1). Since slice C (2026-10-12) `choice-trace`
takes them too (single-case mode — the strict lane's depth guard traces a
seeded row; `EnumProgram.seeded?`). -/
inductive EntryArg where
  | int (value : Int)
  | bool (value : Bool)
  | ref (cell : Nat) (path : List GoCore.Machine.SeedPathElem)
  | nil
  deriving Repr

/-- The flag that supplies an `EntryArg` (refusal texts name it). -/
def EntryArg.flag : EntryArg → String
  | .int _ => "--arg-int"
  | .bool _ => "--arg-bool"
  | .ref _ _ => "--arg-ref"
  | .nil => "--arg-nil"

/-- Whether an entry argument needs a seed (`--arg-ref` / `--arg-nil`). -/
def EntryArg.needsSeed : EntryArg → Bool
  | .ref _ _ | .nil => true
  | _ => false

/-- `--arg-bool`'s literal: exactly Go's spellings `true` / `false`.
Anything else (`1`, `True`, `"true"`, the empty string) refuses BY NAME —
no truthiness coercion. -/
def parseBoolLiteral (value : String) : Except String Bool :=
  match value with
  | "true" => .ok true
  | "false" => .ok false
  | _ => .error s!"--arg-bool: not a bool literal (expected true or false): {value}"

/-- A parameter type's UNDERLYING type for entry-argument checking: a
declared non-struct type (`type Flag bool`, `type Count uint8`) resolves
through the table to its underlying; every other type (structs and
interfaces included) is returned as is; an opaque declaration resolves to
`.unsupported` (the machine's refusal). `bound` descends on the table's
dependency order (`TypeEnv.WellFounded`); exhaustion or an unknown index
refuses by name. -/
def entryParamUnderlying (types : GoCore.TypeEnv) : Nat → GoCore.Ty → Except String GoCore.Ty
  | bound + 1, .defined i =>
      match types[i]? with
      | some (_, .defined target) => entryParamUnderlying types bound target
      -- An opaque declaration is the machine's to refuse (`unsupported`,
      -- naming the feature, at parameter normalization): handed back as
      -- `.unsupported` so `entryArgValues` defers to it.
      | some (_, .opaqueDecl reason) => .ok (.unsupported reason)
      | some _ => .ok (.defined i)
      | none => .error s!"parameter type index {i} is not in the program's type table"
  | 0, .defined i => .error s!"parameter type index {i}: type-table descent exhausted"
  | _, t => .ok t

/-- The entry function and the arity check of `entryArgValues`/`entrySeedArgs` (the unseeded
text byte-identical to the pre-seed CLI's: the BUG-119 controls pin it). A missing `main` is
the one named case (Codex F5, release-readiness row 41; RULED [USER] Mike 2026-10-13,
relayed: option (1) — keep `main` unexported in every mode and make the refusal explain
itself): the frontend never exports `main` — in default mode it must exist (BUG-125), and a
library-package wire or a `--subject` wire never had one — so `--function main` says why and names
the way out on every wire it is printed for (fix round, review LOW-3); every other missing name
keeps the old text. -/
def entryFunc (program : GoCore.Program) (name : String) (args : Array EntryArg) (seeded : Bool) :
    Except String GoCore.Func := do
  let func ←
    match GoCore.findFunctionIn? program.funcs ⟨name⟩ with
    | some func => pure func
    | none =>
        if name == "main" then
          throw "entry function not found: main — the frontend never exports main (in default mode it must exist, BUG-125); the wire holds the package's other functions; run one of them with --function (docs/cli.md)"
        else
          throw s!"entry function not found: {name}"
  if func.args.size != args.size then
    let flags := if seeded then "--arg-int/--arg-bool/--arg-ref/--arg-nil" else "--arg-int/--arg-bool"
    throw s!"entry function {name} takes {func.args.size} parameter(s), got {args.size} command-line argument(s) ({flags})"
  return func

/-- One entry argument at parameter `pos` (0-based; texts say `pos + 1`). `seed` is the decoded
seed when `--seed` was given. The `--arg-int`/`--arg-bool` arms and texts are the pre-seed
`entryArgValues`' verbatim. -/
def entryArgCheck (program : GoCore.Program) (name : String) (func : GoCore.Func)
    (seed : Option (Array GoCore.Machine.SeedCell)) (pos : Nat) (arg : EntryArg) :
    Except String GoCore.Machine.SeedArg := do
  let types := program.typeDefs
  let some param := func.args[pos]? | throw s!"internal: parameter {pos + 1} missing"
  let shown := GoCore.Ty.dynamicName types.nameOf? param.typ
  -- Display only: the Go spelling from the carried name table; a
  -- hand-built program without one shows the declaration index.
  let pname := match func.locals[param.id]? with
    | some l => l.name
    | none => s!"#{param.id}"
  let under ← entryParamUnderlying types types.size param.typ
  match arg, under, seed with
  | .int v, .int kind, _ =>
      if kind.normalize v != v then
        throw s!"--arg-int (argument {pos + 1}): {v} is out of range for parameter {pname} of type {shown} ({kind.name})"
      return .scalar (.int v)
  | .bool b, .bool, _ => return .scalar (.bool b)
  -- A frontend-QUARANTINED parameter (`$stub` params of a quarantined
  -- function, an opaque declaration) is not checked here: the value is
  -- handed on and the machine refuses it as `unsupported`, naming the
  -- quarantine cause (parameter normalization's `.unsupported` arm), so
  -- the refusal keeps its class (the harness's frontend-export stage).
  | .int v, .unsupported _, _ => return .scalar (.int v)
  | .bool b, .unsupported _, _ => return .scalar (.bool b)
  -- Seed arguments (slice B): only with `--seed` (native-json-run's parse refuses them without
  -- it — a usage error; the enumerators and the tracer refuse the flags by name). This arm is the
  -- belt: no path reaches it from a command line.
  | .ref _ _, _, none | .nil, _, none =>
      throw s!"{arg.flag} (argument {pos + 1}): a seed reference or nil needs --seed <file> (native-json-run only, golean-seed-v1)"
  | .ref k path, .pointer target, some cells =>
      let leafOrErr : Except Stop (Loc × GoCore.Ty) := do
        let root ← GoCore.Machine.seedCellTy cells k
        GoCore.Machine.seedPathLoc types (.base ⟨0⟩) root path
      match leafOrErr with
      | .error e =>
          throw s!"--arg-ref (argument {pos + 1}): parameter {pname} has type {shown}; --arg-ref {GoCore.Machine.renderSeedPath k path}: {e.message}"
      | .ok (_, leaf) =>
          if GoCore.Ty.eqb leaf target then return .ref k path
          else throw s!"--arg-ref (argument {pos + 1}): parameter {pname} has type {shown}; --arg-ref {GoCore.Machine.renderSeedPath k path} points at {GoCore.Ty.dynamicName types.nameOf? leaf}"
  | .nil, .pointer _, some _ => return .nil
  -- A quarantined parameter cannot take a seed reference: there is no declared pointer type to
  -- resolve against, so the CLI refuses by name (the int/bool deferral above keeps the machine's
  -- class only because the machine CAN receive a scalar there).
  | .ref _ _, .unsupported reason, some _ | .nil, .unsupported reason, some _ =>
      throw s!"{arg.flag} (argument {pos + 1}): parameter {pname} of entry function {name} is frontend-quarantined ({reason}) — a seed reference cannot be resolved at it"
  | _, _, _ =>
      throw s!"{arg.flag} (argument {pos + 1}): parameter {pname} of entry function {name} has type {shown}, which {arg.flag} cannot supply"

/-- Check the command-line entry arguments against the entry function's
parameter list and produce the machine's argument values. Fails closed,
BY NAME, on: an unknown entry function; an arity mismatch; an
`--arg-int` at a parameter whose underlying type is not an integer type;
an `--arg-int` literal outside its parameter kind's range (no silent
wrap — a Go call `f(300)` at a `uint8` parameter is a compile error); an
`--arg-bool` at a parameter whose underlying type is not `bool`. A
parameter whose underlying type is `.unsupported` (a frontend-quarantined
stub, an opaque declaration) is deferred to the machine, which refuses it as
`unsupported` naming the quarantine cause. Before this check (2026-10-07) an `--arg-int` at a `bool`, `string` or
interface parameter reached the machine unchecked (normalization's
catch-all arm keeps the raw `.int`), so the mismatch surfaced, if at
all, only as a `stuck` at a later use of the parameter, and an
out-of-range literal wrapped silently: both are refused here, at the
CLI, before any step. -/
def entryArgValues (program : GoCore.Program) (name : String) (args : Array EntryArg) :
    Except String (Array GoValue) := do
  let func ← entryFunc program name args false
  let mut out : Array GoValue := #[]
  for h : pos in [0:args.size] do
    match ← entryArgCheck program name func none pos args[pos] with
    | .scalar v => out := out.push v
    -- Unreachable: without a seed `entryArgCheck` refuses `--arg-ref`/`--arg-nil` by name.
    | _ => throw s!"internal: argument {pos + 1}: a seed argument without --seed"
  return out

/-- The SEEDED twin of `entryArgValues` (seeded-heap slice B, design §6): the same checks and
the same texts, byte for byte, for `--arg-int`/`--arg-bool` (handed to the core as
`SeedArg.scalar`, which passes them unchecked — D5: this IS their check), plus `--arg-ref`
(at a pointer parameter, pre-checked against the seed's DECLARED types by the core's own
`seedPathLoc`; the core re-checks — the equation's premise is the core's) and `--arg-nil` (at a
pointer parameter). The arity text names all four flags. -/
def entrySeedArgs (program : GoCore.Program) (name : String) (seed : Array GoCore.Machine.SeedCell)
    (args : Array EntryArg) : Except String (Array GoCore.Machine.SeedArg) := do
  let func ← entryFunc program name args true
  let mut out : Array GoCore.Machine.SeedArg := #[]
  for h : pos in [0:args.size] do
    out := out.push (← entryArgCheck program name func (some seed) pos args[pos])
  return out

/-- The OS error's text on ONE line, WITHOUT the path: Lean's `IO.Error`
rendering appends `\n  file: <path>`, and the refusal already leads with
the path, so that line is dropped (the path is named exactly once — train
r75 message tidy) and the rest joined (a refusal line must stay a line). -/
private def oneLine (text : String) : String :=
  let lines := (text.splitOn "\n").map (fun l => toString l.trimAscii)
  " ".intercalate (lines.filter (fun l => !l.startsWith "file: "))

/-- Read a subcommand's input file (a wire, a manifest) as bytes, CATCHING
the OS error: a missing or unreadable `--input` is a refusal that names
the path and the OS cause (BUG-120, 2026-10-08), never an IO exception
escaping `main` as the runtime's uncaught-exception message. Each
subcommand renders the `.error` in its own refusal channel
(`native-json-run`: a `status:error` JSON on stdout; `coverage-observations`
and `choice-trace`: their stderr line, exit 1). -/
def readInputBytes (input : FilePath) : IO (Except String ByteArray) := do
  try
    return .ok (← IO.FS.readBinFile input)
  catch err =>
    return .error s!"{input}: cannot read input: {oneLine (toString err)}"

/-- The text twin of `readInputBytes` (a TSV manifest; BUG-120). -/
def readInputText (input : FilePath) : IO (Except String String) := do
  try
    return .ok (← IO.FS.readFile input)
  catch err =>
    return .error s!"{input}: cannot read input: {oneLine (toString err)}"

/-- Write a subcommand's output file whole (a results or dump HEADER),
CATCHING the OS error: an unwritable path — a missing directory, a
permission failure, a full disk — is a refusal that names the path and the
OS cause, `<path>: cannot write output: <OS error>` (BUG-122, 2026-10-12;
release-readiness item 9), never an IO exception escaping `main` as the
runtime's uncaught-exception message. The write side of `readInputText`. -/
def writeOutputText (path : FilePath) (text : String) : IO (Except String Unit) := do
  try
    IO.FS.writeFile path text
    return .ok ()
  catch err =>
    return .error s!"{path}: cannot write output: {oneLine (toString err)}"

/-- Append lines to a subcommand's output file (a batch's per-case records),
the same catch as `writeOutputText` (BUG-122). -/
def appendOutputLines (path : FilePath) (lines : List String) : IO (Except String Unit) := do
  try
    IO.FS.withFile path .append fun h => for l in lines do h.putStrLn l
    return .ok ()
  catch err =>
    return .error s!"{path}: cannot write output: {oneLine (toString err)}"

/-- `native-json-run`'s choice report mode (F1 of the 2026-10-13 fail-closed pass). -/
inductive ChoiceReportMode where
  /-- `--no-choice-report`: nothing on stderr; the production driver exactly as before. -/
  | off
  /-- The default: the consultation COUNT read off the production run's own leftover tape (the
  tape padded with `choicePadLength` zeros) — no replay. -/
  | count
  /-- `--choice-report=full`: the count plus `choice-trace`'s accounting pass (sites, bounds, the
  driver-agreement refusal, the menu invariants) — a replay, costly on long runs. -/
  | full
  deriving Repr, BEq, DecidableEq

structure RunArgs where
  input : Option FilePath := none
  functionName : Option String := none
  /-- The entry arguments in command-line order (`--arg-int` and
  `--arg-bool` interleaved as given). -/
  args : Array EntryArg := #[]
  /-- `--seed <file.json>` (seeded-heap slice B, design §6): the `golean-seed-v1` file whose
  cells are allocated after package init and before the entry's parameters. At most once. -/
  seed : Option FilePath := none
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
  /-- `native-json-run` only: the choice report (F1 of the 2026-10-13 fail-closed pass; §2.1 of
  docs/cli.md). Default `.count` (the padded-tape count, zero replay); `--choice-report=full` the
  tracer pass; `--no-choice-report` off (the differential runner passes it — its depth guard
  accounts every strict row's consumption already). -/
  choiceReport : ChoiceReportMode := .count
  /-- Set once a choice-report flag is given (a second one is a usage error). -/
  choiceReportGiven : Bool := false
  deriving Repr

private def usage : String :=
  "usage:\n" ++
  "  golean native-json-run --input <file> --function <name> [--seed <file.json>]\n" ++
  "      [--arg-int <n> | --arg-bool <true|false> | --arg-ref <k(.f|[i])*> | --arg-nil ...] [--fuel <n>] [--choices <n,n,...>]\n" ++
  "      [--no-choice-report | --choice-report=full]  (by default a run that consulted a choice site says so on stderr: its\n" ++
  "       observation is one member of a set; =full also names the sites, replaying the run — docs/cli.md §2.1)\n" ++
  "      (entry arguments bind the parameters positionally, in command-line order; each is checked against its parameter type;\n" ++
  "       --arg-ref and --arg-nil need --seed: a reference into the seed's cells, a nil pointer — golean-seed-v1, docs/cli.md)\n" ++
  "  golean observation-eq --left <json> --right <json>\n" ++
  "  golean coverage-observations --input <file> --function <name> [--arg-int <n> | --arg-bool <true|false> ...] [--fuel <n>] [--engine dedup]\n" ++
  "      [--max-width <B>] [--max-sites <D>] [--cap <N>] [--work-cap <W>] [--expect-status <ok|panic|ok,panic|race>]
      [--allow-nonterm-iters <per-branch-loop-re-entries>] [--backedge <full|k>]\n" ++
  "      (--engine dedup reads only --work-cap and --expect-status; --fuel, --max-width, --max-sites, --cap and --backedge are refused there by name)\n" ++
  "  golean choice-trace --input <file> --function <name> [--seed <file.json>] [--arg-int <n> | --arg-bool <true|false> | --arg-ref <k(.f|[i])*> | --arg-nil ...]\n" ++
  "      [--fuel <n>] [--stream <spec>]... [--trace]\n" ++
  "  golean choice-trace --batch <manifest.tsv> --out <results.tsv> [--dump <file>] [--fuel <n>] [--skip <k>] [--take <n>]\n" ++
  "      (the labelled-consumption tracer; `golean choice-trace --help` for the stream specs and the manifest format)\n"

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
      parseRunArgs rest { cfg with args := cfg.args.push (.int (← parseJsonInt "--arg-int" value)) }
  | "--arg-bool" :: value :: rest, cfg => do
      parseRunArgs rest { cfg with args := cfg.args.push (.bool (← parseBoolLiteral value)) }
  | "--arg-ref" :: value :: rest, cfg => do
      let (k, path) ← GoLean.SeedFile.parseArgRef value
      parseRunArgs rest { cfg with args := cfg.args.push (.ref k path) }
  | "--arg-nil" :: rest, cfg =>
      parseRunArgs rest { cfg with args := cfg.args.push .nil }
  | "--seed" :: path :: rest, cfg =>
      match cfg.seed with
      | some _ => .error s!"duplicate --seed (at most one seed file)\n{usage}"
      | none => parseRunArgs rest { cfg with seed := some (FilePath.mk path) }
  | "--fuel" :: value :: rest, cfg => do
      parseRunArgs rest { cfg with fuel := (← parseJsonNat "--fuel" value) }
  | "--choices" :: value :: rest, cfg => do
      let parts := (value.splitOn ",").filter (fun s => !s.isEmpty)
      let choices ← parts.mapM (fun s => parseJsonNat "--choices" s)
      parseRunArgs rest { cfg with choices }
  | "--no-choice-report" :: rest, cfg =>
      if cfg.choiceReportGiven then .error s!"--no-choice-report: a choice-report flag was already given (at most one)\n{usage}"
      else parseRunArgs rest { cfg with choiceReport := .off, choiceReportGiven := true }
  | "--choice-report=full" :: rest, cfg =>
      if cfg.choiceReportGiven then .error s!"--choice-report=full: a choice-report flag was already given (at most one)\n{usage}"
      else parseRunArgs rest { cfg with choiceReport := .full, choiceReportGiven := true }
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

/-- The observation rendering of a value. `nameOf` reads a declared type's
key back from the program's type table (`TypeEnv.nameOf?`; C2 made
`Ty.defined` an index) for the `dynamic` field of an interface box.
`locR` renders every LOCATION the value carries (a pointer, a slice/map/
chan base): the unseeded observation passes `locJson` in `Id` (raw ids,
byte-identical to the pre-seed encoder — `goValueJson`); the seeded one
(seeded-heap slice B, design §5/D7) renders a location seed-relative or
refuses the whole observation (`seedLocJson`, in `Except`). ONE walk for
both, so the seeded shape cannot drift from the unseeded one. -/
private partial def goValueJsonWith {m : Type → Type} [Monad m] [Inhabited (m Json)]
    (nameOf : TypeIdx → Option TypeId) (locR : Loc → m Json) : GoValue → m Json
  | .unit => pure <| Json.mkObj [("tag", Json.str "unit")]
  | .bool value => pure <| Json.mkObj [("tag", Json.str "bool"), ("value", Lean.toJson value)]
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
      pure <| Json.mkObj [
        ("tag", Json.str "int"),
        ("kind", Json.str kind.name),
        ("value", Lean.toJson value)
      ]
  -- Bit patterns, never decimal strings (note §5): equality is bit-exact
  -- modulo the NaN canonicalization above; Go's shortest-representation
  -- printing stays outside the trust surface.
  | .float bits kind =>
      pure <| Json.mkObj [
        ("tag", Json.str "float"),
        ("kind", Json.str kind.name),
        ("bits", Lean.toJson (canonFloatObsBits kind bits))
      ]
  | .string value => pure <| Json.mkObj [("tag", Json.str "string"), ("bytes", Lean.toJson value.byteNats)]
  | .addr loc => locR loc
  | .nil => pure <| Json.mkObj [("tag", Json.str "nil")]
  -- Func values have NO observation (release-readiness item 22, 2026-10-12):
  -- every seam that renders a readout refuses one by name first
  -- (`readoutRefusal?` / `funcObserved?`, below), so this arm is never
  -- printed in an observation. It stays a VISIBLE non-decodable marker
  -- (the decoder has no `func` tag), never a plausible value, should a
  -- future seam bypass the refusal.
  | .funcVal fid _ =>
      pure <| Json.mkObj [("tag", Json.str "func"), ("id", Json.str fid.key)]
  | .interface dynamic value => do
      let inner ← goValueJsonWith nameOf locR value
      pure <| Json.mkObj [
        ("tag", Json.str "interface"),
        ("dynamic", Json.str (dynamic.dynamicName nameOf)),
        ("value", inner)
      ]
  | .struct typeId fields => do
      -- `reflect.Type.Name()` returns "" for any NON-DEFINED type
      -- (reflect/type.go); the canonical anonymous empty struct is the
      -- one unnamed struct TypeId the wire mints (`emptyStructName`,
      -- tools/nativefrontend/wire.go), so it renders as "" — the
      -- internal key "struct{}" leaked verbatim before (BUG-019,
      -- arc-final audit F7, 2026-08-06). Named empty structs are
      -- defined types and keep their names.
      let fs ← fields.mapM (fun (name, value) => do
        let v ← goValueJsonWith nameOf locR value
        pure <| Json.mkObj [("name", Json.str name), ("value", v)])
      pure <| Json.mkObj [
        ("tag", Json.str "struct"),
        ("typeName", Json.str (if typeId.key == "struct{}" then "" else typeId.unqualified)),
        ("fields", Json.arr fs)
      ]
  | .array values => do
      let vs ← values.mapM (goValueJsonWith nameOf locR)
      pure <| Json.mkObj [
        ("tag", Json.str "array"),
        ("values", Json.arr vs)
      ]
  | .slice value => do
      let base ← match value.base with
        | some loc => locR loc
        | none => pure Json.null
      pure <| Json.mkObj [
        ("tag", Json.str "slice"),
        ("base", base),
        ("offset", Lean.toJson value.offset),
        ("len", Lean.toJson value.len),
        ("cap", Lean.toJson value.cap)
      ]
  | .map value => do
      let base ← match value.base with
        | some loc => locR loc
        | none => pure Json.null
      pure <| Json.mkObj [
        ("tag", Json.str "map"),
        ("base", base)
      ]
  -- Channel observations mirror the map shape (reference identity). The
  -- Go harness FAILS CLOSED on a channel-typed result (reflect.Chan is
  -- an unsupported observation kind there), so a case whose OUTPUT is a
  -- raw channel is outside the differential's comparable surface — this
  -- arm keeps the machine side total and diagnosable.
  | .chan value => do
      let base ← match value.base with
        | some loc => locR loc
        | none => pure Json.null
      pure <| Json.mkObj [
        ("tag", Json.str "chan"),
        ("base", base)
      ]
  -- Sync primitive state (spec-parity slice 2): a subject RETURNING a
  -- sync struct is copy-class misuse with no Go-side counterpart shape
  -- (the harness reflects it as an opaque struct) — the tag is emitted
  -- so the mismatch is a VISIBLE red, never a false pass. No corpus
  -- case observes one; the machine-internal repr is diagnostic only.
  | .syncData p =>
      pure <| Json.mkObj [("tag", Json.str "syncData"), ("state", Json.str s!"{repr p}")]

/-- The UNSEEDED observation rendering of a value: raw location ids (`locJson`), exactly the
pre-seed encoder's output. -/
private def goValueJson (nameOf : TypeIdx → Option TypeId) (v : GoValue) : Json :=
  Id.run (goValueJsonWith nameOf (fun l => pure (locJson l)) v)

/-- The SEED-RELATIVE rendering of a location (design §5): `{"tag":"seedRef","cell":k,
"path":[…]}` when the location lies inside the seed (`seedRelative? b n` — slice A's pure
helper; `b` the seed's base, `n` its cell count), else the named refusal: a pointer that escapes
the seed (into a parameter, a result, a global or a run-allocated cell) has no seed-relative
spelling, and the WHOLE observation refuses — never a partial seed. `what` names the observed
position (`result i` / `cell k`). -/
private def seedLocJson (b n : Nat) (what : String) (l : Loc) : Except String Json :=
  match GoCore.Machine.seedRelative? b n l with
  | some (k, path) =>
      .ok <| Json.mkObj [
        ("tag", Json.str "seedRef"),
        ("cell", Lean.toJson k),
        ("path", Json.arr (path.toArray.map fun
          | .field f => Json.str f
          | .index i => Lean.toJson i))
      ]
  | none =>
      .error s!"seed readout: {what} holds a pointer outside the seed (root address {(GoCore.Loc.rootPath l).1.id}: a parameter, result, global or run-allocated cell) — not expressible seed-relative"

/-- The program OUTPUT field of every observation (stdlib slice 3,
2026-09-04): the bytes `print`/`println` wrote to fd 2, folded in step
order by the driver (`Readout.output` / the `RunResult` error path's
prefix — G-OUT). ALWAYS present, possibly empty, so the comparator is
total over every row: an old-shape observation without it fails the
exact-key decode below, never compares. The bytes are carried as a JSON
STRING, which requires valid UTF-8; bytes that are not (a program
printing a string holding raw non-UTF-8 bytes) cannot be carried
byte-exactly, so they are emitted as an OBJECT the decoder refuses BY
NAME (`output` must be a string) — the row goes red at the comparator
rather than silently comparing a lossy rendering. -/
private def outputJson (output : GoString) : Json :=
  match String.fromUTF8? (ByteArray.mk output.bytes) with
  | some s => Json.str s
  | none =>
      Json.mkObj [("invalidUtf8", Json.arr (output.bytes.map fun b => Lean.toJson b.toNat))]

private def runJson (nameOf : TypeIdx → Option TypeId) : GoLean.GoCore.Readout → Json
  | { values, output } =>
      Json.mkObj [
        ("schema", Json.str observationSchema),
        ("status", Json.str "ok"),
        ("values", Json.arr (values.map (goValueJson nameOf))),
        ("output", outputJson output)
      ]

/-- A non-`ok` observation: the stop's status and message plus the OUTPUT
PREFIX the run produced before it (G-OUT: `Obs.terminal` carries the
stderr prefix — gc's stderr carries the program's prints before the
`panic:`/`fatal error:` block, and the harness splits them the same way).
Refusal statuses carry it too (diagnostic; no oracle compares them). -/
private def errorJson (error : Stop) (output : GoString := GoString.empty) : Json :=
  Json.mkObj [
    ("schema", Json.str observationSchema),
    ("status", Json.str error.status),
    ("message", Json.str error.message),
    ("output", outputJson output)
  ]

/-- A CLI-level `status:error` observation (an unreadable file, a parse/decode refusal, a bad entry
argument or seed file — every one BEFORE any step runs; and, since the choice report (F1 of the
2026-10-13 fail-closed pass), `native-json-run`'s refusal when the consumption accounting disagrees
with the driver — the run's own observation is then withheld). Since release-readiness item 22
(2026-10-12; [USER] Mike (item 22: fix), relayed) it carries `output` like every other status: the
empty string, which is exactly what the program wrote (it never ran). Before, the key was absent,
so the strict decoder — `error` admits exactly `message, output, schema, status` — refused the
CLI's own output, and `observation-eq` could not decode it. Additive: `golean-observation-v1`
keeps its name; the decoder is unchanged. Public for the eval pins. -/
def cliErrorJson (message : String) : Json :=
  Json.mkObj [
    ("schema", Json.str observationSchema),
    ("status", Json.str "error"),
    ("message", Json.str message),
    ("output", outputJson GoString.empty)
  ]

/-- BUG-099 at the OBSERVATION seam (release-readiness item 1, 2026-10-12):
a readout value whose dynamic type is the machine's ONE synthetic
runtime-error id (`$runtime.Error`, `runtimeErrorTypeIdx`) has no
gc-correct observation — gc spells the concrete fault type
(`boundsError`, `errorString`, `*TypeAssertionError`, …) with a struct
payload, the machine `Error` with a string — so the readout REFUSES BY
NAME instead of rendering a wrong `ok` (the row
`panic-recover/recovered-runtime-error-type/observed`, a silently wrong
answer until this). The three sibling channels already refuse: the
concrete-target assert text (`typeAssertPanicMessage`, Ops.lean), the
panic print (Machine.lean) and the method set (BUG-009/BUG-053). The
search walks what an observation RENDERS with a dynamic type — interface
boxes, through struct fields and array elements; slice/map/chan bases
render as identities and carry none. -/
private def runtimeErrorObserved? (v : GoValue) : Option String :=
  match v with
  | .interface (.defined idx) inner =>
      if idx == GoCore.runtimeErrorTypeIdx then some "an interface box"
      else (runtimeErrorObserved? inner).map (fun w => s!"a boxed value: {w}")
  | .interface _ inner => runtimeErrorObserved? inner
  | .struct typeId fields =>
      fields.attach.toList.findSome? (fun ⟨(name, fv), _⟩ =>
        (runtimeErrorObserved? fv).map (fun w => s!"field {name} of {typeId.unqualified}: {w}"))
  | .array vs =>
      vs.attach.toList.findSome? (fun ⟨ev, _⟩ =>
        (runtimeErrorObserved? ev).map (fun w => s!"an array element: {w}"))
  | _ => none
termination_by v
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›
       try simp only [Prod.mk.sizeOf_spec] at this
       omega)

/-- A FUNC-TYPED position in a TYPE (release-readiness item 22, 2026-10-12; [USER] Mike ruled item 22
fixed, relayed; the refusal is [AGENT]'s decision, the static half from the pre-merge review's
MEDIUM-1/2): the positions the Go observer's `reflect` walk reaches by STATIC kind — the type
itself, array elements, the fields of a declared struct, a declared type's underlying type
(`.defined` resolved through the table, `TypeEnv.resolve`'s descent, `bound`-structural) — where
`reflect.Func` refuses, nil or not. Pointer, slice, map and chan types are leaves (their
values render as identities and the Go observer refuses those kinds itself); an interface type
is a leaf (its DYNAMIC type is checked on the value, `funcObserved?`). `.error` = the type
cannot be resolved (an unknown index, a chain longer than the table: unreachable on an
accepted program) — the caller refuses by name, never skips. -/
private def funcTypeIn? (types : GoCore.TypeEnv) (bound : Nat) (ty : GoCore.Ty) : Except String (Option String) :=
  match ty with
  | .funcType .. => .ok (some "a func type")
  | .array _ e => do
      return (← funcTypeIn? types bound e).map (fun w => s!"an array element of {w}")
  | .defined i =>
      match bound with
      | 0 => .error s!"type index {i}: the defined-type chain exceeds the table size"
      | bound + 1 =>
          match types[i]? with
          | none => .error s!"unknown type index {i} (no entry in the type table)"
          | some (name, .struct fields) =>
              fields.toList.findSomeM? (fun f => do
                return (← funcTypeIn? types bound f.typ).map
                  (fun w => s!"field {f.name} of {name.unqualified}, {w}"))
          | some (name, .defined u) => do
              return (← funcTypeIn? types bound u).map
                (fun w => s!"{name.unqualified}, declared over {w}")
          | some (_, .interfaceDef _) => .ok none
          | some (_, .opaqueDecl _) => .ok none
  | _ => .ok none
termination_by (bound, ty)

/-- A FUNC VALUE in what an observation renders (item 22; see `funcTypeIn?`): a Go func value
has no observable identity — not comparable (only to nil), no stable address, a closure's
captures invisible — and the Go observer refuses `reflect.Func` by name
(`tools/coverageharness`). So the machine refuses it by name too, at the same seam, rather than
spelling a `func` tag its own decoder refuses (the former shape: emitted under `ok`, never
decodable). The value walk is `runtimeErrorObserved?`'s — interface boxes, struct fields, array
elements — and at an interface box it checks the DYNAMIC type statically (`funcTypeIn?`), so a
boxed nil func of a declared func type (`any(Fn(nil))`) or a boxed struct with a nil func field
refuses exactly as Go's `Elem()` walk does. Every NON-interface position is covered by the
declared result type (`readoutRefusal?` runs `funcTypeIn?` on it first), so a nil func there
refuses too. -/
private def funcObserved? (types : GoCore.TypeEnv) (v : GoValue) : Except String (Option String) :=
  match v with
  | .funcVal fid _ => .ok (some s!"a func value ({fid.key})")
  | .interface dyn inner => do
      match ← funcTypeIn? types (types.size + 1) dyn with
      | some w => return some s!"an interface box of {w}"
      | none => return (← funcObserved? types inner).map (fun w => s!"a boxed value: {w}")
  | .struct typeId fields =>
      fields.attach.toList.findSomeM? (fun ⟨(name, fv), _⟩ => do
        return (← funcObserved? types fv).map (fun w => s!"field {name} of {typeId.unqualified}: {w}"))
  | .array vs =>
      vs.attach.toList.findSomeM? (fun ⟨ev, _⟩ => do
        return (← funcObserved? types ev).map (fun w => s!"an array element: {w}"))
  | _ => .ok none
termination_by v
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›
       try simp only [Prod.mk.sizeOf_spec] at this
       omega)

/-- The named func refusal; `clause` names the position and what it has/holds. -/
private def funcRefusal (clause : String) : Stop :=
  .unsupported s!"observation of {clause}: a Go func value has no observable identity (not comparable, no stable address; the Go observer refuses reflect.Func, nil or not) — not in golean-observation-v1, refused by name at the observation seam"

/-- What a readout seam knows besides the values (item 22): the program's type table (interface
boxes render their dynamic type's key through it; `funcTypeIn?` resolves declared types in it)
and the entry function's DECLARED result types, one per readout value. Every seam has the entry
in scope (`native-json-run`, `--seed`, the enumerators, the tracer). -/
structure ObsCtx where
  types : GoCore.TypeEnv
  resultTys : Array GoCore.Ty

/-- The observation context of an entry function. -/
def ObsCtx.ofFunc (types : GoCore.TypeEnv) (f : GoCore.Func) : ObsCtx :=
  ⟨types, f.results.map (·.typ)⟩

/-- The observation context of an entry looked up by name; an unknown entry declares no result
types, so a readout with any value refuses by name in `readoutRefusal?` (the count check). -/
def ObsCtx.ofEntry (program : GoCore.Program) (functionName : String) : ObsCtx :=
  match GoCore.findFunctionIn? program.funcs ⟨functionName⟩ with
  | some f => ObsCtx.ofFunc program.typeDefs f
  | none => ⟨program.typeDefs, #[]⟩

/-- The readout's refusal, if any: BUG-099's synthetic type observed in a result (the first such
result, by position); else, per result in order, a func-typed DECLARED position (`funcTypeIn?`,
nil or not) or a func value / func-typed interface box in the value (`funcObserved?`) — item 22.
The value count must equal the declared result count; a mismatch, or a type the table cannot
resolve, refuses by name (`internal`) rather than skipping the check. -/
private def readoutRefusal? (oc : ObsCtx) (r : GoLean.GoCore.Readout) : Option Stop :=
  if oc.resultTys.size != r.values.size then
    some (.internal s!"observation: the readout has {r.values.size} result value(s) but the entry declares {oc.resultTys.size} result type(s) — the func-type check cannot be applied (refused by name, never skipped)")
  else
  let bug099 := ((List.range r.values.size).findSome? (fun i =>
      r.values[i]? >>= fun v => (runtimeErrorObserved? v).map (fun w => (i, w)))).map
    (fun (i, w) =>
      .unsupported s!"observation of result {i} names the dynamic type of a recovered runtime error ({w}), which the machine models as one synthetic id ({GoCore.runtimeErrorTypeId.key}, reserved table index {GoCore.runtimeErrorTypeIdx}) where gc has a concrete runtime type per fault (runtime.boundsError / runtime.errorString / *runtime.TypeAssertionError / …) with a struct payload — no gc-correct observation exists; BUG-099, refused by name")
  let funcAt (i : Nat) : Option Stop :=
    match r.values[i]?, oc.resultTys[i]? with
    | some v, some ty =>
        match funcTypeIn? oc.types (oc.types.size + 1) ty with
        | .error e => some (.internal s!"observation of result {i}: its declared type cannot be resolved ({e})")
        | .ok (some w) => some (funcRefusal s!"result {i}, which has {w}")
        | .ok none =>
            match funcObserved? oc.types v with
            | .error e => some (.internal s!"observation of result {i}: a boxed dynamic type cannot be resolved ({e})")
            | .ok (some w) => some (funcRefusal s!"result {i}, which holds {w}")
            | .ok none => none
    | _, _ => some (.internal s!"observation: result {i} missing")
  bug099 <|> (List.range r.values.size).findSome? funcAt

/-- The observation AND its status word for a readout, from one place: `ok`
with `runJson`, or the readout's refusal (`readoutRefusal?`: BUG-099's, or a
func-typed position — item 22; status `unsupported`) with the run's output prefix. Every seam that renders a readout goes through this, so the
status word beside an observation (the enumerators' leaf labels,
`coverage-observations`' status discipline, `native-json-run`'s exit code)
never says `ok` over a refusal. -/
private def readoutObs (oc : ObsCtx) (r : GoLean.GoCore.Readout) :
    String × Json :=
  match readoutRefusal? oc r with
  | some stop => (stop.status, errorJson stop r.output)
  | none => ("ok", runJson oc.types.nameOf? r)

/-- The status word `readoutObs` gives a readout (`ok`, or its refusal's status) — public for the
tracer, whose own loop classifies main's exit before the readout is rendered. -/
def readoutStatus (oc : ObsCtx) (r : GoLean.GoCore.Readout) : String :=
  (readoutObs oc r).1

/-- The SEEDED observation (seeded-heap slice B, design §5, D7): the readout's results and the
seed cells' FINAL values, every location rendered seed-relative over `seedRelative? b n` with
`b` the readout's own `base` and `n` its cell count (`seedLocJson`; the base rides the readout
since RE-PIN 19 — before, it was re-read from a second setup call); the `ok` observation gains
the key `seed` — one kind-carrying value per cell, in cell order. A location outside the seed
anywhere (a result or a cell) refuses the WHOLE observation, `Stop.unsupported` naming the
position (status `unsupported`); BUG-099's readout refusal applies first, exactly as unseeded.
Unseeded runs never come here (`readoutObs`, no `seed` key, byte-identical output). Public for
the eval pins. Recorded (review NIT, 2026-10-12): the rendering is computed before the BUG-099
check is consulted — pure, and only the refusal path discards it. -/
def seededObs (oc : ObsCtx) (sr : GoCore.Machine.SeededReadout) :
    String × Json :=
  let nameOf := oc.types.nameOf?
  let b := sr.base
  let n := sr.seedFinal.size
  let rendered : Except String (Array Json × Array Json) := do
    let vs ← (List.range sr.readout.values.size).toArray.mapM fun i =>
      match sr.readout.values[i]? with
      | some v => goValueJsonWith nameOf (seedLocJson b n s!"result {i}") v
      | none => .error s!"internal: result {i} missing"
    let cs ← (List.range n).toArray.mapM fun k =>
      match sr.seedFinal[k]? with
      | some v => goValueJsonWith nameOf (seedLocJson b n s!"cell {k}") v
      | none => .error s!"internal: seed cell {k} missing"
    pure (vs, cs)
  -- The seed cells' final values are observed too: a func value in a seed cell refuses by name
  -- like a func result (item 22), after the readout's own refusal. A GUARD only: no
  -- golean-seed-v1 file can place a func-typed position today (a func spelling refuses, a
  -- func-typed struct field refuses as a missing field, an `any` field takes `nil` only at
  -- pointer types), so no seed reaches it through the CLI; the eval pin drives it directly.
  let cellFunc := (List.range n).findSome? (fun k =>
    sr.seedFinal[k]? >>= fun v =>
      match funcObserved? oc.types v with
      | .error e => some (.internal s!"observation of seed cell {k}: a boxed dynamic type cannot be resolved ({e})")
      | .ok w => w.map (fun w => funcRefusal s!"seed cell {k}, which holds {w}"))
  match readoutRefusal? oc sr.readout <|> cellFunc with
  | some stop => (stop.status, errorJson stop sr.readout.output)
  | none =>
      match rendered with
      | .error msg =>
          let stop : Stop := .unsupported msg
          (stop.status, errorJson stop sr.readout.output)
      | .ok (vs, cs) =>
          ("ok", Json.mkObj [
            ("schema", Json.str observationSchema),
            ("status", Json.str "ok"),
            ("values", Json.arr vs),
            ("seed", Json.arr cs),
            ("output", outputJson sr.readout.output)
          ])

/-- The `seedRef` location (seeded-heap slice B, design §5): exact keys `cell`, `path`, `tag`;
`cell` a nat BELOW the observation's seed size, `path` an array of field names (strings) and
indices (nats). `seedN` is the observation's `seed` array size — `none` on an observation
WITHOUT a `seed` key, where a `seedRef` refuses by name (it has nothing to be relative to). -/
private def decodeSeedRef (seedN : Option Nat) (path : String) (obj : StrictJson.Obj) :
    Except String Unit := do
  let some n := seedN
    | throw s!"{path}: a seedRef location in an observation without a `seed` key (nothing to be relative to)"
  StrictJson.requireExactKeys path obj ["cell", "path", "tag"]
  let cell ← StrictJson.nat s!"{path}.cell" (← StrictJson.field path obj "cell")
  if cell ≥ n then
    throw s!"{path}.cell: {cell} out of range for a seed of {n} cell(s)"
  let elems ← StrictJson.array s!"{path}.path" (← StrictJson.field path obj "path")
  let _ ← StrictJson.mapArrayIdx elems (fun i e =>
    match e with
    | .str _ => pure ()
    | other => do
        let _ ← StrictJson.nat s!"{path}.path[{i}]" other
        pure ())
  pure ()

private partial def decodeLocObservation (seedN : Option Nat) (path : String) (json : Json) : Except String Unit := do
  let obj ← StrictJson.obj path json
  let tag ← StrictJson.string s!"{path}.tag" (← StrictJson.field path obj "tag")
  match tag with
  | "seedRef" => decodeSeedRef seedN path obj
  | "addr" =>
      StrictJson.requireExactKeys path obj ["id", "tag"]
      let _ ← StrictJson.nat s!"{path}.id" (← StrictJson.field path obj "id")
      pure ()
  | "fieldAddr" =>
      StrictJson.requireExactKeys path obj ["base", "fieldName", "tag", "typeName"]
      decodeLocObservation seedN s!"{path}.base" (← StrictJson.field path obj "base")
      let _ ← StrictJson.string s!"{path}.typeName" (← StrictJson.field path obj "typeName")
      let _ ← StrictJson.string s!"{path}.fieldName" (← StrictJson.field path obj "fieldName")
      pure ()
  | "indexAddr" =>
      StrictJson.requireExactKeys path obj ["base", "index", "tag"]
      decodeLocObservation seedN s!"{path}.base" (← StrictJson.field path obj "base")
      let _ ← StrictJson.int s!"{path}.index" (← StrictJson.field path obj "index")
      pure ()
  | other =>
      throw s!"{path}.tag: unknown location tag {repr other}"

private def decodeOptionalLoc (seedN : Option Nat) (path : String) (json : Json) : Except String Unit :=
  match json with
  | .null => pure ()
  | other => decodeLocObservation seedN path other

private partial def decodeGoValueObservation (seedN : Option Nat) (path : String) (json : Json) : Except String Unit := do
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
      -- anything else. `uintptr` is deliberately ABSENT: since BUG-124's
      -- repair (2026-10-12) the machine carries it as its own kind and
      -- `goValueJson` would spell `{"kind":"uintptr"}`, but
      -- `golean-observation-v1`'s kind set stays the ten concrete kinds
      -- ([USER] 2026-10-12, D2 = O1 of
      -- `docs/2026-10-12_uintptr-repair-design.md`): a returned uintptr
      -- is refused HERE by name — and by the Go observer first
      -- (`tools/coverageharness`, `reflect.Uintptr`) — never aliased
      -- into uint64.
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
      decodeGoValueObservation seedN s!"{path}.value" (← StrictJson.field path obj "value")
  | "addr" | "fieldAddr" | "indexAddr" | "seedRef" =>
      decodeLocObservation seedN path json
  | "struct" =>
      StrictJson.requireExactKeys path obj ["fields", "tag", "typeName"]
      let _ ← StrictJson.string s!"{path}.typeName" (← StrictJson.field path obj "typeName")
      let fields ← StrictJson.array s!"{path}.fields" (← StrictJson.field path obj "fields")
      let _ ← StrictJson.mapArrayIdx fields (fun i fieldJson => do
        let fieldObj ← StrictJson.obj s!"{path}.fields[{i}]" fieldJson
        StrictJson.requireExactKeys s!"{path}.fields[{i}]" fieldObj ["name", "value"]
        let _ ← StrictJson.string s!"{path}.fields[{i}].name" (← StrictJson.field s!"{path}.fields[{i}]" fieldObj "name")
        decodeGoValueObservation seedN s!"{path}.fields[{i}].value" (← StrictJson.field s!"{path}.fields[{i}]" fieldObj "value"))
      pure ()
  | "array" =>
      StrictJson.requireExactKeys path obj ["tag", "values"]
      let values ← StrictJson.array s!"{path}.values" (← StrictJson.field path obj "values")
      let _ ← StrictJson.mapArrayIdx values (fun i value => do
        decodeGoValueObservation seedN s!"{path}.values[{i}]" value)
      pure ()
  | "slice" =>
      StrictJson.requireExactKeys path obj ["base", "cap", "len", "offset", "tag"]
      decodeOptionalLoc seedN s!"{path}.base" (← StrictJson.field path obj "base")
      let _ ← StrictJson.nat s!"{path}.offset" (← StrictJson.field path obj "offset")
      let _ ← StrictJson.nat s!"{path}.len" (← StrictJson.field path obj "len")
      let _ ← StrictJson.nat s!"{path}.cap" (← StrictJson.field path obj "cap")
      pure ()
  | "map" =>
      StrictJson.requireExactKeys path obj ["base", "tag"]
      decodeOptionalLoc seedN s!"{path}.base" (← StrictJson.field path obj "base")
  -- No `mapData`/`chanData` arms (A3): payloads are heap CELLS, not values;
  -- neither side of the differential can emit one, so the tags are unknown
  -- here and refuse below like any other.
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
  -- `output` (stdlib slice 3): required on every status, a STRING (the
  -- encoder's invalid-UTF-8 object refuses here by name). Checked INSIDE
  -- the status arms, after the status word itself is known: an unknown
  -- status names ITSELF first (the T5 lane fixture pins that message).
  let checkOutput : Except String Unit := do
    match ← StrictJson.field path obj "output" with
    | .str _ => pure ()
    | .obj _ => throw s!"{path}.output: the program output is not valid UTF-8 — the observation JSON cannot carry it byte-exactly (refused by name, never compared lossily)"
    | _ => throw s!"{path}.output: expected a string (the program's fd-2 bytes)"
  match status with
  | "ok" =>
      -- Seeded-heap slice B (design §5): an `ok` observation carries EITHER the four keys
      -- (unseeded) OR the four plus `seed` (a `--seed` run: the cells' final values, a
      -- `seedRef` resolving into them). No other key set decodes. Recorded (review NIT,
      -- 2026-10-12): a raw `addr` inside a seed-carrying observation still decodes (lenient — the
      -- seeded encoder never emits one; a Go twin that did would compare unequal, not pass).
      let seedN ←
        if !obj.contains "seed" then do
          StrictJson.requireExactKeys path obj ["output", "schema", "status", "values"]
          pure none
        else do
          StrictJson.requireExactKeys path obj ["output", "schema", "seed", "status", "values"]
          let cells ← StrictJson.array s!"{path}.seed" (← StrictJson.field path obj "seed")
          pure (some cells.size)
      checkOutput
      let values ← StrictJson.array s!"{path}.values" (← StrictJson.field path obj "values")
      let _ ← StrictJson.mapArrayIdx values (fun i value => do
        decodeGoValueObservation seedN s!"{path}.values[{i}]" value)
      if let some _ := seedN then
        let cells ← StrictJson.array s!"{path}.seed" (← StrictJson.field path obj "seed")
        let _ ← StrictJson.mapArrayIdx cells (fun k cell => do
          decodeGoValueObservation seedN s!"{path}.seed[{k}]" cell)
      return json
  -- "fatal" (spec-parity slice 2): gc's unrecoverable runtime-throw
  -- class (`Stop.fatal` — the sync misuse fatals), message-carrying
  -- like deadlock/race.
  | "panic" | "unsupported" | "stuck" | "error" | "fuel-out" | "deadlock" | "race"
  | "fatal" =>
      StrictJson.requireExactKeys path obj ["message", "output", "schema", "status"]
      checkOutput
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

/-! ### The choice report (F1 of the 2026-10-13 fail-closed pass)

F1, verbatim: «`native-json-run` on a program with a consulted choice site answers `ok` with the
canonical member and nothing marks it». The DEFAULT report replays nothing: the run itself is made
on the given tape padded with `choicePadLength` zeros, and the count of consultations is read off
the leftover. By `Choices.consumeAt` (State.lean) a bound-≤-1 consult pops nothing and a drawn 0
selects slot 0 exactly as an exhausted tape does, so the padded run IS the unpadded run (pinned by
the eval tests over the driver; the wiring half — the variant below is the driver on the tape it is
given — is the theorem `runProgramPoolOutLeftoverM_fst`). The driver returns its leftover only when
the pool loop reaches main's exit; on a `Stop` ending there is none, and the report says so. -/

/-- The zeros appended to the tape for the count (2^20). A run consulting more reports «at least». -/
def choicePadLength : Nat := 2 ^ 20

/-- `runProgramPoolOutM`'s wiring (setup, the pool loop, the readout — the same public core
functions in the same order), also returning the pool loop's LEFTOVER tape when the loop reaches
main's exit (`none` on a `Stop` ending, where `execProgLoopOut` returns none). -/
def runProgramPoolOutLeftoverM (fuel : Nat) (program : GoCore.Program) (name : String)
    (args : Array GoValue) (choices : GoCore.Choices) :
    GoCore.Machine.RunResult × Option GoCore.Choices :=
  match GoCore.Machine.runProgramSetupM fuel program name args choices with
  | .error e => (.error (e, GoString.empty), none)
  | .ok (pctx, c₀, s₀, resultLocs, choices₁) =>
      match GoCore.Machine.execProgLoopOut pctx fuel ⟨#[.running c₀ none], s₀, 0⟩ {} choices₁ GoString.empty with
      | (out, .error e) => (.error (e, out), none)
      | (out, .ok (sF, left)) =>
          match GoCore.Machine.loadMany pctx sF resultLocs with
          | .ok vs => (.ok { values := vs.toArray, output := out }, some left)
          | .error e => (.error (e, out), some left)

/-- The variant's result IS the driver's, on the tape it is given. -/
theorem runProgramPoolOutLeftoverM_fst (fuel : Nat) (program : GoCore.Program) (name : String)
    (args : Array GoValue) (choices : GoCore.Choices) :
    (runProgramPoolOutLeftoverM fuel program name args choices).1 =
      GoCore.Machine.runProgramPoolOutM fuel program name args choices := by
  unfold runProgramPoolOutLeftoverM GoCore.Machine.runProgramPoolOutM
  rcases GoCore.Machine.runProgramSetupM fuel program name args choices with
    _ | ⟨pctx, c₀, s₀, resultLocs, choices₁⟩
  · rfl
  · dsimp only
    rcases GoCore.Machine.execProgLoopOut pctx fuel ⟨#[.running c₀ none], s₀, 0⟩ {} choices₁ GoString.empty with
      ⟨out, _ | ⟨sF, left⟩⟩
    · rfl
    · dsimp only
      rcases GoCore.Machine.loadMany pctx sF resultLocs with _ | vs <;> rfl

/-- `runProgramPoolSeededOutM`'s wiring, also returning the leftover tape (as above). -/
def runProgramPoolSeededOutLeftoverM (fuel : Nat) (program : GoCore.Program) (name : String)
    (seed : Array GoCore.Machine.SeedCell) (args : Array GoCore.Machine.SeedArg) (choices : GoCore.Choices) :
    Except (Stop × GoString) GoCore.Machine.SeededReadout × Option GoCore.Choices :=
  match GoCore.Machine.runProgramSetupSeededM fuel program name seed args choices with
  | .error e => (.error (e, GoString.empty), none)
  | .ok (pctx, c₀, s₀, resultLocs, slots, choices₁) =>
      match GoCore.Machine.seedBase slots with
      | .error e => (.error (e, GoString.empty), none)
      | .ok base =>
      match GoCore.Machine.execProgLoopOut pctx fuel ⟨#[.running c₀ none], s₀, 0⟩ {} choices₁ GoString.empty with
      | (out, .error e) => (.error (e, out), none)
      | (out, .ok (sF, left)) =>
          match GoCore.Machine.loadMany pctx sF resultLocs with
          | .error e => (.error (e, out), some left)
          | .ok vs =>
              match GoCore.Machine.loadMany pctx sF slots.toList with
              | .error e => (.error (e, out), some left)
              | .ok fs =>
                  (.ok { readout := { values := vs.toArray, output := out }, base := base,
                         seedFinal := fs.toArray }, some left)

/-- The seeded variant's result IS the seeded driver's, on the tape it is given. -/
theorem runProgramPoolSeededOutLeftoverM_fst (fuel : Nat) (program : GoCore.Program) (name : String)
    (seed : Array GoCore.Machine.SeedCell) (args : Array GoCore.Machine.SeedArg) (choices : GoCore.Choices) :
    (runProgramPoolSeededOutLeftoverM fuel program name seed args choices).1 =
      GoCore.Machine.runProgramPoolSeededOutM fuel program name seed args choices := by
  unfold runProgramPoolSeededOutLeftoverM GoCore.Machine.runProgramPoolSeededOutM
  rcases GoCore.Machine.runProgramSetupSeededM fuel program name seed args choices with
    _ | ⟨pctx, c₀, s₀, resultLocs, slots, choices₁⟩
  · rfl
  · dsimp only
    rcases GoCore.Machine.seedBase slots with _ | base
    · rfl
    · dsimp only
      rcases GoCore.Machine.execProgLoopOut pctx fuel ⟨#[.running c₀ none], s₀, 0⟩ {} choices₁ GoString.empty with
        ⟨out, _ | ⟨sF, left⟩⟩
      · rfl
      · dsimp only
        rcases GoCore.Machine.loadMany pctx sF resultLocs with _ | vs
        · rfl
        · dsimp only
          rcases GoCore.Machine.loadMany pctx sF slots.toList with _ | fs <;> rfl

/-- The consultation count read off a padded run: `given` the user's tape length; `consulted`
`given + choicePadLength − |leftover|`, exact while the leftover is non-empty (`exact`), a lower
bound otherwise. -/
structure ChoiceCount where
  given : Nat
  consulted : Nat
  exact : Bool
  deriving Repr, BEq

-- The binder is not named `given`: Lean 4.35 forbids `given` (with `requires`, `ensures`) as a
-- binder name in a `def` signature; the field keeps its name and the JSON key is unchanged.
def ChoiceCount.ofLeftover (givenLen : Nat) (leftover : GoCore.Choices) : ChoiceCount :=
  { given := givenLen, consulted := givenLen + choicePadLength - leftover.length,
    exact := !leftover.isEmpty }

/-- The statuses the enumerator certifies a set for (`coverage-observations --expect-status`). -/
def enumeratorCertifies (status : String) : Bool :=
  status == "ok" || status == "panic" || status == "race"

private def streamWords (choices : List Nat) : String :=
  "[" ++ ",".intercalate (choices.map toString) ++ "]"

/-- The default stderr line for a run that ended with `status` on the tape `choices`: `count?` is
the padded count (`none` — a `Stop` ending, no leftover). `none` = nothing to say. Public for the
eval pins. -/
def choiceCountLine (choices : List Nat) (status : String) : Option ChoiceCount → Option String
  | none =>
      let tail :=
        if enumeratorCertifies status then " (coverage-observations certifies the set)"
        else s!"; no enumerator certificate for status {status}"
      some s!"native-json-run: choice consultations not counted — the run ended with status {status}, for which the driver returns no leftover tape; if a choice site was consulted the observation is one member of a set — --choice-report=full or choice-trace counts them{tail}"
  | some c =>
      if c.consulted == 0 then none else
      let n := if c.exact then s!"consulted {c.consulted} choice site(s)"
        else s!"consulted at least {c.consulted} choice site(s) (beyond the {choicePadLength}-entry pad; --choice-report=full counts exactly)"
      let member := if choices.isEmpty then "one member" else s!"the member the stream {streamWords choices} selects"
      let cert :=
        if enumeratorCertifies status then " — see coverage-observations (the certified set) and choice-trace (the sites)"
        else s!" — no enumerator certificate for status {status}; choice-trace names the sites"
      let exhausted :=
        if !choices.isEmpty && c.consulted > c.given then
          s!" (stream exhausted at consultation #{c.given + 1}; the rest drew the canonical 0)"
        else ""
      some s!"native-json-run: {n}; the observation is {member} of a set{cert}{exhausted}"

/-- What `native-json-run` hands the full accounting pass (`--choice-report=full`): the decoded
run's inputs and the run's result (seeded: its readout projection, `(·.readout)`). -/
structure ChoiceReportInput where
  program : GoCore.Program
  functionName : String
  entryArgs : Array GoValue
  seeded? : Option (Array GoCore.Machine.SeedCell × Array GoCore.Machine.SeedArg)
  fuel : Nat
  choices : List Nat
  result : GoCore.Machine.RunResult

/-- The full pass's verdict: the tracer's count of consultations with bound ≥ 2 (`wide`) and its
line (`none` when `wide = 0`). -/
structure FullChoiceReport where
  wide : Nat
  line : Option String

/-- The full accounting pass (`--choice-report=full`). It lives in `GoLean.ChoiceTrace` (which
imports this module), so `Main` passes it in: `.error why` — the accounting disagrees with the
driver (or cannot run), and the run is REFUSED by name. -/
abbrev ChoiceReporter := ChoiceReportInput → Except String FullChoiceReport

/-- What `native-json-run` prints for a run: (stdout line, stderr line, exit code). Pure, so the
refusal path is pinned in the eval tests with a forged reporter. `.off`: the observation only.
`.count`: the observation and `choiceCountLine`. `.full`: the reporter must agree — a refusal, or
a padded count that is exact and differs from the tracer's `wide`, REFUSES the run (status
`error`, exit 1; the observation is withheld); else the tracer's line (or, when it is silent and
the run ended without a count, nothing — the tracer counted zero). -/
def choiceReportOutcome (mode : ChoiceReportMode) (reporter : ChoiceReporter)
    (input : ChoiceReportInput) (count? : Option ChoiceCount) (status : String) (obs : Json) :
    String × Option String × UInt32 :=
  let code : UInt32 := if status == "ok" then 0 else 1
  let refuse (why : String) : String × Option String × UInt32 :=
    ((cliErrorJson s!"consumption accounting disagrees with the driver (native-json-run --choice-report=full; the default report does not replay): {why}").compress, none, 1)
  match mode with
  | .off => (obs.compress, none, code)
  | .count => (obs.compress, choiceCountLine input.choices status count?, code)
  | .full =>
      match reporter input with
      | .error why => refuse why
      | .ok r =>
          match count? with
          | some c =>
              if c.exact && c.consulted != r.wide then
                refuse s!"the padded-tape count is {c.consulted}, the tracer counted {r.wide} consultation(s) with bound ≥ 2"
              else if !c.exact && r.wide < c.consulted then
                refuse s!"the padded-tape count is at least {c.consulted}, the tracer counted {r.wide}"
              else (obs.compress, r.line, code)
          | none => (obs.compress, r.line, code)

/-- Print `choiceReportOutcome`: stdout first, then (flushed) the stderr line, so the order holds
also when the two streams are merged. -/
private def emitWithChoiceReport (mode : ChoiceReportMode) (reporter : ChoiceReporter)
    (input : ChoiceReportInput) (count? : Option ChoiceCount) (status : String) (obs : Json) :
    IO UInt32 := do
  let (out, err?, code) := choiceReportOutcome mode reporter input count? status obs
  IO.println out
  if let some line := err? then
    (← IO.getStdout).flush
    IO.eprintln line
  return code

/-- The tape a run is made on: the given one, padded for the count unless the report is off. -/
private def runTape (mode : ChoiceReportMode) (choices : List Nat) : List Nat :=
  if mode == .off then choices else choices ++ List.replicate choicePadLength 0

/-- `native-json-run --seed` (seeded-heap slice B, design §6): decode the seed file against the
program's type table (`SeedFile.decodeSeedBytes` — the strict byte parse, the shape, the type
spellings; refusals are `status:error`, exit 1, before any step), check the entry arguments
(`entrySeedArgs`), run the seeded POOL entry `runProgramPoolSeededOutM` (slice A's
`SeedPool.lean`, upstream of the proofs), and print the seeded observation (`seededObs`).

The seed's base `b` (the post-init allocator bound, a RUN quantity — init may allocate, D1) is
the readout's `base` (RE-PIN 19, 2026-10-12): the core reads it off the setup's slot list once,
inside the run. Before the re-pin this driver re-ran `runProgramSetupSeededM` after the run to
read slot 0 — package init twice per seeded run (slice B's recorded debt, review LOW-2). With an
empty seed no location can be seed-relative and `b` is never consulted. -/
private def runSeeded (reporter : ChoiceReporter) (program : GoCore.Program) (input : FilePath)
    (functionName : String) (seedPath : FilePath) (cfg : RunArgs) : IO UInt32 := do
  match ← readInputBytes seedPath with
  | .error err =>
      IO.println (cliErrorJson err).compress
      return 1
  | .ok bytes =>
  match GoLean.SeedFile.decodeSeedBytes program.typeDefs bytes with
  | .error err =>
      IO.println (cliErrorJson s!"{seedPath}: {err}").compress
      return 1
  | .ok seed =>
  match entrySeedArgs program functionName seed cfg.args with
  | .error err =>
      IO.println (cliErrorJson s!"{input}: {err}").compress
      return 1
  | .ok seedArgs =>
  -- `.off`: the seeded driver itself; otherwise its leftover-returning wiring on the padded tape
  -- (`runProgramPoolSeededOutLeftoverM_fst`).
  let (res, left?) :=
    if cfg.choiceReport == .off then
      (GoCore.Machine.runProgramPoolSeededOutM cfg.fuel program functionName seed seedArgs cfg.choices, none)
    else runProgramPoolSeededOutLeftoverM cfg.fuel program functionName seed seedArgs (runTape cfg.choiceReport cfg.choices)
  let count? := left?.map (ChoiceCount.ofLeftover cfg.choices.length)
  let input : ChoiceReportInput :=
    { program, functionName, entryArgs := #[], seeded? := some (seed, seedArgs), fuel := cfg.fuel,
      choices := cfg.choices, result := res.map (·.readout) }
  match res with
  | .error (err, out) => emitWithChoiceReport cfg.choiceReport reporter input count? err.status (errorJson err out)
  | .ok sr =>
      let (status, obs) := seededObs (ObsCtx.ofEntry program functionName) sr
      emitWithChoiceReport cfg.choiceReport reporter input count? status obs

private def runNativeJsonRun (reporter : ChoiceReporter) (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  match parseRunArgs args {} with
  | .error err =>
      IO.eprintln err
      return 2
  | .ok cfg =>
      -- Seeded-heap slice B (design §3/§6): `--arg-ref`/`--arg-nil` name seed cells, so without
      -- `--seed` they are a usage error (exit 2), before any file is read.
      if cfg.seed.isNone && cfg.args.any EntryArg.needsSeed then
        IO.eprintln s!"--arg-ref/--arg-nil need --seed <file.json> (a reference names a seed cell; golean-seed-v1)\n{usage}"
        return 2
      match cfg.input, cfg.functionName with
      | some input, some functionName =>
          let input := absoluteFrom cwd input
          -- BUG-110: the production wire is parsed from its BYTES by the
          -- strict parser (GoLean/StrictJsonParse.lean): duplicate object
          -- keys, unpaired surrogate escapes and invalid UTF-8 refuse HERE,
          -- before any schema validator sees a (collapsed) object.
          -- BUG-120: a missing/unreadable wire refuses by name.
          match ← readInputBytes input with
          | .error err =>
              IO.println (cliErrorJson err).compress
              return 1
          | .ok bytes =>
          match GoLean.StrictJson.parseBytes bytes GoLean.StrictJson.wireNestingDepth with
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
                  -- (`runProgramPoolM`) — on programs that never spawn
                  -- it reaches the sequential driver's result at fuel
                  -- + `seqOpCount` (one boundary-clear pool step per
                  -- completed registry op, C5: `execProg_single_eq_execStmt`,
                  -- Multi.lean's `execProg` docstring; NOT the same
                  -- step count at the same fuel), and it is the only
                  -- driver on which `go` statements run.
                  -- Since stdlib slice 3 the whole-run result carries
                  -- the program OUTPUT on both paths (`RunResult`).
                  match cfg.seed with
                  | some seedPath => runSeeded reporter program input functionName (absoluteFrom cwd seedPath) cfg
                  | none =>
                  match entryArgValues program functionName cfg.args with
                  | .error err =>
                      IO.println (cliErrorJson s!"{input}: {err}").compress
                      return 1
                  | .ok entryArgs =>
                  -- `.off`: the driver itself; otherwise its leftover-returning wiring on the
                  -- padded tape (`runProgramPoolOutLeftoverM_fst`) — the choice report's count.
                  let (res, left?) :=
                    if cfg.choiceReport == .off then
                      (GoLean.GoCore.Machine.runProgramPoolOutM cfg.fuel program functionName entryArgs cfg.choices, none)
                    else runProgramPoolOutLeftoverM cfg.fuel program functionName entryArgs (runTape cfg.choiceReport cfg.choices)
                  let count? := left?.map (ChoiceCount.ofLeftover cfg.choices.length)
                  let rinput : ChoiceReportInput :=
                    { program, functionName, entryArgs, seeded? := none, fuel := cfg.fuel,
                      choices := cfg.choices, result := res }
                  match res with
                  | .ok result =>
                      -- BUG-099: a readout that would observe the synthetic
                      -- runtime-error type is a refusal (exit 1), never `ok`.
                      let (status, obs) := readoutObs (ObsCtx.ofEntry program functionName) result
                      emitWithChoiceReport cfg.choiceReport reporter rinput count? status obs
                  | .error (err, out) =>
                      emitWithChoiceReport cfg.choiceReport reporter rinput count? err.status (errorJson err out)
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
and `canonicalSlot0` row (State.lean — the census as code, exhaustiveness-checked;
consumption itself is under the ONE uniform rule, pop iff bound ≥ 2 — G-U),
its `stepNeeds`/`stepNeedsSeq` arm, AND its row here; the sentinel
alarm is the executable check).
The semantic core's consume sites and their accountant arms:
1. `stepMulti`'s boundary scheduling pick (Multi.lean, the slot-menu
   length at a boundary with ≥ 2 menu entries — the L1 site, stage C's
   `postOp` site at a goroutine's open post-op boundary (C5's flag), and
   stage D's `backEdge` site at the loop re-entry shapes: same
   `Choices.consumeAtE t.boundarySite` call, menu from `schedSlots`,
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
7. `applySyncOp`'s TRY-head pick (Machine.lean, `ChoiceSite.tryLock`,
   Q-TRYLOCK RULED [USER] 2026-08-31 row 5, implemented 2026-09-03:
   `tryLockWidth op pre` — 2 at an acquirable cell, 1 = no pop at a
   held one) → the `.syncStK` apply arm of both accountants (via the
   same `syncCell`/`tryLockWidth`).
8. `stepFn`'s unsequenced-operand probe pick (StepFn.lean, the
   `.panicking chain (.probeK k)` arm — `ChoiceSite.unseqPanic`, latitude
   E13 option (b) RULED [USER] 2026-09-05 relayed, lane e13-b: bound 2
   exactly there, DEFER = `.next k` / RAISE = `.panicking chain k`; a
   probe whose operand yields a value pops NOTHING — `.retV _ (.probeK
   _)` is non-consuming) → the `.panicking _ (.probeK _)` arm of both
   accountants (`stepNeeds`/`stepNeedsSeq`; the projection arm is
   `seqConsumption`'s `.panicking _ (.probeK _) ↦ some (.unseqPanic, 2)`,
   Machine.lean; the constructor + `canonicalSlot0` row are State.lean's).
   Row added at the e13-b audit fix round (R9) — the LOCKSTEP obligation
   above was owed by the commit that added the site.
9. THE ABORT's `repanicCollapse` pick (StepFn.lean's `.panicking _ .stop`
   arm and Multi.lean's `stepThread` tombstone arm, both through
   `abortConsult`/`repanicCollapseWidth` — BUG-004 item 1, landing chunk
   L3 2026-09-07, an [AGENT] extension of BUG-087's ruling SHAPE under
   R-1 ([USER] ratification — PENDING at the lane's tip, RULED [USER] 2026-09-07 at merge train round 24 by the merge sign-off (relayed by the [AGENT] coordinator; the merge-ask listed D2, D5, the BUG-087-shape extension and the C4 (c)→(a) move as the four items ratified by this sign-off)): bound 2 exactly at
   an abort whose head is a recovered entry with an EQUAL successor
   payload, COLLAPSE = ` [recovered, repanicked]` / two-line form =
   ` [recovered]`; bound 1 — no pop — at every other abort) → the
   `Config.abort?` arm of both projections (`seqConsumption`'s
   `.panicking (first :: rest) .stop ↦ some (.repanicCollapse, 2)` when
   `repanicEqualNext`, Machine.lean; `poolConsumption`'s abort arm reads
   it, Multi.lean); the sequential DFS records the panic LEAF per branch
   (the abort's step is the `panic` terminal and returns no leftover —
   the pool's does, and `abortLeftover` exposes it for `enumInitRun`).
   The constructor + `canonicalSlot0` row are State.lean's.
10. THE `unseq` SCHEDULER's pick (StepFn.lean's `stepUnseqNext`, the
   `.next (.unseqK … .pick _)` arm — `ChoiceSite.unseqNext`, the
   evaluation-order model v2.1 Stage B, 2026-09-16; the mechanism RULED
   [USER] 2026-09-16 relayed): bound = the number of READY occurrences
   (`UnseqGraph.ready`, the ONE computation `stepFn`, `Step.unseqPick` and
   the projection share) EXACTLY, a consult only at ≥ 2 → the `.next
   (.unseqK … .pick _)` arm of `seqConsumption` (Machine.lean), which both
   accountants project. Every other phase of the frame (ENTER, run, wait,
   a value head's result) is non-consuming (`stepUnseqEnter_stream`,
   `stepUnseqValue_stream`, `stepUnseqNext_consumption_none`). The
   constructor + `canonicalSlot0` row are State.lean's.
11. THE CONVERSION CAPACITY pick (Machine.lean's `applyStrictOpPick`, the
   strict apply's one stream-holding funnel — `ChoiceSite.convCap`, latitude
   R3 / the gc-verified project's b6, [USER] Mike 2026-10-07 agreed and
   approved the build, relayed; design `docs/2026-10-07_conv-cap-design.md`): at the
   apply of `[]byte(s)` / `[]rune(s)` on a string operand, bound = the member
   count of gc's measured envelope `convCapMembers kind literal len`
   (Ops.lean: 1 to 3), a consult only at ≥ 2 → the `.strict` arm of
   `seqConsumption` (`strictConsult?`, Machine.lean), which both accountants
   project; a one-member list (every literal conversion) pops nothing, and a
   non-string operand refuses ahead of the consult. The constructor +
   `canonicalSlot0` row are State.lean's.
Non-consuming by signature (no arm needed): `resumeThread`,
`spawnStep`, `commitClause`, `applyPairing`, the boundary clear,
`raceUpdate` (stage B: it folds the step's emitted `StepEvent` and
takes NO stream at all — the old consumption replication is deleted),
and —
spec-parity slice 2 — the non-TRY sync heads (`applySyncOpCore`) and
the sync wake path: the sync registry entry adds NEW BOUNDARIES to
`Config.atBoundary` (row 1's L1 bound reuses the machine's
`runnableIdxs`/`atBoundary` directly, so the accountant tracks them
with no new arm) but no consume sites of its own (the envelope
statement at `applySyncOpCore`: acquisition order among contenders is
entirely L1 latitude) — the TRY heads' site is row 7.

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
  /-- The entry arguments in command-line order (`--arg-int` and
  `--arg-bool` interleaved), checked against the entry's parameters by
  `entryArgValues` before setup — the same check and refusals as
  `native-json-run` (BUG-119, 2026-10-08; before it an out-of-range
  `--arg-int` wrapped silently and a mistyped one reached the machine). -/
  args : Array EntryArg := #[]
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
  /-- `--allow-nonterm-iters K` (stage D §5d, re-expressed 2026-10-06 —
  `docs/2026-10-06_spin-bounds.md`): per-branch budget of K LOOP
  RE-ENTRIES (`loopReentry`), with branches that take a (K+1)-th counted
  as `nonterm`, never members. Replaces `--allow-nonterm N` (a per-branch
  budget in pool STEPS, RETIRED: a refactor changing the steps per
  iteration moved every spin row's tree — C4, train r59). The step fuel
  stays the run default; its exhaustion under this accounting is a named
  refusal, never a nonterm count. -/
  allowNontermIters : Option Nat := none
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
  /-- The flags given on the command line, in order (release-readiness
  item 27, review F3 2026-10-12): the dedup path reads only `--work-cap`
  and `--expect-status`, and refuses by name the DFS flags it cannot read
  — a flag that parses but changes nothing would be a silent no-op. -/
  given : List String := []
  deriving Repr

private def parseEnumArgs : List String → EnumArgs → Except String EnumArgs
  | [], cfg => .ok cfg
  | "--input" :: path :: rest, cfg =>
      parseEnumArgs rest { cfg with input := some (FilePath.mk path) }
  | "--function" :: name :: rest, cfg =>
      parseEnumArgs rest { cfg with functionName := some name }
  | "--arg-int" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with args := cfg.args.push (.int (← parseJsonInt "--arg-int" value)) }
  | "--arg-bool" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with args := cfg.args.push (.bool (← parseBoolLiteral value)) }
  | "--fuel" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with fuel := (← parseJsonNat "--fuel" value), given := cfg.given ++ ["--fuel"] }
  | "--max-width" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with maxWidth := (← parseJsonNat "--max-width" value), given := cfg.given ++ ["--max-width"] }
  | "--max-sites" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with maxSites := (← parseJsonNat "--max-sites" value), given := cfg.given ++ ["--max-sites"] }
  | "--cap" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with cap := (← parseJsonNat "--cap" value), given := cfg.given ++ ["--cap"] }
  | "--work-cap" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with workCap := (← parseJsonNat "--work-cap" value) }
  | "--allow-nonterm-iters" :: value :: rest, cfg => do
      parseEnumArgs rest { cfg with allowNontermIters := some (← parseJsonNat "--allow-nonterm-iters" value) }
  | "--seed" :: _, _ | "--arg-ref" :: _, _ | "--arg-nil" :: _, _ =>
      -- Seeded-heap slice B (design §6, D6 — v1): the enumerator's setup is a hand MIRROR of
      -- `runProgramM`'s (`enumSetup`) and does not seed; mirroring the seeded setup is deferred.
      .error s!"coverage-observations: --seed/--arg-ref/--arg-nil are not supported here in golean-seed-v1 (seeded runs are native-json-run only — design D6; the enumerator's setup mirror does not seed)\n{usage}"
  | "--allow-nonterm" :: _ :: _, _ =>
      -- RETIRED 2026-10-06 (docs/2026-10-06_spin-bounds.md): a per-branch
      -- budget in pool STEPS moves with every step-count refactor. Refused
      -- by name, never silently re-read as the iteration budget.
      .error s!"--allow-nonterm is RETIRED (a per-branch budget in pool steps; it moved with every step-count change — C4, train r59): declare the budget in loop re-entries with --allow-nonterm-iters <K> (docs/2026-10-06_spin-bounds.md)\n{usage}"
  | "--backedge" :: value :: rest, cfg => do
      if value == "full" then
        parseEnumArgs rest { cfg with backedgeMode := some none, given := cfg.given ++ ["--backedge"] }
      else
        parseEnumArgs rest { cfg with backedgeMode := some (some (← parseJsonNat "--backedge" value)), given := cfg.given ++ ["--backedge"] }
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

private def renderStop (err : Stop) : String :=
  s!"{err.status}: {err.message}"

/-- The per-run-invariant half of the enumeration driver: subject lookup,
arity check, global seeding, and the `$pkginit` lookup/shape check — a
mirror of `runProgramM`'s pre-stream wiring (the seeding itself is the
SHARED `GoCore.Machine.seedGlobals`, which is stream-independent; the
stream-consuming phases live in `enumRunProgram`, run per stream).
Non-`private` so the driver-agreement eval tests can pin the copy
against the original (audit F5). -/
structure EnumProgram where
  /-- The run's ONE program context (B7): built by `enumSetup` from the
  decoded program, shared by setup, init, exploration and readout. -/
  ctx : GoCore.ProgramCtx
  /-- Globals-seeded initial store (pre-`$pkginit`). -/
  σ₀ : GoCore.Store
  /-- The `$pkginit` body, when the program has one — run PER STREAM
  (its choice consumption is part of the run; init slice,
  `docs/2026-08-05_init-design.md`). -/
  initBody? : Option GoCore.Stmt
  func : GoCore.Func
  args : Array GoValue
  /-- The SEED of a traced seeded run (seeded-heap slice C, 2026-10-12): the cells and the entry
  arguments `native-json-run --seed` takes, placed after init by `EnumProgram.entryStore` — the
  core's own `seedCells` then `resolveSeedArgs` at `b = σ₁.heap.size`, `runProgramSetupSeededM`'s
  two calls in its order. `none` (every unseeded program) leaves `args` the entry's values and
  every path byte-identical. Only the TRACER builds a seeded program (`choice-trace --seed`, for
  the strict lane's depth guard); `explore` and `dedupSeed` refuse one by name (the enumerator
  does not seed in v1, design D6 — the tracer's v1 refusal was engineering, [AGENT], and is
  lifted here: the ruling of 2026-10-12 «D1, D5 and the v1 refusals of the enumerator/tracer are
  engineering, [AGENT]», relayed). -/
  seeded? : Option (Array GoCore.Machine.SeedCell × Array GoCore.Machine.SeedArg) := none

/-- The subject's entry store and argument values over the post-init store `σ₁`: unseeded,
`(σ₁, ep.args)` exactly; seeded, `runProgramSetupSeededM`'s `seedCells` then `resolveSeedArgs`
(at `b = σ₁.heap.size`), the same calls in the same order — the slot list is not needed here (the
tracer does not read the seed back). -/
def EnumProgram.entryStore (ep : EnumProgram) (σ₁ : GoCore.Store) :
    Except Stop (GoCore.Store × Array GoValue) :=
  match ep.seeded? with
  | none => .ok (σ₁, ep.args)
  | some (seed, sargs) => do
      let (sS, _) ← GoCore.Machine.seedCells ep.ctx σ₁ seed
      let vals ← GoCore.Machine.resolveSeedArgs ep.ctx.types σ₁.heap.size seed ep.func.args sargs
      pure (sS, vals)

def enumSetup (program : GoCore.Program) (name : String)
    (args : Array GoValue)
    (seeded? : Option (Array GoCore.Machine.SeedCell × Array GoCore.Machine.SeedArg) := none) :
    Except Stop EnumProgram := do
  -- Pre-init step ORDER (find → arity → seed → init-shape) is shared
  -- verbatim with `runProgramM` (audit response 2026-08-05, C6:
  -- divergent orders gave divergent fail-closed errors on the
  -- arity+init-failure intersection; pinned by the driver-agreement
  -- eval test on the wrong-arity shape).
  let func ←
    match GoCore.findFunctionIn? program.funcs ⟨name⟩ with
    | some func => pure func
    | none => throw (.stuck s!"GoCore function not found: {name}")
  -- Seeded (slice C): the arity is the seed arguments' — `runProgramSetupSeededM`'s check.
  let arity := match seeded? with
    | some (_, sargs) => sargs.size
    | none => args.size
  if func.args.size != arity then
    throw (.stuck s!"expected {func.args.size} argument(s), got {arity}")
  -- Mirror of `runProgramSetupM`'s reserved-prefix check (C2 §2; audit
  -- fix R2): the same text, the same position, so the drivers agree.
  if program.typeDefs.hasReservedPrefix then pure () else
    throw (.internal s!"program type table does not lead with the two machine-reserved entries ({GoCore.emptyStructTypeId.key} at index 0, {GoCore.runtimeErrorTypeId.key} at index 1): TypeEnv.hasReservedPrefix fails on a {program.typeDefs.size}-entry table — prepend TypeEnv.reserved (C2 acceptance clause)")
  -- B7: the decoded program IS the context; the store starts empty (the
  -- same construction as `runProgramSetupM`'s — wire-neutral: no field of
  -- the wire record is read differently).
  let ctx : GoCore.ProgramCtx := ⟨program⟩
  let state : GoCore.Store := {}
  let σ₀ ← GoCore.Machine.seedGlobals ctx state program.globals
  -- Defense-in-depth behind the decoder's globaladdr bound check
  -- (audit response, C1): mirror of `runProgramM`'s post-seed assert
  -- (heap-only since B7 — the same text as the core seam's).
  if GoCore.Machine.StateWf ctx σ₀ then pure () else
    throw (.internal "seeded state ill-formed: a location in a global cell dangles beyond the allocator bound")
  let initBody? ←
    match GoCore.findFunctionIn? program.funcs GoCore.pkgInitFuncId with
    | none => pure none
    | some initF =>
        if initF.args.size != 0 || initF.results.size != 0 then
          throw (.stuck s!"malformed {GoCore.pkgInitFuncId.key}: expected no parameters and no results")
        else pure (some initF.body)
  return { ctx, σ₀, initBody?, func, args, seeded? }

/-- A pool step is a LOOP RE-ENTRY iff the goroutine it stepped
(`StepEvent.who`) was, BEFORE the step, running with its boundary flag
clear at a back-edge shape — `Config.boundarySite = .backEdge`:
`.next (.loop …)`, `.signal .cont (.loop …)`, `.next (.mapIterK …)` (the
envelope statement of `ChoiceSite.backEdge`, Multi.lean). The flag-clear
step (`.running c (some _)` → `.opDoneStrip`) is NOT one, so an iteration
counts exactly once. The spin rows' per-branch budget
(`--allow-nonterm-iters K`) is counted in these — the machine's own
iteration vocabulary, read through a public definition — rather than in
pool steps, which a refactor changing the steps per iteration moves (C4,
train r59; `docs/2026-10-06_spin-bounds.md`).
It reads only the PRE-step thread array (`threads`, i.e. `m.threads`), so a driver can capture
that array before `stepMulti` and let the step update the store in place (holding the whole
pre-step `MultiConfig` across the step forced a copy of the heap per step — quadratic on a growing
heap; measured 2026-10-13 when `native-json-run`'s choice report began running `enumPoolRun` by
default). -/
def loopReentry (threads : Array GoCore.Machine.Thread) (ev : GoCore.Machine.StepEvent) : Bool :=
  match threads[ev.who]? with
  | some (.running c none) => c.boundarySite == .backEdge
  | _ => false

/-- The stop at step-fuel 0 on a budgeted pool run: `.fuelOut` under the
plain run fuel; under the iteration accounting (`--allow-nonterm-iters K`)
the step fuel is the SAFETY NET and its exhaustion is NAMED — the
iteration bound was not the one that cut the branch — never the counted
nonterm class (fail closed: an exhausted bound is a refusal, not a pass). -/
def stepFuelStop (itersCap : Option Nat) : Stop :=
  match itersCap with
  | none => .fuelOut
  | some k => .internal s!"per-branch step fuel exhausted under the iteration accounting (--allow-nonterm-iters {k}): the step fuel, not the iteration bound, cut this branch — the declared bound is not the binding one; raise --fuel or re-examine the row (docs/2026-10-06_spin-bounds.md)"

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
Member statuses: `"ok"` (main's terminal, readout at the pinned result
locations), `"panic"` (any goroutine's unrecovered panic — the stream
is KEPT: the panic is a member), and — lane d — `"race"` (the
detector's refusal, also a member with its stream: for a racy case
EVERY enumerated path must carry it, which `--expect-status race`
enforces; under any other expectation a race member fails the status
discipline loudly). All other `Stop`s (stuck, unsupported,
internal, fuel-out, and `deadlock` — a deadlocking member still has
no membership handling) propagate and the enumeration fails loud —
CARRYING the output folded before them, exactly as `execProgLoopOut`
pairs its `Stop` with the pre-step `acc` (audit fix 2026-09-05, the
tracer's engine/enumerator comparison: a refusal's printed prefix is
part of the observation, so an error without it compared only
status + message and could not see an output divergence on any
refusal path). Returns (status, observation, leftover); non-`private`
so the driver-agreement eval tests can pin it against the originals it
mirrors (audit F5). The per-branch budget (2026-10-06): `itersCap` =
`--allow-nonterm-iters K` (none = no iteration accounting) and `iters` =
the loop re-entries taken so far (`loopReentry`); the (K+1)-th re-entry
throws `.fuelOut` with the output so far — the declared nonterm class —
while step-fuel exhaustion under a cap is `stepFuelStop`'s named stop. -/
def enumPoolRun (pctx : GoCore.ProgramCtx) (resultLocs : List Loc) (resultTys : Array GoCore.Ty)
    (itersCap : Option Nat) :
    Nat → Nat → GoCore.Machine.MultiConfig → GoCore.Machine.RaceState →
    GoCore.Choices → GoString →
    Except (Stop × GoString) (String × Json × GoCore.Choices)
  | fuel, iters, m, r, choices, acc =>
      -- `acc`: the program output folded so far (stdlib slice 3) — every
      -- member observation carries it (`execProgLoopOut`'s fold, mirrored),
      -- and so does every refusal (`execProgLoopOut`'s `(acc, throw e)`).
      if m.threads.isEmpty then
        throw (.internal "thread pool without a main goroutine", acc)
      else
        match m.panicMsg? with
        | some msg => return ("panic", errorJson (.panic msg) acc, choices)
        | none =>
            match m.mainOutcome? with
            | some σf =>
                -- THE MAIN-EXIT WINDOW (L5, BUG-044) — `execProgLoop`'s
                -- bound-2 site, mirrored: with runnable goroutines left,
                -- pick 0 exits now, pick 1 takes one more pool step.
                (match GoCore.Machine.runnableIdxs pctx m.shared m.threads with
                | [] => do
                    let vals ← (GoCore.Machine.loadMany pctx σf resultLocs).mapError (·, acc)
                    let (st, obs) := readoutObs ⟨pctx.types, resultTys⟩ { values := vals.toArray, output := acc }
                    return (st, obs, choices)
                | _ :: _ =>
                    let (pick, choices₁) :=
                      GoCore.Choices.consumeAt .l5ExitWindow 2 choices
                    if pick == 0 then do
                      let vals ← (GoCore.Machine.loadMany pctx σf resultLocs).mapError (·, acc)
                      let (st, obs) := readoutObs ⟨pctx.types, resultTys⟩ { values := vals.toArray, output := acc }
                      return (st, obs, choices₁)
                    else
                      match fuel with
                      | 0 => throw (stepFuelStop itersCap, acc)
                      | fuel + 1 => do
                          let threads₀ := m.threads
                          let (m', choices', ev) ←
                            (GoCore.Machine.stepMulti pctx m choices₁).mapError (·, acc)
                          let acc' := ev.out.foldl GoString.append acc
                          let iters' := if loopReentry threads₀ ev then iters + 1 else iters
                          match GoCore.Machine.raceUpdate ev m' r with
                          | .error .raceDetected =>
                              return ("race", errorJson .raceDetected acc', choices')
                          | .error e => throw (e, acc)
                          | .ok r' =>
                              if itersCap.any (iters' > ·) then throw (.fuelOut, acc')
                              else enumPoolRun pctx resultLocs resultTys itersCap fuel iters' m' r' choices' acc')
            | none =>
                if (GoCore.Machine.runnableIdxs pctx m.shared m.threads).isEmpty then
                  throw (.deadlock, acc)
                else
                  match fuel with
                  | 0 => throw (stepFuelStop itersCap, acc)
                  | fuel + 1 => do
                      let threads₀ := m.threads
                      let (m', choices', ev) ←
                        (GoCore.Machine.stepMulti pctx m choices).mapError (·, acc)
                      let acc' := ev.out.foldl GoString.append acc
                      let iters' := if loopReentry threads₀ ev then iters + 1 else iters
                      match GoCore.Machine.raceUpdate ev m' r with
                      | .error .raceDetected =>
                          return ("race", errorJson .raceDetected acc', choices')
                      | .error e => throw (e, acc)
                      | .ok r' =>
                          if itersCap.any (iters' > ·) then throw (.fuelOut, acc')
                          else enumPoolRun pctx resultLocs resultTys itersCap fuel iters' m' r' choices' acc'

/-- The `$pkginit` phase of an enumeration run (init slice):
`runConfig`-mirroring terminal handling, but returning the FINAL STATE
(the subject runs from it) instead of a result observation. A panic terminal is the run's
observation (a panicking initializer aborts the program before the
subject), reported with the leftover stream like any panic member. -/
def enumInitRun (pctx : GoCore.ProgramCtx) :
    Nat → GoCore.Store → GoCore.Machine.Config → GoCore.Choices →
    Except Stop (Sum (GoCore.Store × GoCore.Choices) (String × GoCore.Choices))
  | _, σ, .next .stop, choices => return .inl (σ, choices)
  | _, _, .blockedSend _ _ _, _ => throw .deadlock
  | _, _, .blockedRecv _ _ _ _ _, _ => throw .deadlock
  | _, _, .blockedSelect _ _ _, _ => throw .deadlock
  | 0, _, _, _ => throw .fuelOut
  | fuel + 1, σ, c, choices => do
      -- The init-phase print guard (stdlib slice 3): mirrors
      -- `runInitConfig` — no output fold on the sequential phase.
      if let some e := GoCore.Machine.initPrintRefusal? c then throw e
      -- THE ABORT (B4): the sequential machine raises the panic terminal
      -- at the abort step (`stepFn` at `Config.abort?`); it is the run's
      -- panic member, with the stream AFTER the abort's `repanicCollapse`
      -- consult (`abortLeftover` — the sequential step itself returns no
      -- leftover on its error path; landing chunk L3).
      match GoCore.Machine.stepFn pctx σ c choices with
      | .error (.panic msg) => return .inr (msg, GoCore.Machine.abortLeftover c choices)
      | .error e => throw e
      | .ok (c', σ', choices', _) => enumInitRun pctx fuel σ' c' choices'

/-- One whole-PROGRAM enumeration run under one stream: `$pkginit` (when
present) consumes from the stream first, then the subject entry wiring
(the `runProgramM` mirror — `bindParams`/`allocDecls`/`pinResultLocs`
are deterministic and choice-free, but the post-init STATE they extend
can differ per stream, so they run here, per stream, not in setup) and
the subject itself on the leftover. The returned leftover is the
composite run's — init sites and subject sites are all sites of the
run, which is what the explore loop's probe semantics count. A `Stop`
carries the output folded before it (`RunResult`'s shape — empty for
the setup and the sequential init phase, `runProgramPoolOutM`'s
mirror), so the tracer's driver-agreement check compares the WHOLE
refusal observation (audit fix 2026-09-05). -/
def enumRunProgram (ep : EnumProgram) (runFuel : Nat)
    (stream : GoCore.Choices) (itersCap : Option Nat := none) :
    Except (Stop × GoString) (String × Json × GoCore.Choices) := do
  let noOut {α} (r : Except Stop α) : Except (Stop × GoString) α :=
    r.mapError (·, GoString.empty)
  let (σ₁, choices₁) ←
    match ep.initBody? with
    | none => pure (ep.σ₀, stream)
    | some body =>
        -- Diagnostic errors carry the `package init:` phase marker,
        -- mirroring `runPkgInitM` (audit response 2026-08-05, C6); the
        -- panic member's message stays unmarked (Go-observable).
        match enumInitRun ep.ctx runFuel ep.σ₀
            (.exec body [] (.frame [] [] [] [] .stop GoCore.pkgInitFuncId)) stream with
        | .error e => throw (GoCore.Machine.markInitPhase e, GoString.empty)
        | .ok (.inl r) => pure r
        | .ok (.inr (msg, leftover)) => return ("panic", errorJson (.panic msg), leftover)
  -- Seeded (slice C): the seed is placed here, after init, before the bind (`entryStore`;
  -- unseeded it is `(σ₁, ep.args)` and nothing changes).
  let (σE, argVals) ← noOut (ep.entryStore σ₁)
  let (env, s₂) ← noOut (GoCore.Machine.bindParams ep.ctx [] σE ep.func.args.toList argVals.toList)
  let (frameEnv, s₃) ← noOut (GoCore.Machine.allocDecls ep.ctx env s₂ ep.func.results.toList)
  let resultLocs ← noOut (GoCore.Machine.pinResultLocs frameEnv ep.func.results.toList)
  -- The subject runs on the POOL (slice 4), mirroring `runProgramPoolM`:
  -- a fresh one-thread pool over the initialized state, race detector
  -- armed from empty.
  enumPoolRun ep.ctx resultLocs (ep.func.results.map (·.typ)) itersCap runFuel 0
    ⟨#[.running (.exec ep.func.body frameEnv (.frame [] [] [] [] .stop ep.func.id)) none], s₃, 0⟩ {}
    choices₁ GoString.empty

/-- The observation `native-json-run` prints for a driver result — public
so the driver-agreement eval tests compare the two drivers on the SAME
canonical JSON (audit F5). Since stdlib slice 3 the whole-run result is a
`RunResult` (the stop carries its output prefix). -/
def observationOfRunOut (oc : ObsCtx) :
    GoCore.Machine.RunResult → Json
  | .ok result => (readoutObs oc result).2
  | .error (err, out) => errorJson err out

/-- The `Except Stop Readout` form (the sequential drivers, which have no
output channel — their stops carry an EMPTY prefix). `nameOf` is the
program's `typeDefs.nameOf?` (interface boxes render their dynamic type's
key through it). -/
def observationOfRun (oc : ObsCtx)
    (r : Except Stop GoCore.Readout) : Json :=
  observationOfRunOut oc (r.mapError (·, GoString.empty))

/-- The member VOCABULARY the enumeration lanes emit (audit fix F5,
2026-09-04): normal readouts, unrecovered panics and the race refusal.
Since B2 `Obs` can STATE a fatal or deadlock member; the engine
(`EnumDedup.nodeObs`) and the checker (`checkNode`/`checkEdge`) refuse
them upstream, and this guard refuses BY NAME at the emit site should
either ever regress — a member outside the vocabulary must never print
as a certified observation with a status word the lanes do not declare. -/
def memberVocabularyRefusal? : GoCore.Machine.Obs → Option String
  | .ok _ => none
  | .terminal (.panic _) => none
  | .terminal .raceDetected => none
  | .terminal t =>
      some s!"certified member with terminal status `{t.status}` outside the lanes' member vocabulary (ok/panic/race): a fatal or deadlock member must be refused upstream (engine nodeObs, checker checkNode) — reaching the emit site is an engine/checker regression"

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
  /-- Branches that exhausted the per-branch ITERATION budget under an
  explicit `--allow-nonterm-iters K` (W3.2 stage D §5d; counted in loop
  re-entries since 2026-10-06, `docs/2026-10-06_spin-bounds.md`):
  COUNTED, never an observation member, never green-contributing —
  membership means "oracle observation ∈ TERMINATING members". Without
  the flag every budget exhaustion stays a loud failure (fail-closed
  default); the step fuel's exhaustion is loud under either setting. -/
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

/-- The consumption accountant (docstring above), since wave (iii) B8 a
PROJECTION of the machine's own `poolConsumption` (Multi.lean) — the
dispatch ladder is no longer mirrored here. `none` = the vector suffices
(the real `stepMulti` will draw only from it); `some b` = the step's next
draw would exceed the vector — a site of bound `b` at this position. -/
def stepNeeds (pctx : GoCore.ProgramCtx) (m : GoCore.Machine.MultiConfig) (picks : GoCore.Choices) :
    Option Nat :=
  (GoCore.Machine.poolConsumption pctx m picks).map (·.2)

/-- The SEQUENTIAL accountant for the `$pkginit` phase (one `stepFn`
step consumes at most one pick): `some b` iff this configuration's next
step draws a pick, with bound `b` — the machine's `seqConsumption`
(theorem `stepFn_consumption`), projected. -/
def stepNeedsSeq (pctx : GoCore.ProgramCtx) (σ : GoCore.Store) (c : GoCore.Machine.Config) :
    Option Nat :=
  (GoCore.Machine.seqConsumption pctx σ c).map (·.2)

/-- Exploration context (invariant across the tree). -/
structure ExpCtx where
  ep : EnumProgram
  runFuel : Nat
  width : Nat
  sites : Nat
  cap : Nat
  workCap : Nat
  expectStatus : Option (List String)
  /-- `some K` = `--allow-nonterm-iters K`: the per-branch budget in LOOP
  RE-ENTRIES (`loopReentry`), with branches taking a (K+1)-th counted into
  `EnumOutcome.nonterm` instead of failing the enumeration (stage D §5d —
  the wedge family's honest divergent branches; re-expressed from pool
  steps 2026-10-06, `docs/2026-10-06_spin-bounds.md`). `none` = the
  fail-closed default. The step fuel (`runFuel`) is never a nonterm
  accounting: its exhaustion fails loud under either setting. -/
  allowNontermIters : Option Nat := none
  /-- backEdge per-site enumeration mode (stage D §5d): `none` =
  UNDECLARED — a bound ≥ 2 backEdge consult fails loud (a row must say
  which tree it certifies); `some none` = `--backedge full`
  (exhaustive); `some (some k)` = `--backedge k` (canonical slot 0
  plus the first k anti-progress slots per occurrence; the alias
  ladder is SKIPPED at capped occurrences — a capped site's width is
  deliberately un-certified, and `backedgeCapped` prints it). -/
  backedgeMode : Option (Option Nat) := none

/-- The ENUMERATORS' readout: a readout refusal (`readoutRefusal?` — BUG-099's
synthetic runtime-error type observed in a result) is the ENUMERATION's
refusal, in the shape of a step-level `unsupported` («cannot certify the
observation set»), never a member. The member vocabulary is `ok`/`panic`/
`race`; a refusal word printed as a member under exit 0 — as happened
without `--expect-status`: the DFS recorded it as a leaf, the dedup path
listed it beside `certified=checkCert` — would certify a set the machine
cannot stand behind (the runtime lane's adversarial review, 2026-10-12,
MEDIUM). `readoutObs` stays the one rendering seam. -/
private def readoutMember (oc : ObsCtx) (r : GoLean.GoCore.Readout)
    (site : String) : Except String Json :=
  match readoutRefusal? oc r with
  | some stop =>
      .error s!"result readout refused {site} — cannot certify the observation set: {renderStop stop}"
  | none => .ok (readoutObs oc r).2

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
    match enumRunProgram ctx.ep ctx.runFuel (prefixPicks ++ [d]) ctx.allowNontermIters with
    | .error (.fuelOut, _) =>
        if ctx.allowNontermIters.isSome then
          -- The rung aliased onto a divergent branch — under the
          -- iteration accounting `enumPoolRun` throws `.fuelOut` ONLY at
          -- the (K+1)-th loop re-entry (step-fuel exhaustion is the named
          -- `stepFuelStop`, caught by the arm below) — the same class the
          -- DFS counts into `nonterm` under the explicit flag; it yields
          -- no observation, so it cannot escape the membership check
          -- either. Counted as a probe run (work accounting).
          o := { o with probes := o.probes + 1 }
        else
          throw s!"alias-guard probe {prefixPicks ++ [d]} failed: the probed member's run errored — {renderStop Stop.fuelOut}. Under a correct bound this rung aliases onto an in-bound member, so this is a member-class failure (e.g. a deadlocking or fuel-out member, which has no membership handling), NOT evidence against the computed bound {bound} (audit F15; a bound refutation is a probe OBSERVATION outside the enumerated set)"
    | .error (err, _) =>
        throw s!"alias-guard probe {prefixPicks ++ [d]} failed: the probed member's run errored — {renderStop err}. Under a correct bound this rung aliases onto an in-bound member, so this is a member-class failure (e.g. a deadlocking or fuel-out member, which has no membership handling), NOT evidence against the computed bound {bound} (audit F15; a bound refutation is a probe OBSERVATION outside the enumerated set)"
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

/-- A branch that exhausted its per-branch iteration budget under
`--allow-nonterm-iters`: counted, pruned, never a member (stage D §5d). -/
def recordNonterm (out : EnumOutcome) : Except String EnumOutcome :=
  .ok { out with nonterm := out.nonterm + 1 }

/-- The DFS's step-fuel exhaustion text: ALWAYS a loud failure (the step
fuel is never a nonterm accounting). Under `--allow-nonterm-iters` it
names the cause — the step fuel, not the declared iteration bound, cut
the branch, so the declared bound is not the binding one. -/
def stepFuelExhausted (ctx : ExpCtx) : String :=
  match ctx.allowNontermIters with
  | none => "per-path fuel exhausted (raise --fuel)"
  | some k => s!"per-path STEP fuel exhausted under the iteration accounting (--allow-nonterm-iters {k}): the step fuel, not the iteration bound, cut this branch — the declared bound is not the binding one; raise --fuel or re-examine the row (docs/2026-10-06_spin-bounds.md)"

mutual

/-- DFS over the POOL phase from a mid-run state. `path` is the picks
consumed so far, REVERSED (a snoc list); `stepPicks` the picks fed to
the in-progress pool step (reversed); `fuel` the remaining per-path
pool-step budget (the safety net); `iters` the loop re-entries taken
along this path (`loopReentry`), judged against `ctx.allowNontermIters`
at each completed step. Terminal classification mirrors `enumPoolRun`
(panic/main/deadlock before the fuel check); each completed step goes
through the REAL `stepMulti` + `raceUpdate`. -/
partial def poolDFS (ctx : ExpCtx) (out : EnumOutcome) (path : List Nat)
    (resultLocs : List Loc)
    (fuel iters : Nat) (m : GoCore.Machine.MultiConfig)
    (r : GoCore.Machine.RaceState) (acc : GoString) : Except String EnumOutcome := do
  -- `acc`: the program output folded along THIS path (stdlib slice 3) —
  -- a path-local accumulator, so two interleavings printing "ab"/"ba"
  -- are two members (the L1 latitude the membership lane enumerates).
  if out.steps + out.probes > ctx.workCap then
    .error s!"work cap exceeded after {out.steps} step(s) + {out.probes} probe(s) with subtrees still unexplored — raise --work-cap or narrow the case"
  else if m.threads.isEmpty then
    .error "thread pool without a main goroutine"
  else
    match m.panicMsg? with
    | some msg =>
        recordLeaf ctx out path "panic" (errorJson (.panic msg) acc) path.length
    | none =>
      match m.mainOutcome? with
      | some σf =>
          let exitLeaf : EnumOutcome → List Nat → Except String EnumOutcome :=
            fun o p =>
              match GoCore.Machine.loadMany ctx.ep.ctx σf resultLocs with
              | .error e =>
                  .error s!"result readout failed at a terminal: {renderStop e}"
              | .ok vals => do
                  let obs ← readoutMember (ObsCtx.ofFunc ctx.ep.ctx.types ctx.ep.func) { values := vals.toArray, output := acc }
                    s!"at a terminal under pick assignment {p.reverse}"
                  recordLeaf ctx o p "ok" obs p.length
          (match GoCore.Machine.runnableIdxs ctx.ep.ctx m.shared m.threads with
          | [] => exitLeaf out path
          | _ :: _ =>
              -- THE MAIN-EXIT WINDOW (L5, BUG-044): a bound-2 site —
              -- pick 0 exits with main's readout, pick 1 takes one more
              -- pool step (mirrors `enumPoolRun`/`execProgLoop`).
              branchSite ctx out path 2 path.length fun o b =>
                if b == 0 then exitLeaf o (b :: path)
                else
                  match fuel with
                  | 0 => .error (stepFuelExhausted ctx)
                  | fuel' + 1 =>
                      poolStepDFS ctx o (b :: path) resultLocs fuel' iters m r acc [])
      | none =>
        if (GoCore.Machine.runnableIdxs ctx.ep.ctx m.shared m.threads).isEmpty then
          .error s!"deadlock member under pick assignment {path.reverse} — deadlocking members have no membership handling (fail loud, per the design)"
        else
          match fuel with
          | 0 => .error (stepFuelExhausted ctx)
          | fuel' + 1 => poolStepDFS ctx out path resultLocs fuel' iters m r acc []

/-- Feed picks to the CURRENT pool step until the accountant says the
vector suffices, branching at each reported site; then take the step
through the real `stepMulti` + `raceUpdate`. -/
partial def poolStepDFS (ctx : ExpCtx) (out : EnumOutcome) (path : List Nat)
    (resultLocs : List Loc) (fuel iters : Nat)
    (m : GoCore.Machine.MultiConfig) (r : GoCore.Machine.RaceState)
    (acc : GoString) (stepPicks : List Nat) : Except String EnumOutcome := do
  let picks := stepPicks.reverse
  -- Is THIS consumption the boundary scheduling consult of a backEdge
  -- site? (First consumption of the step at a boundary config whose
  -- site is backEdge — the reported bound is then the slot-menu
  -- length; stage D §5d's per-site enumeration mode applies.)
  let backEdgeSched :=
    stepPicks.isEmpty &&
    (match m.threads[m.cur]? with
     | some t => t.atBoundary && t.boundarySite == .backEdge
         -- The consult CONSUMES (and the mode applies) only when the
         -- slot menu has ≥ 2 entries; at a singleton menu the step's
         -- first consumption is an ordinary data pick (e.g. the
         -- mapIter pick at a single-goroutine `.mapIterK` re-entry),
         -- which branches exhaustively as always.
         && 2 ≤ (GoCore.Machine.schedSlots ctx.ep.ctx m.shared m.threads m.cur
              t.boundarySite).length
     | none => false)
  match stepNeeds ctx.ep.ctx m picks with
  | some bound =>
      if backEdgeSched then
        match ctx.backedgeMode with
        | none =>
            .error s!"backEdge scheduling site of bound {bound} under pick assignment {path.reverse} — the row must DECLARE its back-edge tree: backedge=<k> (capped: canonical slot + k anti-progress slots per occurrence) or backedge=full (exhaustive; loop-length-exponential) — stage D §5d, never a silent prune"
        | some none =>
            branchSite ctx out path bound path.length fun o b =>
              poolStepDFS ctx o (b :: path) resultLocs fuel iters m r acc (b :: stepPicks)
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
                o ← poolStepDFS ctx o (b :: path) resultLocs fuel iters m r acc
                  (b :: stepPicks)
              return o
      else
        branchSite ctx out path bound path.length fun o b =>
          poolStepDFS ctx o (b :: path) resultLocs fuel iters m r acc (b :: stepPicks)
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
      match GoCore.Machine.stepMulti ctx.ep.ctx m (picks ++ [0]) with
      | .error e =>
          .error s!"machine step failed under pick assignment {path.reverse} — cannot certify the observation set: {renderStop e}"
      | .ok (m', leftover, ev) =>
          if leftover != [0] then
            .error s!"consumption accountant drift under {path.reverse}: sentinel-suffixed step left {leftover} (expected the sentinel alone) — the accountant {if leftover.isEmpty then "MISSED a consumption site (the machine drew the sentinel)" else "over-counted (supplied picks went unconsumed)"}; driver-copy drift, cannot certify"
          else
            -- The output fold (stdlib slice 3): this step's `out` events
            -- extend the path's accumulator (`execProgLoopOut`, mirrored).
            let acc' := ev.out.foldl GoString.append acc
            match GoCore.Machine.raceUpdate ev m' r with
            | .error .raceDetected =>
                recordLeaf ctx { out with steps := out.steps + 1 } path
                  "race" (errorJson .raceDetected acc') path.length
            | .error e =>
                .error s!"race-detector update failed: {renderStop e}"
            | .ok r' =>
                -- The per-branch ITERATION budget (2026-10-06): a loop
                -- re-entry (`loopReentry`, the pre-step config of the
                -- stepped goroutine) beyond the declared K prunes the
                -- branch into the counted nonterm class — the same
                -- bucket the step-fuel budget used to fill, now moved
                -- only by the program's own iteration count.
                let iters' := if loopReentry m.threads ev then iters + 1 else iters
                let out' := { out with steps := out.steps + 1 }
                if ctx.allowNontermIters.any (iters' > ·) then recordNonterm out'
                else poolDFS ctx out' path resultLocs fuel iters' m' r' acc'

end

/-- The per-branch subject entry (`enumRunProgram`'s wiring, per init
branch): bind params, allocate results, pin locations, seed the
one-thread pool with the detector armed. -/
partial def subjectEntry (ctx : ExpCtx) (out : EnumOutcome) (path : List Nat)
    (σ : GoCore.Store) : Except String EnumOutcome := do
  match GoCore.Machine.bindParams ctx.ep.ctx [] σ ctx.ep.func.args.toList
      ctx.ep.args.toList with
  | .error e => .error s!"subject entry failed: {renderStop e}"
  | .ok (env, s₂) =>
    match GoCore.Machine.allocDecls ctx.ep.ctx env s₂ ctx.ep.func.results.toList with
    | .error e => .error s!"subject entry failed: {renderStop e}"
    | .ok (frameEnv, s₃) =>
      match GoCore.Machine.pinResultLocs frameEnv ctx.ep.func.results.toList with
      | .error e => .error s!"subject entry failed: {renderStop e}"
      | .ok resultLocs =>
          poolDFS ctx out path resultLocs ctx.runFuel 0
            ⟨#[.running (.exec ctx.ep.func.body frameEnv (.frame [] [] [] [] .stop ctx.ep.func.id)) none], s₃, 0⟩
            {} GoString.empty

/-- DFS over the `$pkginit` phase (sequential, one pick per step at
most); on the init terminal, wire the subject entry (per branch — the
post-init state differs per path) and hand off to the pool DFS. A
panicking initializer is the run's (panic) member. -/
partial def initDFS (ctx : ExpCtx) (out : EnumOutcome) (path : List Nat)
    (fuel : Nat) (σ : GoCore.Store) (c : GoCore.Machine.Config) :
    Except String EnumOutcome := do
  if out.steps + out.probes > ctx.workCap then
    .error s!"work cap exceeded after {out.steps} step(s) + {out.probes} probe(s) with subtrees still unexplored — raise --work-cap or narrow the case"
  else
    match c with
    | .next .stop => subjectEntry ctx out path σ
    | .blockedSend _ _ _ => .error "package init deadlocked (fail loud)"
    | .blockedRecv _ _ _ _ _ => .error "package init deadlocked (fail loud)"
    | .blockedSelect _ _ _ => .error "package init deadlocked (fail loud)"
    | c =>
      match fuel with
      | 0 => .error "per-path fuel exhausted in package init (raise --fuel)"
      | fuel' + 1 =>
        -- The init-phase print guard (stdlib slice 3): mirrors
        -- `runInitConfig` — no output fold on the sequential phase.
        if let some e := GoCore.Machine.initPrintRefusal? c then
          throw s!"package init: {renderStop e}"
        match stepNeedsSeq ctx.ep.ctx σ c with
        | some bound =>
            -- Sentinel-suffixed like the pool path: the branch pick
            -- must be consumed AND nothing more (a sequential step
            -- draws at most one pick — checked, not assumed).
            branchSite ctx out path bound path.length fun o b =>
              match GoCore.Machine.stepFn ctx.ep.ctx σ c [b, 0] with
              | .error (.panic msg) =>
                  -- THE ABORT (B4): the step's panic terminal is the
                  -- path's panic member (the old `.panicked` leaf, one
                  -- step on).
                  recordLeaf ctx { o with steps := o.steps + 1 } (b :: path) "panic"
                    (errorJson (.panic msg)) (b :: path).length
              | .error e =>
                  .error s!"package init step failed under {(b :: path).reverse}: {renderStop e}"
              | .ok (c', σ', leftover, _) =>
                  if leftover != [0] then
                    .error s!"consumption accountant drift in package init under {(b :: path).reverse}: sentinel-suffixed step left {leftover} (expected the sentinel alone) — driver-copy drift"
                  else
                    initDFS ctx { o with steps := o.steps + 1 } (b :: path)
                      fuel' σ' c'
        | none =>
            -- TWO-SIDED here too (S4 audit): the sentinel must survive
            -- a step the accountant called non-consuming.
            match GoCore.Machine.stepFn ctx.ep.ctx σ c [0] with
            | .error (.panic msg) =>
                -- THE ABORT (B4): the panic member (see above).
                recordLeaf ctx { out with steps := out.steps + 1 } path "panic"
                  (errorJson (.panic msg)) path.length
            | .error e =>
                .error s!"package init failed under {path.reverse}: {renderStop (GoCore.Machine.markInitPhase e)}"
            | .ok (c', σ', leftover, _) =>
                if leftover != [0] then
                  .error s!"consumption accountant drift in package init under {path.reverse}: a step the accountant called non-consuming drew the sentinel — driver-copy drift"
                else
                  initDFS ctx { out with steps := out.steps + 1 } path fuel' σ' c'

/-- The engine's entry: explore from the seeded state (init phase when
present, then the pool subject per branch), then run the certification
check — every alias-probe observation must be a member. -/
def explore (ep : EnumProgram) (runFuel width sites cap workCap : Nat)
    (expectStatus : Option (List String))
    (allowNontermIters : Option Nat := none)
    (backedgeMode : Option (Option Nat) := none) :
    Except String EnumOutcome := do
  -- Seeded-heap slice C: the enumerator does not seed (design D6, v1); a seeded program here
  -- is a wiring defect, refused by name rather than explored unseeded.
  if ep.seeded?.isSome then
    throw "internal: explore was handed a SEEDED program — the enumerator does not seed in golean-seed-v1 (D6); only choice-trace runs seeded programs"
  -- `--allow-nonterm-iters K` is the PER-BRANCH budget, counted in loop
  -- re-entries (stage D §5d, re-expressed 2026-10-06): divergent branches
  -- are pruned-and-counted at their (K+1)-th re-entry. The run fuel stays
  -- the step SAFETY NET (never a nonterm accounting — `stepFuelExhausted`).
  let ctx : ExpCtx :=
    { ep, runFuel, width, sites, cap, workCap, expectStatus,
      allowNontermIters, backedgeMode }
  let out ←
    match ep.initBody? with
    | none => subjectEntry ctx {} [] ep.σ₀
    | some body =>
        initDFS ctx {} [] runFuel ep.σ₀
          (.exec body [] (.frame [] [] [] [] .stop GoCore.pkgInitFuncId))
  -- THE CERTIFICATION CHECK: probe observations ⊆ enumerated set.
  for pobs in out.probeObservations do
    if !out.observations.contains pobs then
      throw s!"alias guard: a probe pick ≥ the computed site bound produced an observation OUTSIDE the enumerated set — the bound accountant (or the case's width assertion) is REFUTED; cannot certify. Probe observation: {pobs.compress}"
  return out

/-- The dedup path's SEEDED POOL: the subject's entry (parameters bound,
result cells allocated, result locations pinned) as the root `MultiConfig`
with an empty detector — the one construction `runDedupObservations` and the
tests' certified-set checks (`Tests/UnseqHarness.lean`) share, so a test's
`m₀` is the CLI's `m₀` by definition, not by mirror. Factored out at Stage D
(route α); the three entry failures fold into one `Stop`. -/
def dedupSeed (ep : EnumProgram) :
    Except Stop (List Loc × GoCore.Machine.MultiConfig × GoCore.Machine.RaceState) := do
  if ep.seeded?.isSome then
    throw (.internal "dedupSeed was handed a SEEDED program — the dedup engine does not seed in golean-seed-v1 (D6)")
  let (env, s₂) ← GoCore.Machine.bindParams ep.ctx [] ep.σ₀ ep.func.args.toList ep.args.toList
  let (frameEnv, s₃) ← GoCore.Machine.allocDecls ep.ctx env s₂ ep.func.results.toList
  let resultLocs ← GoCore.Machine.pinResultLocs frameEnv ep.func.results.toList
  return (resultLocs,
    ⟨#[.running (.exec ep.func.body frameEnv (.frame [] [] [] [] .stop ep.func.id)) none], s₃, 0⟩,
    ({} : GoCore.Machine.RaceState))

/-- The dedup-engine path (POR slice, `docs/2026-08-21_w32-por-design.md`):
build the state-graph certificate (untrusted engine), run THE VERIFIED
CHECKER, and only then print the set — the printed lines are backed by
`checkCert_slowObs` (member set = `SlowObs`, the ∃-fuel ∃-stream image
of the unmodified `execProgLoop`). The theorem covers each member's
values and terminal status; the `output` key printed for every member
is `Readout`'s default, empty, honest because the ENGINE refuses output
events — outside the theorem (backlog row 53). The DFS lane's
accountant/sentinel/alias-ladder heuristics do not apply here; the
trust boundary is the checker plus the compiled-code trust every
differential artifact already carries. -/
private def dedupInertFlags : List String :=
  ["--fuel", "--max-width", "--max-sites", "--cap", "--backedge"]

def runDedupObservations (ep : EnumProgram) (cfg : EnumArgs) : IO UInt32 := do
  if ep.initBody?.isSome then
    IO.eprintln "coverage-observations: --engine dedup does not support a $pkginit phase (refused fail-closed; use the DFS engine)"
    return 1
  -- Release-readiness item 27: the DFS flags this path never reads are
  -- refused by name in `runCoverageObservations`, before any input is read.
  -- Refuse, never ignore: nonterm accounting under dedup is an open
  -- ruling (M-9) — a certificate is silent about divergent branches,
  -- so accepting the flag here would answer M-9 silently (launch
  -- audit D3-F-3; previously the flag was dropped without a word).
  if cfg.allowNontermIters.isSome then
    IO.eprintln "coverage-observations: --engine dedup does not support --allow-nonterm-iters (refused fail-closed pending the M-9 ruling; use the DFS engine)"
    return 1
  match dedupSeed ep with
  | .error e =>
      IO.eprintln s!"coverage-observations: subject entry failed: {renderStop e}"
      return 1
  | .ok (resultLocs, m₀, r₀) =>
    match EnumDedup.buildCert ep.ctx resultLocs m₀ r₀ cfg.workCap with
    | .error err =>
        IO.eprintln s!"coverage-observations: dedup engine: {err}"
        return 1
    | .ok (cert, stats) =>
      -- THE VERIFIED CHECKER — the certification boundary. A refusal
      -- here is fail-closed: engine bug, eqb fuel exhaustion, or a
      -- fragment mismatch; never a silently-narrower set.
      if !GoCore.Machine.checkCert ep.ctx GoCore.Machine.dedupNodeEqb
          resultLocs m₀ r₀ cert then
        IO.eprintln "coverage-observations: dedup certificate REFUSED by the verified checker — cannot certify (engine bug or fragment mismatch)"
        return 1
      -- The status/JSON words are the outcome grammar's own (`Terminal.status`,
      -- `errorJson` on the terminal) — byte-identical to the former per-
      -- constructor table for panic/race; fatal/deadlock members are still
      -- refused upstream (engine + checker), so no new word is emitted.
      -- BUG-099: an `.ok` member whose readout observes the synthetic
      -- runtime-error type is the ENUMERATION's refusal (`readoutMember`):
      -- never a member, never a status word beside `certified=checkCert`.
      for t in cert.members do
        if let .ok vs := t.1 then
          if let .error why := readoutMember (ObsCtx.ofFunc ep.ctx.types ep.func) { values := vs.toArray } "on a certified member" then
            IO.eprintln s!"coverage-observations: {why}"
            return 1
      let obsOf : GoCore.Machine.Obs → String × Json := fun o =>
        match o with
        | .ok vs => readoutObs (ObsCtx.ofFunc ep.ctx.types ep.func) { values := vs.toArray }
        | .terminal t => (t.status, errorJson (.terminal t))
      let statusOf : GoCore.Machine.Obs → String := fun o => (obsOf o).1
      let obsJson : GoCore.Machine.Obs → Json := fun o => (obsOf o).2
      -- The member vocabulary (audit fix F5): refuse by name before any
      -- status word is compared or printed.
      for t in cert.members do
        if let some why := memberVocabularyRefusal? t.1 then
          IO.eprintln s!"coverage-observations: {why}. Member: {(obsJson t.1).compress}"
          return 1
      -- status discipline (audit F1/F8), unchanged in meaning
      for t in cert.members do
        if cfg.expectStatus.any (fun ss => !ss.contains (statusOf t.1)) then
          IO.eprintln s!"coverage-observations: machine-side status divergence: certified member has status {statusOf t.1}, outside the case's declared status set {cfg.expectStatus.getD []} — a member Go may never realize is a machine bug. Member: {(obsJson t.1).compress}"
          return 1
      let lines := (cert.members.map (fun t => (obsJson t.1).compress)).qsort (· < ·)
      for line in lines do
        IO.println line
      IO.eprintln s!"coverage-observations: observations={cert.members.size} steps={stats.edges} probes=0 sites={stats.nodes} leaves=0 maxdepth=0 width=- engine=dedup nodes={stats.nodes} edges={stats.edges} dedupHits={stats.dedupHits} certified=checkCert"
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
          -- Release-readiness item 27 (review F3, 2026-10-12): under --engine
          -- dedup the DFS's budget flags have no reading — the certificate is
          -- about the WHOLE state graph (`EnumDedup.buildCert` takes the work
          -- budget only), so `--fuel`, `--max-width`, `--max-sites`, `--cap`
          -- and `--backedge` would parse and change nothing. A silent no-op is
          -- refused by name HERE, before any input is read: a usage error
          -- (exit 2, like --max-width 0), not a late refusal after setup (the
          -- lane's review, LOW-2).
          if cfg.engine.isSome then
            let inert := (cfg.given.filter dedupInertFlags.contains).eraseDups
            if !inert.isEmpty then
              IO.eprintln s!"coverage-observations: --engine dedup reads only --work-cap (the state-graph work budget) and --expect-status: {", ".intercalate inert} given — inapplicable to the whole-graph certificate (not a budgeted exploration), refused by name rather than ignored (release-readiness item 27)"
              return 2
          let input := absoluteFrom cwd input
          -- BUG-110: strict byte parse (see runNativeJsonRun). BUG-120: a
          -- missing/unreadable wire refuses by name.
          match ← readInputBytes input with
          | .error err =>
              IO.eprintln s!"coverage-observations: {err}"
              return 1
          | .ok bytes =>
          match GoLean.StrictJson.parseBytes bytes GoLean.StrictJson.wireNestingDepth with
          | .error err =>
              IO.eprintln s!"coverage-observations: {input}: JSON parse error: {err}"
              return 1
          | .ok json =>
              match GoLean.NativeToIR.decodeProgram json with
              | .error err =>
                  IO.eprintln s!"coverage-observations: {input}: {err}"
                  return 1
              | .ok program =>
                  -- BUG-119: the entry arguments pass `native-json-run`'s
                  -- check (`entryArgValues`) before setup — the same
                  -- command lines refuse with the same causes.
                  match entryArgValues program functionName cfg.args with
                  | .error err =>
                      IO.eprintln s!"coverage-observations: {input}: {err}"
                      return 1
                  | .ok entryArgs =>
                  match enumSetup program functionName entryArgs with
                  | .error err =>
                      IO.eprintln s!"coverage-observations: setup failed: {renderStop err}"
                      return 1
                  | .ok ep =>
                      match cfg.engine with
                      | some _ => runDedupObservations ep cfg
                      | none =>
                      match explore ep cfg.fuel
                          cfg.maxWidth cfg.maxSites cfg.cap cfg.workCap
                          cfg.expectStatus cfg.allowNontermIters
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
                            match cfg.allowNontermIters with
                            | none => ""
                            | some k => s!" allow-nonterm-iters={k} nonterm={out.nonterm}"
                          IO.eprintln s!"coverage-observations: observations={out.observations.size} steps={out.steps} probes={out.probes} sites={out.sitesSeen} leaves={out.leaves} maxdepth={out.maxDepth} width={cfg.maxWidth}{modeStr}{ntStr}"
                          return 0
      | _, _ =>
          IO.eprintln s!"provide --input <file> and --function <name>\n{usage}"
          return 2

/-- The CLI's subcommands. `reporter` is `native-json-run`'s consumption-accounting pass (F1 of the
2026-10-13 fail-closed pass) — `GoLean.ChoiceTrace.consumptionReport`, passed in by `Main` because
that module imports this one. -/
def main (reporter : ChoiceReporter) (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] | ["-h"] =>
      IO.println usage
      return 0
  | "native-json-run" :: rest => runNativeJsonRun reporter rest
  | "observation-eq" :: rest => runObservationEq rest
  | "coverage-observations" :: rest => runCoverageObservations rest
  | [] =>
      IO.println usage
      return 0
  | cmd :: _ =>
      IO.eprintln s!"unknown command: {cmd}\n{usage}"
      return 2

end GoLean.CLI
