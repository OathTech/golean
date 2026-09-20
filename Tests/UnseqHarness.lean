import GoLean.CLI

/-! # The `unseq` test harness — exact sets over all tapes, named refusals, single tapes

Factored out of `Tests/UnseqScheduler.lean` at Stage C (2026-09-19) so the wire
tests (`Tests/UnseqWire.lean` — hand-built WIRES through the strict byte parser,
the decoder and the same enumerator) share ONE harness with the hand-built GRAPH
tests. Nothing here is a driver of its own: `enumerate` is `CLI.enumSetup` →
`CLI.explore` (the stepwise pool explorer with the machine's own consumption
accountant and the alias-ladder certification check); `runTape` is
`CLI.enumRunProgram`. Kept in the `Tests.UnseqScheduler` namespace so the Stage B
test file reads unchanged. -/

namespace Tests.UnseqScheduler

open GoLean GoCore GoCore.Machine

/-! ## Harness -/

structure Member where
  status : String
  values : List Int := []
  output : String := ""
  /-- A substring the panic/refusal message must contain (`""` = no constraint). -/
  msgHas : String := ""
  deriving Repr, BEq

def fail (msg : String) : IO Bool := do
  IO.eprintln s!"FAIL: {msg}"
  return false

def ok (msg : String) : IO Bool := do
  IO.println s!"ok: {msg}"
  return true

/-- Project an observation JSON to (status, int values, output, message). -/
def project (j : Lean.Json) : Except String Member := do
  let status ← j.getObjValAs? String "status"
  let output ← (j.getObjValAs? String "output") <|> pure ""
  let message ← (j.getObjValAs? String "message") <|> pure ""
  let values ←
    match j.getObjVal? "values" with
    | .ok (.arr vs) => vs.toList.mapM fun v => do
        let n ← v.getObjValAs? Int "value"
        pure n
    | _ => pure []
  return { status, values, output, msgHas := message }

def memberMatches (expected actual : Member) : Bool :=
  expected.status == actual.status && expected.values == actual.values
    && expected.output == actual.output
    && (expected.msgHas == "" || (actual.msgHas.splitOn expected.msgHas).length > 1)

def enumerate (program : Program) (name : String) (width : Nat := 8) (sites : Nat := 24) :
    Except String CLI.EnumOutcome :=
  match CLI.enumSetup program name #[] with
  | .error err => .error s!"setup failed: {repr err}"
  | .ok ep => CLI.explore ep 200000 width sites 128 5000000 none

/-- The EXACT-SET assertion: the enumerated observations, projected, equal
the expected members (each expected matched by exactly one actual, and no
actual unmatched). -/
def expectSet (name : String) (program : Program) (fn : String) (expected : List Member)
    (width : Nat := 8) : IO Bool := do
  match enumerate program fn width with
  | .error msg => fail s!"{name}: enumeration failed: {msg}"
  | .ok out =>
    match out.observations.toList.mapM project with
    | .error e => fail s!"{name}: observation decode: {e}"
    | .ok actual =>
      let unmatchedExpected := expected.filter fun e => !(actual.any (memberMatches e ·))
      let unmatchedActual := actual.filter fun a => !(expected.any (memberMatches · a))
      if unmatchedExpected.isEmpty && unmatchedActual.isEmpty && actual.length == expected.length then
        ok s!"{name}: exact set of {expected.length} member(s) — leaves={out.leaves} sites={out.sitesSeen} steps={out.steps} maxDepth={out.maxDepth}"
      else
        fail s!"{name}: set mismatch — expected {repr expected}; actual {repr actual}; unmatched expected {repr unmatchedExpected}; unmatched actual {repr unmatchedActual}"

/-- A NAMED refusal of the whole enumeration (a malformed graph, an invalid
join, a blocked receive — never a member, never a stuck run). -/
def expectRefusal (name : String) (program : Program) (fn : String) (needle : String) : IO Bool := do
  match enumerate program fn with
  | .error msg =>
      if (msg.splitOn needle).length > 1 then ok s!"{name}: refused by name ({needle})"
      else fail s!"{name}: refused, but not naming {repr needle}: {msg}"
  | .ok out => fail s!"{name}: expected a named refusal ({repr needle}), got {out.observations.size} member(s)"

/-- One tape's run through the enumerator's single-run driver (the pool
mirror): (status, projected member, leftover stream). -/
def runTape (program : Program) (fn : String) (tape : List Nat) :
    Except String (Member × List Nat) :=
  match CLI.enumSetup program fn #[] with
  | .error err => .error s!"setup failed: {repr err}"
  | .ok ep =>
    match CLI.enumRunProgram ep 200000 tape with
    | .error (e, out) => .error s!"{repr e} (output {repr (String.fromUTF8! (ByteArray.mk out.bytes))})"
    | .ok (_, j, leftover) => (project j).map (·, leftover)

def expectTape (name : String) (program : Program) (fn : String) (tape : List Nat)
    (expected : Member) (leftover : Option (List Nat) := none) : IO Bool := do
  match runTape program fn tape with
  | .error e => fail s!"{name}: tape {tape} failed: {e}"
  | .ok (m, left) =>
    if !memberMatches expected m then
      fail s!"{name}: tape {tape} gave {repr m}, expected {repr expected}"
    else match leftover with
      | some l => if left == l then ok s!"{name}: tape {tape} → expected member, leftover {left}"
                  else fail s!"{name}: tape {tape} leftover {left}, expected {l}"
      | none => ok s!"{name}: tape {tape} → expected member"

def expectTapeStop (name : String) (program : Program) (fn : String) (tape : List Nat)
    (needle : String) : IO Bool := do
  match runTape program fn tape with
  | .error e =>
      if (e.splitOn needle).length > 1 then ok s!"{name}: tape {tape} stopped by name ({needle})"
      else fail s!"{name}: tape {tape} stopped without naming {repr needle}: {e}"
  | .ok (m, _) => fail s!"{name}: tape {tape} expected the stop {repr needle}, got {repr m}"

/-! ## Route α (Stage D): the certified dedup engine on the same programs

`expectDedupSet` runs the UNTRUSTED engine (`EnumDedup.buildCert`) from the
CLI's own seeded pool (`CLI.dedupSeed` — the one construction the
`--engine dedup` path uses), validates the certificate with THE VERIFIED
CHECKER (`checkCert`, unmodified; `checkCert_slowObs` is what makes an
accepted certificate the set-equality claim) and compares the certified
member set EXACTLY with the expected members. The certified vocabulary is
the readout values and the Go terminal — no output: a printing program is
REFUSED by the engine by name (`expectDedupRefusal`), never certified. -/

/-- A checker `Obs` as the harness's `Member` (int readouts; a panic's message). -/
def projectObs (o : Obs) : Member :=
  match o with
  | .ok vs => { status := "ok",
                values := vs.filterMap fun v => match v with | .int n _ => some n | _ => none }
  | .terminal t => { status := t.status, msgHas := t.message }

def expectDedupSet (name : String) (program : Program) (fn : String) (expected : List Member)
    (workCap : Nat := 5000000) : IO Bool := do
  match CLI.enumSetup program fn #[] with
  | .error err => fail s!"{name}: setup failed: {repr err}"
  | .ok ep =>
  match CLI.dedupSeed ep with
  | .error err => fail s!"{name}: seed failed: {repr err}"
  | .ok (resultLocs, m₀, r₀) =>
  match EnumDedup.buildCert ep.ctx resultLocs m₀ r₀ workCap with
  | .error e => fail s!"{name}: dedup engine refused: {e}"
  | .ok (cert, stats) =>
    if !checkCert ep.ctx dedupNodeEqb resultLocs m₀ r₀ cert then
      fail s!"{name}: certificate REFUSED by the verified checker (nodes={stats.nodes} edges={stats.edges})"
    else
      let actual := cert.members.toList.map fun t => projectObs t.1
      let unmatchedExpected := expected.filter fun e => !(actual.any (memberMatches e ·))
      let unmatchedActual := actual.filter fun a => !(expected.any (memberMatches · a))
      if unmatchedExpected.isEmpty && unmatchedActual.isEmpty && actual.length == expected.length then
        ok s!"{name}: CERTIFIED exact set of {expected.length} member(s) — nodes={stats.nodes} edges={stats.edges} dedupHits={stats.dedupHits}"
      else
        fail s!"{name}: certified set mismatch — expected {repr expected}; actual {repr actual}; unmatched expected {repr unmatchedExpected}; unmatched actual {repr unmatchedActual}"

/-- The engine's NAMED refusal (a printing step, a refused shape, the work
budget) — never a certificate. -/
def expectDedupRefusal (name : String) (program : Program) (fn : String) (needle : String)
    (workCap : Nat := 5000000) : IO Bool := do
  match CLI.enumSetup program fn #[] with
  | .error err => fail s!"{name}: setup failed: {repr err}"
  | .ok ep =>
  match CLI.dedupSeed ep with
  | .error err => fail s!"{name}: seed failed: {repr err}"
  | .ok (resultLocs, m₀, r₀) =>
  match EnumDedup.buildCert ep.ctx resultLocs m₀ r₀ workCap with
  | .error e =>
      if (e.splitOn needle).length > 1 then ok s!"{name}: dedup engine refused by name ({needle})"
      else fail s!"{name}: dedup engine refused, but not naming {repr needle}: {e}"
  | .ok (cert, _) => fail s!"{name}: expected the dedup refusal {repr needle}, got a certificate with {cert.members.size} member(s)"

def okZ (z : Int) : Member := { status := "ok", values := [z] }
def okOut (out : String) : Member := { status := "ok", output := out }
def panicOut (needle : String) (out : String := "") : Member :=
  { status := "panic", output := out, msgHas := needle }
def oob (i n : Nat) : String := s!"index out of range [{i}] with length {n}"

end Tests.UnseqScheduler
