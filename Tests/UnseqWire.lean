import GoLean.CLI
import Tests.UnseqHarness

/-! # Hand-built `unseq` WIRES through the strict byte parser, the decoder and the enumerator (Stage C, C1)

Check (b) of the evaluation-order model v2.1 §2 — «MACHINE EQUALS REFERENCE over
the WIRE» — on the six spike witnesses (W1–W6) and R1 / R2a–c / R4 / R6
(`docs/evidence/2026-09-16_eval-order-v2-spike/outcomes.txt`): every fixture under
`Tests/unseq-wire/` is a wire file whose `unseq` node was written BY HAND
(`Tests/unseq-wire/build.py`; the surrounding program — lifted closures, `main`,
the envelope — is the real frontend's), read from its BYTES by
`StrictJson.parseBytes`, decoded by `NativeToIR.decodeProgram` (the `unseq` arm,
design `docs/2026-09-19_unseq-stage-c-design.md` §5) and enumerated over ALL tapes
by the same `CLI.enumSetup` → `CLI.explore` path the corpus uses; the projected
observation set must equal the reference set EXACTLY. The negative variants
(`r1-reduced`, `r2b-entry`, `r6-fused`) decode and give the reference's REFUTED /
NARROWED sets — the exact-set check names an edge mutation the decoder cannot.
The one-edit MUTANTS (`mut-*.json`, needles in `mutants.tsv`) must be refused BY
NAME by the decoder; `scripts/check-unseq-wire` drives the same files through the
real CLI binary. -/

namespace Tests.UnseqWire

open GoLean GoCore Tests.UnseqScheduler

def fixtureDir : String := "Tests/unseq-wire"

/-- Parse a wire file from its BYTES (the production path: duplicate keys,
surrogates and invalid UTF-8 refuse in the byte parser) and decode it. -/
def loadWire (file : String) : IO (Except String Program) := do
  let bytes ← IO.FS.readBinFile s!"{fixtureDir}/{file}"
  match StrictJson.parseBytes bytes StrictJson.wireNestingDepth with
  | .error e => return .error s!"JSON parse error: {e}"
  | .ok json => return NativeToIR.decodeProgram json

def wireSet (name file fn : String) (expected : List Member) (width : Nat := 8) : IO Bool := do
  match ← loadWire file with
  | .error e => fail s!"{name}: {file} did not decode: {e}"
  | .ok p => expectSet name p fn expected width

def wireRefusal (name file needle : String) : IO Bool := do
  match ← loadWire file with
  | .error e =>
      if (e.splitOn needle).length > 1 then ok s!"{name}: refused by name ({needle})"
      else fail s!"{name}: refused without naming {repr needle}: {e}"
  | .ok _ => fail s!"{name}: {file} decoded; expected the refusal {repr needle}"

/-- The mutants and their needles, from the generated `mutants.tsv`. -/
def readMutants : IO (List (String × String)) := do
  let text ← IO.FS.readFile s!"{fixtureDir}/mutants.tsv"
  let rows := text.splitOn "\n" |>.filter (fun l => !l.isEmpty && !l.startsWith "#")
  return rows.filterMap fun l =>
    match l.splitOn "\t" with
    | [m, needle] => some (m, needle)
    | _ => none

def main (_args : List String) : IO Unit := do
  let checks : List (IO Bool) := [
    wireSet "W1 wire: v := mut() + a" "w1.json" "w1" [okZ 1, okZ 2],
    wireSet "W2 wire: v := a[b[0]] + mut()" "w2.json" "w2" [okZ 10, okZ 30, okZ 40],
    wireSet "W3 wire: a[i] += mut()" "w3.json" "w3" [okOut "w3 11 20\n", okOut "w3 10 21\n"],
    wireSet "W4 wire: _ = a[1] + b[2] both nil" "w4.json" "w4" [panicOut (oob 1 0), panicOut (oob 2 0)],
    wireSet "W5 wire: loop, stale binders impossible" "w5.json" "w5" [panicOut (oob 0 0) "", panicOut (oob 0 0) "7\n"],
    wireSet "W6 wire: v := x + inc() + inc()" "w6.json" "w6" [okZ 0, okZ 1, okZ 2],
    wireSet "R1 wire: x + y + mut(), unreduced" "r1.json" "r1" [okZ 0, okZ 1, okZ 2, okZ 3],
    wireSet "R1 wire REDUCED (read y after read x): loses 1 — the refuted reduction as a NEGATIVE" "r1-reduced.json" "r1" [okZ 0, okZ 2, okZ 3],
    wireSet "R2a wire z=true" "r2a.json" "r2aTrue" [okOut "guard k\nguard result true 7\n"],
    wireSet "R2a wire z=false" "r2a.json" "r2aFalse" [okOut "guard h\nguard k\nguard result true 7\n"],
    wireRefusal "R2a INVALID join (sinkB reads the region-confined $u1): refused by the decoder, statically" "r2a-invalid-join.json" "invalid branch join",
    wireSet "R2b wire, E1 anchored at the COMPLETION" "r2b.json" "r2b" [okOut "logical false 0\n"],
    wireSet "R2b wire anchored at the guard ENTRY (refuted): a lexical-edge mutation the exact-set check names" "r2b-entry.json" "r2b" [okOut "logical false 0\n", okOut "logical true 0\n"],
    wireSet "R2c wire b=true" "r2c.json" "r2cTrue" [okOut "g\nk\nsink 1 true 7\n", okOut "g\nh\nk\nsink 1 true 7\n"],
    wireSet "R2c wire b=false" "r2c.json" "r2cFalse" [okOut "g\nk\nsink 1 true 7\n", okOut "g\nk\nsink 1 false 7\n"],
    wireSet "R4 wire: old := a; a[0] += mut() (mut rebinds a)" "r4.json" "r4" [okOut "old 11 20\na 100 200\n", okOut "old 10 20\na 101 200\n"],
    wireSet "R6 wire SPLIT" "r6.json" "r6" [okZ 10, okZ 20],
    wireSet "R6 wire FUSED (the narrowing): a data-edge mutation the exact-set check names" "r6-fused.json" "r6" [okZ 20],
    -- THE FRONTEND'S OWN LOWERING (C2): source → actual frontend bytes → strict decoder →
    -- machine → EXACT reference sets (v2.1 §7 row C's exit; the graphs are the emitter's,
    -- not hand-built — the same reference sets as the hand-built wires above).
    wireSet "NATIVE W1" "native-w1.json" "w1" [okZ 1, okZ 2],
    wireSet "NATIVE W2" "native-w2.json" "w2" [okZ 10, okZ 30, okZ 40] 3,
    wireSet "NATIVE W3" "native-w3.json" "w3" [okOut "w3 11 20\n", okOut "w3 10 21\n"],
    wireSet "NATIVE W5" "native-w5.json" "w5" [panicOut (oob 0 0) "", panicOut (oob 0 0) "7\n"],
    wireSet "NATIVE W6" "native-w6.json" "w6" [okZ 0, okZ 1, okZ 2],
    wireSet "NATIVE R1" "native-r1.json" "r1" [okZ 0, okZ 1, okZ 2, okZ 3] 3,
    wireSet "NATIVE R2a z=true" "native-r2a.json" "r2aTrue" [okOut "guard k\nguard result true 7\n"],
    wireSet "NATIVE R2a z=false" "native-r2a.json" "r2aFalse" [okOut "guard h\nguard k\nguard result true 7\n"],
    wireSet "NATIVE R2b" "native-r2b.json" "r2b" [okOut "logical false 0\n"],
    wireSet "NATIVE R2c b=true" "native-r2c.json" "r2cTrue" [okOut "g\nk\nsink 1 true 7\n", okOut "g\nh\nk\nsink 1 true 7\n"],
    wireSet "NATIVE R2c b=false" "native-r2c.json" "r2cFalse" [okOut "g\nk\nsink 1 true 7\n", okOut "g\nk\nsink 1 false 7\n"],
    wireSet "NATIVE R4" "native-r4.json" "r4" [okOut "old 11 20\na 100 200\n", okOut "old 10 20\na 101 200\n"],
    wireSet "NATIVE R6" "native-r6.json" "r6" [okZ 10, okZ 20],
    -- EDGE MUTATIONS of the LOWERED graphs (v2.1 §8): each decodes; the exact-set check
    -- names the changed set (the decoder cannot see a missing or wrong edge).
    wireSet "EDGE data (R6: the access reads the variable's header, not the frozen slot) → the fused {20}" "edge-data.json" "r6" [okZ 20],
    wireSet "EDGE lexical (R2b: change() anchored at the guard entry) → {false, true}" "edge-lexical.json" "r2b" [okOut "logical false 0\n", okOut "logical true 0\n"],
    wireSet "EDGE guard (R2a z=true: h taken out of its region) → h runs unconditionally, unordered vs k AND vs sinkB" "edge-guard.json" "r2aTrue"
      [okOut "guard h\nguard k\nguard result true 7\n", okOut "guard k\nguard h\nguard result true 7\n",
       okOut "guard k\nguard result true 7\nguard h\n"],
    wireSet "EDGE phase (W3: the store writes the loaded value, the op never reaches the store) → {w3 10 20}" "edge-phase.json" "w3" [okOut "w3 10 20\n"]]
  let mutantsL ← readMutants
  let mutantChecks : List (IO Bool) := mutantsL.map fun (m, needle) =>
    wireRefusal s!"mutant {m}" s!"{m}.json" needle
  let mut failuresN := 0
  for c in checks ++ mutantChecks do
    if !(← c) then failuresN := failuresN + 1
  if mutantsL.length < 15 then
    IO.eprintln s!"Unseq wire (Stage C): FAIL — only {mutantsL.length} mutant(s) listed in mutants.tsv (expected ≥ 15)"
    IO.Process.exit 1
  if failuresN == 0 then IO.println s!"Unseq wire (Stage C): PASS — every reference set exact over the wire, {mutantsL.length} mutants refused by name"
  else
    IO.eprintln s!"Unseq wire (Stage C): FAIL — {failuresN} check(s) failed"
    IO.Process.exit 1

end Tests.UnseqWire

def main := Tests.UnseqWire.main
