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
real CLI binary. The Stage C audit fix round (2026-09-20) added the CONSTANT-HEAD
witnesses `cguard`/`celem`/`cstr` (audit F2: a constant copied into a cell — a
guard's test, a store's value — the frontend's own shape, which the C1 decoder
refused by name; hand-built AND native, each a singleton main's legacy path
also gives) and the mutant `mut-nested-completion-join` (audit F3: a NESTED
guard's completion binder consumed outside its enclosing region — statically
refused since D12's fix; the machine's `unproducedConsumer?` refusal stays
behind it). -/

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
    -- CONSTANT HEADS (audit fix round 2026-09-20, F2): a constant copied into a cell — the
    -- guard's test (`true && f()`), the phase-2 store's value (`a[f()] = 5`, `a[f()] = "s"`);
    -- D8 admits the bare constant, D9 types it against the cell. Singletons = main's answers.
    wireSet "CGUARD wire: ok := true && f() — a constant guard test copied into a bool cell" "cguard.json" "cguard" [okZ 2],
    wireSet "CELEM wire: a[f()] = 5 — an int constant as the store's value cell (a captured: header READ unordered vs f, same value)" "celem.json" "celem"
      [{ status := "ok", values := [59], output := "f\n" }],
    wireSet "CSTR wire: a[f()] = \"s\" — a string constant as the store's value cell" "cstr.json" "cstr"
      [{ status := "ok", values := [1], output := "f\n" }],
    -- STAGE E, family E1 (2026-09-21): PACKAGE-LEVEL variables are READ occurrences — the head
    -- `deref(globaladdr)` (D8 admits the `deref` head over an atom or a globaladdr pointer); a
    -- compound target's store rides `then` through `addr(globaladdr)`. References enumerate.py
    -- E1a / E1c.
    wireSet "E1 wire: v := mut() + g — g a package-level variable mut writes" "e1.json" "e1" [okZ 1, okZ 2],
    wireSet "E1C wire: g += f() — a package-level compound target, f writes g" "e1c.json" "e1c" [okZ 2, okZ 11],
    -- STAGE E, family E2 (2026-09-21): the FROZEN target identities of v2.1 §3.4 on a POINTER and a
    -- MAP (the Stage B acceptance matrix's «map/pointer deferred to E»): `*p += mut()` with mut
    -- redirecting p, `m[1] += mut()` with mut rebinding m — the plan's pointer / map VALUE is frozen,
    -- so the load and the store hit ONE pointee / ONE map; the hybrids are not members. References
    -- enumerate.py E2e / E2f; the checksums 11100 (plan first) / 10101 (call first, gc's).
    wireSet "E2PTR wire: *p += mut(), mut redirects p — the frozen pointer VALUE" "e2ptr.json" "e2ptr" [okZ 11100, okZ 10101],
    wireSet "E2MAP wire: m[1] += mut(), mut rebinds m — the frozen map VALUE (unseqReadTarget's map arm)" "e2map.json" "e2map" [okZ 11100, okZ 10101],
    -- STAGE E, family E3 (2026-09-21): the RECEIVE as a `recv` body (the machine's own chanRecv under the
    -- sweep frame) — X3 as native Go: `x[f()] += <-ch`, f then the receive by E1, the load's `[9]` before
    -- or after the receive; the deferred witness prints len(ch). Reference enumerate.py X3 / E3c.
    wireSet "E3RECV wire: x[f()] += <-ch — the receive a `recv` occurrence after f" "e3recv.json" "e3recv"
      [panicOut (oob 9 1) "len 1\n", panicOut (oob 9 1) "len 0\n"],
    -- STAGE E, family E4 (2026-09-21): a SLICE LITERAL as an `allocate` body (the machine's own makeSlice +
    -- element store under the sweep frame; NO E1 edge — v2.1 R3) — BUG-102's shape as native Go:
    -- `[]int{s[i]}[0] + wit5()`, the payload read `s[i]` unordered against the call. Reference
    -- enumerate.py E4b/E4c.
    wireSet "E4ALLOC wire: []int{s[i]}[0] + wit5() — the slice literal an `allocate` body on the payload's cell" "e4alloc.json" "e4alloc"
      [panicOut (oob 9 1) "", panicOut (oob 9 1) "wit 5\n"],
    -- STAGE E AUDIT FIX ROUND (2026-09-21). F1: Go 1.26 `new(x)` — `*new(m()) + x + h() + g()`: m's call
    -- inside new's window, the allocate storing m's value (the first E4 cut stored the ZERO value and
    -- never ran m), x's read unordered against the calls. Reference enumerate.py E4g. F4: `string(b)`
    -- reads the backing array — an occurrence; b aliased by c, m writes c[0]. Reference E4h. F3's base:
    -- a make-slice allocate beside an observable read.
    wireSet "E4NEW wire: *new(m()) + x + h() + g() — new(x) stores m's value; x's read vs the calls" "e4new.json" "e4new"
      [{ status := "ok", values := [109], output := "m\ng\n" }, { status := "ok", values := [110], output := "m\ng\n" }],
    wireSet "E4STRB wire: println(string(b) + m()) — string([]byte) reads the backing array m's alias writes" "e4strb.json" "e4strb"
      [okOut "ab\n", okOut "zb\n"],
    wireSet "E4MAKE wire: len(make([]int, n)) + x + h() — the make-slice allocate; x's read vs h" "e4make.json" "e4make"
      [okZ 103, okZ 112],
    -- STAGE E5, family E5a (2026-09-22): the reading-(a) built-ins (RATIFIED [USER] 2026-09-22) — `append` /
    -- `copy` as `wide` bodies (the machine's own appendSlice / copySlice under the sweep frame; EFFECTFUL E1
    -- participants), `min` as a pure E1-ordered head. References enumerate.py E5a2 / E5a3 / E5a5.
    wireSet "E5APPEND wire: append(s, 3)[0] + m() — the append a wide body (in place, E1-ordered); the result read vs m" "e5append.json" "e5append" [okZ 6, okZ 15],
    wireSet "E5COPY wire: d[0] + copy(d, s) — the copy's write vs the sibling checked read" "e5copy.json" "e5copy" [okZ 2, okZ 9],
    wireSet "E5MINMAX wire: min(x, 100) + y + m() — min a pure E1-ordered head; y's read vs m" "e5minmax.json" "e5minmax" [okZ 7, okZ 16],
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
    wireSet "NATIVE CGUARD (the frontend's constant-head copy, refused at C1 — audit F2)" "native-cguard.json" "cguard" [okZ 2],
    wireSet "NATIVE CELEM" "native-celem.json" "celem" [{ status := "ok", values := [59], output := "f\n" }],
    wireSet "NATIVE CSTR" "native-cstr.json" "cstr" [{ status := "ok", values := [1], output := "f\n" }],
    wireSet "NATIVE E1 (the frontend's own lowering of a package-level read — Stage E E1)" "native-e1.json" "e1" [okZ 1, okZ 2],
    wireSet "NATIVE E1C (the frontend's own lowering of a package-level compound target)" "native-e1c.json" "e1c" [okZ 2, okZ 11],
    wireSet "NATIVE E2PTR (the frontend's own deref plan — Stage E E2)" "native-e2ptr.json" "e2ptr" [okZ 11100, okZ 10101],
    wireSet "NATIVE E2MAP (the frontend's own map-element plan)" "native-e2map.json" "e2map" [okZ 11100, okZ 10101],
    wireSet "NATIVE E2FLD (the frontend's own field-addr plan through a redirected pointer)" "native-e2fld.json" "e2fld" [okZ 11100, okZ 10101],
    wireSet "NATIVE E3RECV (the frontend's own `recv` occurrence — Stage E E3)" "native-e3recv.json" "e3recv"
      [panicOut (oob 9 1) "len 1\n", panicOut (oob 9 1) "len 0\n"],
    wireSet "NATIVE E3METHOD (a value-receiver method call: the receiver copy vs the argument call — E14)" "native-e3method.json" "e3method" [okZ 6, okZ 15],
    wireSet "NATIVE E4ALLOC (the frontend's own `allocate` occurrence — Stage E E4)" "native-e4alloc.json" "e4alloc"
      [panicOut (oob 9 1) "", panicOut (oob 9 1) "wit 5\n"],
    wireSet "NATIVE E4CONV (a conversion as a pure head: the captured string's read vs the mutating call — E12)" "native-e4conv.json" "e4conv" [okZ 98, okZ 123],
    wireSet "NATIVE E4NEW (the frontend's own new(x) lowering — audit fix round F1)" "native-e4new.json" "e4new"
      [{ status := "ok", values := [109], output := "m\ng\n" }, { status := "ok", values := [110], output := "m\ng\n" }],
    wireSet "NATIVE E4STRB (the frontend's own string([]byte) occurrence — audit fix round F4)" "native-e4strb.json" "e4strb"
      [okOut "ab\n", okOut "zb\n"],
    wireSet "NATIVE E4MAKE (the frontend's own make-slice allocate beside an observable read)" "native-e4make.json" "e4make"
      [okZ 103, okZ 112],
    wireSet "NATIVE E5APPEND (the frontend's own wide append — Stage E5 E5a)" "native-e5append.json" "e5append" [okZ 6, okZ 15],
    wireSet "NATIVE E5COPY (the frontend's own wide copy)" "native-e5copy.json" "e5copy" [okZ 2, okZ 9],
    wireSet "NATIVE E5MINMAX (the frontend's own min head, E1-ordered)" "native-e5minmax.json" "e5minmax" [okZ 7, okZ 16],
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
