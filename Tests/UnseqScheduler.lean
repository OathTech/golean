import GoLean.CLI

/-! # The `unseq` scheduler on hand-built graphs — the reference sets (Stage B)

Every witness of the reference enumerator
(`docs/evidence/2026-09-16_eval-order-v2-spike/{enumerate.py,outcomes.txt}`)
as a hand-built `Stmt.unseq` graph, enumerated over ALL tapes by the EXISTING
enumerator/driver path (`CLI.enumSetup` → `CLI.explore`, the stepwise pool
explorer with the machine's own consumption accountant; single tapes through
`CLI.enumRunProgram`) — never a bespoke driver — and compared EXACTLY with the
reference's member sets. Refusals are asserted BY NAME. -/

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

/-! ## Builders -/

def intP (id : String) : Param := ⟨id, .int⟩
def boolP (id : String) : Param := ⟨id, .bool⟩
def sliceP (id : String) : Param := ⟨id, .slice .int⟩
def fnTy (params : List Ty) (results : List Ty) : Ty := .funcType params results false
def pInt : Ty := .pointer .int
def pSlice : Ty := .pointer (.slice .int)

/-- `*p` for a captured pointer parameter. -/
def derefI (p : String) : Expr := .deref (.var p) .int
def derefS (p : String) : Expr := .deref (.var p) (.slice .int)
/-- `*p = e` -/
def storeP (p : String) (e : Expr) : Stmt := .assign (.addr (.var p)) e
/-- `(*ps)[i] = e` -/
def storeElem (ps : String) (i : Expr) (e : Expr) : Stmt :=
  .assign (.addr (.indexAddr (derefS ps) i)) e
def ret (r : String) (e : Expr) : Stmt := .assign (.var r) e
def println (args : List Expr) : Stmt := .print true args.toArray
def str (s : String) : Expr := .stringLit (GoString.fromLeanString s)

/-- A closure value: the lifted function plus the ADDRESSES it captures. -/
def clos (fid : String) (captures : List String) : Expr :=
  .funcVal ⟨fid⟩ (captures.map Expr.ref).toArray

/-- `make([]int, n)` then element stores. -/
def makeSlice (id : String) (elems : List Int) : List Stmt :=
  [.makeSlice (.var id) .int (.intLit elems.length) none] ++
  (elems.zipIdx.map fun (v, i) =>
    .assign (.addr (.indexAddr (.var id) (.intLit i))) (.intLit v))

def occ (name : String) (body : UnseqBody) (after : List String := [])
    (region : Option String := none) : UnseqOcc := ⟨name, body, after, region⟩

/-- `main` returning an int `z`, with locals and a body. -/
def mainInt (decls : List Param) (body : List Stmt) : Func :=
  { id := ⟨"main"⟩, args := #[], results := #[intP "z"], body := .block decls.toArray body.toArray }
def mainUnit (decls : List Param) (body : List Stmt) : Func :=
  { id := ⟨"main"⟩, args := #[], results := #[], body := .block decls.toArray body.toArray }

def okZ (z : Int) : Member := { status := "ok", values := [z] }
def okOut (out : String) : Member := { status := "ok", output := out }
def panicOut (needle : String) (out : String := "") : Member :=
  { status := "panic", output := out, msgHas := needle }
def oob (i n : Nat) : String := s!"index out of range [{i}] with length {n}"

/-! ## W1  `v := mut() + a`  → {1, 2} -/

def w1mut : Func := {
  id := ⟨"w1mut"⟩, args := #[⟨"pa", pInt⟩], results := #[intP "r"],
  body := .seqn #[storeP "pa" (.intLit 2), ret "r" (.intLit 0)] }
def w1graph : UnseqGraph := {
  cells := [intP "$m", intP "$a", intP "$op"],
  occs := [occ "E_mut" (.invoke ["$m"] (.var "mutv") []),
           occ "R_a" (.eval "$a" (.var "a")),
           occ "Op" (.eval "$op" (.add (.var "$m") (.var "$a"))),
           occ "T_z" (.target "$t" (.var "z"))],
  stores := [("$t", "$op")] }
def w1 : Program := { funcs := #[
  mainInt [intP "a", ⟨"mutv", fnTy [pInt] [.int]⟩]
    [.assign (.var "a") (.intLit 1), .assign (.var "mutv") (clos "w1mut" ["a"]),
     .unseq w1graph (.seqn #[])],
  w1mut] }

/-! ## W2  `v := a[b[0]] + mut()`  → {10, 30, 40} -/

def w2mut : Func := {
  id := ⟨"w2mut"⟩, args := #[⟨"pa", pSlice⟩, ⟨"pb", pSlice⟩], results := #[intP "r"],
  body := .seqn #[storeElem "pa" (.intLit 0) (.intLit 30), storeElem "pa" (.intLit 1) (.intLit 40),
                  storeElem "pb" (.intLit 0) (.intLit 1), ret "r" (.intLit 0)] }
def w2graph : UnseqGraph := {
  cells := [intP "$b0", intP "$ai", intP "$m", intP "$op"],
  occs := [occ "R_b0" (.eval "$b0" (.indexGet (.var "b") (.intLit 0))),
           occ "R_ai" (.eval "$ai" (.indexGet (.var "a") (.var "$b0"))),
           occ "E_mut" (.invoke ["$m"] (.var "mutv") []),
           occ "Op" (.eval "$op" (.add (.var "$ai") (.var "$m"))),
           occ "T_z" (.target "$t" (.var "z"))],
  stores := [("$t", "$op")] }
def w2 : Program := { funcs := #[
  mainInt [sliceP "a", sliceP "b", ⟨"mutv", fnTy [pSlice, pSlice] [.int]⟩]
    (makeSlice "a" [10, 20] ++ makeSlice "b" [0] ++
     [.assign (.var "mutv") (clos "w2mut" ["a", "b"]), .unseq w2graph (.seqn #[])]),
  w2mut] }

/-! ## W3  `a[i] += mut()`  (mut: i = 1, returns 1) → {[11 20], [10 21]}; [10 11] forbidden -/

def w3mut : Func := {
  id := ⟨"w3mut"⟩, args := #[⟨"pi", pInt⟩], results := #[intP "r"],
  body := .seqn #[storeP "pi" (.intLit 1), ret "r" (.intLit 1)] }
def w3graph : UnseqGraph := {
  cells := [sliceP "$hdr", intP "$i", intP "$rd", intP "$m", intP "$op"],
  occs := [occ "R_a" (.eval "$hdr" (.var "a")),
           occ "R_i" (.eval "$i" (.var "i")),
           occ "L" (.target "$t" (.addr (.indexAddr (.var "$hdr") (.var "$i")))),
           occ "Rd" (.load "$rd" "$t"),
           occ "E_mut" (.invoke ["$m"] (.var "mutv") []),
           occ "Op" (.eval "$op" (.add (.var "$rd") (.var "$m")))],
  stores := [("$t", "$op")] }
def w3 : Program := { funcs := #[
  mainUnit [sliceP "a", intP "i", ⟨"mutv", fnTy [pInt] [.int]⟩]
    (makeSlice "a" [10, 20] ++
     [.assign (.var "i") (.intLit 0), .assign (.var "mutv") (clos "w3mut" ["i"]),
      .unseq w3graph (println [str "w3", .indexGet (.var "a") (.intLit 0), .indexGet (.var "a") (.intLit 1)])]),
  w3mut] }

/-! ## W4  `_ = a[1] + b[2]`, both nil → two panics -/

def w4graph : UnseqGraph := {
  cells := [intP "$x", intP "$y", intP "$op"],
  occs := [occ "R_a1" (.eval "$x" (.indexGet (.var "a") (.intLit 1))),
           occ "R_b2" (.eval "$y" (.indexGet (.var "b") (.intLit 2))),
           occ "Op" (.eval "$op" (.add (.var "$x") (.var "$y")))] }
def w4 : Program := { funcs := #[mainUnit [sliceP "a", sliceP "b"] [.unseq w4graph (.seqn #[])]] }

/-! ## W5  loop ×2: `println(a[0] + mut())`, mut: a = nil → {panic; "7" then panic} -/

def w5mut : Func := {
  id := ⟨"w5mut"⟩, args := #[⟨"pa", pSlice⟩], results := #[intP "r"],
  body := .seqn #[storeP "pa" (.nil (some (.slice .int))), ret "r" (.intLit 0)] }
def w5graph : UnseqGraph := {
  cells := [intP "$x", intP "$m", intP "$op"],
  occs := [occ "R_a0" (.eval "$x" (.indexGet (.var "a") (.intLit 0))),
           occ "E_mut" (.invoke ["$m"] (.var "mutv") []),
           occ "Op" (.eval "$op" (.add (.var "$x") (.var "$m")))] }
def w5 : Program := { funcs := #[
  mainUnit [sliceP "a", intP "n", ⟨"mutv", fnTy [pSlice] [.int]⟩]
    (makeSlice "a" [7] ++
     [.assign (.var "mutv") (clos "w5mut" ["a"]), .assign (.var "n") (.intLit 0),
      .while (.lessCmp (.var "n") (.intLit 2))
        (.seqn #[.unseq w5graph (println [.var "$op"]),
                 .assign (.var "n") (.add (.var "n") (.intLit 1))])]),
  w5mut] }

/-! ## W6  `v := x + inc() + inc()` → {0, 1, 2} -/

def w6inc : Func := {
  id := ⟨"w6inc"⟩, args := #[⟨"px", pInt⟩], results := #[intP "r"],
  body := .seqn #[storeP "px" (.add (derefI "px") (.intLit 1)), ret "r" (.intLit 0)] }
def w6graph : UnseqGraph := {
  cells := [intP "$x", intP "$i1", intP "$i2", intP "$op"],
  occs := [occ "R_x" (.eval "$x" (.var "x")),
           occ "E1" (.invoke ["$i1"] (.var "incv") []),
           occ "E2" (.invoke ["$i2"] (.var "incv") []) ["E1"],
           occ "Op" (.eval "$op" (.add (.add (.var "$x") (.var "$i1")) (.var "$i2"))),
           occ "T_z" (.target "$t" (.var "z"))],
  stores := [("$t", "$op")] }
def w6 : Program := { funcs := #[
  mainInt [intP "x", ⟨"incv", fnTy [pInt] [.int]⟩]
    [.assign (.var "x") (.intLit 0), .assign (.var "incv") (clos "w6inc" ["x"]),
     .unseq w6graph (.seqn #[])],
  w6inc] }

/-! ## X1  `xs[ys[9]], b = zs[7], 2` — phase 1 panics, no store -/

def x1graph : UnseqGraph := {
  cells := [sliceP "$xs", intP "$y9", intP "$z7", intP "$two"],
  occs := [occ "R_xs" (.eval "$xs" (.var "xs")),
           occ "R_ys9" (.eval "$y9" (.indexGet (.var "ys") (.intLit 9))),
           occ "L1" (.target "$t1" (.addr (.indexAddr (.var "$xs") (.var "$y9")))),
           occ "R_zs7" (.eval "$z7" (.indexGet (.var "zs") (.intLit 7))),
           occ "K2" (.eval "$two" (.intLit 2)),
           occ "T_b" (.target "$tb" (.var "b"))],
  stores := [("$t1", "$z7"), ("$tb", "$two")] }
def x1 : Program := { funcs := #[
  mainUnit [sliceP "xs", sliceP "ys", sliceP "zs", intP "b"]
    (makeSlice "xs" [0, 0, 0] ++ makeSlice "ys" [0, 0, 0] ++ makeSlice "zs" [0, 0, 0] ++
     [.unseq x1graph (println [str "x1 ok", .var "b"])])] }

/-! ## X2  `v := b2i(z || h()) + x` — the event consumes the JOIN -/

def x2h : Func := {
  id := ⟨"x2h"⟩, args := #[⟨"px", pInt⟩], results := #[boolP "r"],
  body := .seqn #[storeP "px" (.intLit 2), ret "r" (.boolLit true)] }
def b2i : Func := {
  id := ⟨"b2i"⟩, args := #[boolP "b"], results := #[intP "r"],
  body := .ifThenElse (.var "b") (ret "r" (.intLit 1)) (ret "r" (.intLit 0)) }
def x2graph : UnseqGraph := {
  cells := [boolP "$z", boolP "$h", boolP "$cor", intP "$b", intP "$x", intP "$op"],
  occs := [occ "R_z" (.eval "$z" (.var "zz")),
           occ "G" (.guard "$z" false "$cor"),
           occ "E_h" (.invoke ["$h"] (.var "hv") []) [] (some "G"),
           occ "C_or" (.eval "$cor" (.var "$h")) [] (some "G"),
           occ "E_b2i" (.invoke ["$b"] (.var "b2iv") [.var "$cor"]),
           occ "R_x" (.eval "$x" (.var "x")),
           occ "Op" (.eval "$op" (.add (.var "$b") (.var "$x"))),
           occ "T_z" (.target "$t" (.var "z"))],
  stores := [("$t", "$op")] }
def x2 (z : Bool) : Program := { funcs := #[
  mainInt [intP "x", boolP "zz", ⟨"hv", fnTy [pInt] [.bool]⟩, ⟨"b2iv", fnTy [.bool] [.int]⟩]
    [.assign (.var "x") (.intLit 1), .assign (.var "zz") (.boolLit z),
     .assign (.var "hv") (clos "x2h" ["x"]), .assign (.var "b2iv") (clos "b2i" []),
     .unseq x2graph (.seqn #[])],
  x2h, b2i] }

/-! ## X3  `x[f()] += <-ch` — buffered, then EMPTY (blocked is a refusal, not a member).
The frozen channel state is made observable by a deferred `println(len(ch))`
that runs on the panic path (the reference records `len(ch)` beside the panic). -/

def x3f : Func := {
  id := ⟨"x3f"⟩, args := #[], results := #[intP "r"], body := ret "r" (.intLit 9) }
def x3recv : Func := {
  id := ⟨"x3recv"⟩, args := #[⟨"pc", .pointer (.chan .both .int)⟩], results := #[intP "r"],
  body := .chanRecv #[.var "r"] (.deref (.var "pc") (.chan .both .int)) .int }
def x3defer : Func := {
  id := ⟨"x3defer"⟩, args := #[⟨"pc", .pointer (.chan .both .int)⟩], results := #[],
  body := println [str "len", .length (.deref (.var "pc") (.chan .both .int)) (some (.chan .both .int))] }
def x3graph : UnseqGraph := {
  cells := [intP "$f", sliceP "$hdr", intP "$rd", intP "$rc", intP "$op"],
  occs := [occ "E_f" (.invoke ["$f"] (.var "fv") []),
           occ "R_x" (.eval "$hdr" (.var "x")),
           occ "L" (.target "$t" (.addr (.indexAddr (.var "$hdr") (.var "$f")))),
           occ "Rd" (.load "$rd" "$t"),
           occ "E_recv" (.invoke ["$rc"] (.var "recvv") []) ["E_f"],
           occ "Op" (.eval "$op" (.add (.var "$rd") (.var "$rc")))],
  stores := [("$t", "$op")] }
def x3 (buffered : Bool) : Program := { funcs := #[
  mainUnit [sliceP "x", ⟨"ch", .chan .both .int⟩, ⟨"fv", fnTy [] [.int]⟩,
            ⟨"recvv", fnTy [.pointer (.chan .both .int)] [.int]⟩,
            ⟨"dv", fnTy [.pointer (.chan .both .int)] []⟩]
    (makeSlice "x" [1] ++
     [.makeChan (.var "ch") .int (some (.intLit 1))] ++
     (if buffered then [.chanSend (.var "ch") (.intLit 5) .int] else []) ++
     [.assign (.var "fv") (clos "x3f" []), .assign (.var "recvv") (clos "x3recv" ["ch"]),
      .assign (.var "dv") (clos "x3defer" ["ch"]),
      .deferCall (.var "dv") #[],
      .unseq x3graph (.seqn #[])]),
  x3f, x3recv, x3defer] }

/-! ## R1  `v := x + y + mut()` — unreduced {0,1,2,3}; the REFUTED reduction {0,2,3} -/

def r1mut : Func := {
  id := ⟨"r1mut"⟩, args := #[⟨"px", pInt⟩, ⟨"py", pInt⟩], results := #[intP "r"],
  body := .seqn #[storeP "px" (.intLit 1), storeP "py" (.intLit 2), ret "r" (.intLit 0)] }
def r1graph (reduced : Bool) : UnseqGraph := {
  cells := [intP "$x", intP "$y", intP "$m", intP "$op"],
  occs := [occ "R_x" (.eval "$x" (.var "x")),
           occ "R_y" (.eval "$y" (.var "y")) (if reduced then ["R_x"] else []),
           occ "E_mut" (.invoke ["$m"] (.var "mutv") []),
           occ "Op" (.eval "$op" (.add (.add (.var "$x") (.var "$y")) (.var "$m"))),
           occ "T_z" (.target "$t" (.var "z"))],
  stores := [("$t", "$op")] }
def r1 (reduced : Bool) : Program := { funcs := #[
  mainInt [intP "x", intP "y", ⟨"mutv", fnTy [pInt, pInt] [.int]⟩]
    [.assign (.var "x") (.intLit 0), .assign (.var "y") (.intLit 0),
     .assign (.var "mutv") (clos "r1mut" ["x", "y"]), .unseq (r1graph reduced) (.seqn #[])],
  r1mut] }

/-! ## R2a  `sink(z || h(), k())` — a skipped event discharges E1; the INVALID join refuses -/

def pr (fid : String) (text : String) (r : Int) : Func :=
  { id := ⟨fid⟩, args := #[], results := #[intP "r"], body := .seqn #[println [str text], ret "r" (.intLit r)] }
def prB (fid : String) (text : String) (r : Bool) : Func :=
  { id := ⟨fid⟩, args := #[], results := #[boolP "r"], body := .seqn #[println [str text], ret "r" (.boolLit r)] }
def r2ah : Func := prB "r2ah" "guard h" true
def r2ak : Func := pr "r2ak" "guard k" 7
def r2aSink : Func := {
  id := ⟨"r2aSink"⟩, args := #[boolP "b", intP "n"], results := #[],
  body := println [str "guard result", .var "b", .var "n"] }
def r2aKArg : Func := {
  id := ⟨"r2aKArg"⟩, args := #[boolP "b"], results := #[intP "r"],
  body := .seqn #[println [str "guard k"], ret "r" (.intLit 7)] }
def r2aGraph (valid : Bool) : UnseqGraph := {
  cells := [boolP "$z", boolP "$h", boolP "$cor", intP "$k"],
  occs := [occ "R_z" (.eval "$z" (.var "z")),
           occ "G" (.guard "$z" false "$cor"),
           occ "E_h" (.invoke ["$h"] (.var "hv") []) [] (some "G"),
           occ "C_or" (.eval "$cor" (.var "$h")) [] (some "G"),
           (if valid then occ "E_k" (.invoke ["$k"] (.var "kv") []) ["C_or"]
            else occ "E_k" (.invoke ["$k"] (.var "kargv") [.var "$h"])),
           occ "E_sink" (.invoke [] (.var "sinkv") [.var "$cor", .var "$k"])] }
def r2a (z : Bool) (valid : Bool) : Program := { funcs := #[
  mainUnit [boolP "z", ⟨"hv", fnTy [] [.bool]⟩, ⟨"kv", fnTy [] [.int]⟩,
            ⟨"kargv", fnTy [.bool] [.int]⟩, ⟨"sinkv", fnTy [.bool, .int] []⟩]
    [.assign (.var "z") (.boolLit z), .assign (.var "hv") (clos "r2ah" []),
     .assign (.var "kv") (clos "r2ak" []), .assign (.var "kargv") (clos "r2aKArg" []),
     .assign (.var "sinkv") (clos "r2aSink" []), .unseq (r2aGraph valid) (.seqn #[])],
  r2ah, r2ak, r2aKArg, r2aSink] }

/-! ## R2b  `sink(left || b, change())` — E1 anchored at the COMPLETION (vs the refuted ENTRY) -/

def r2bChange : Func := {
  id := ⟨"r2bChange"⟩, args := #[⟨"pb", .pointer .bool⟩], results := #[intP "r"],
  body := .seqn #[storeP "pb" (.boolLit true), ret "r" (.intLit 0)] }
def r2bSink : Func := {
  id := ⟨"r2bSink"⟩, args := #[boolP "b", intP "n"], results := #[],
  body := println [str "logical", .var "b", .var "n"] }
def r2bGraph (anchor : String) : UnseqGraph := {
  cells := [boolP "$l", boolP "$b", boolP "$cor", intP "$c"],
  occs := [occ "R_left" (.eval "$l" (.var "left")),
           occ "G" (.guard "$l" false "$cor"),
           occ "R_b" (.eval "$b" (.var "b")) [] (some "G"),
           occ "C_or" (.eval "$cor" (.var "$b")) [] (some "G"),
           occ "E_change" (.invoke ["$c"] (.var "changev") []) [anchor],
           occ "E_sink" (.invoke [] (.var "sinkv") [.var "$cor", .var "$c"])] }
def r2b (anchor : String) : Program := { funcs := #[
  mainUnit [boolP "left", boolP "b", ⟨"changev", fnTy [.pointer .bool] [.int]⟩, ⟨"sinkv", fnTy [.bool, .int] []⟩]
    [.assign (.var "left") (.boolLit false), .assign (.var "b") (.boolLit false),
     .assign (.var "changev") (clos "r2bChange" ["b"]), .assign (.var "sinkv") (clos "r2bSink" []),
     .unseq (r2bGraph anchor) (.seqn #[])],
  r2bChange, r2bSink] }

/-! ## R2c  `sink(g(), a || (b && h()), k())` — nested guards, an earlier call -/

def r2cG : Func := {
  id := ⟨"r2cG"⟩, args := #[⟨"pa", .pointer .bool⟩], results := #[intP "r"],
  body := .seqn #[println [str "g"], storeP "pa" (.boolLit true), ret "r" (.intLit 1)] }
def r2cH : Func := prB "r2cH" "h" true
def r2cK : Func := pr "r2cK" "k" 7
def r2cSink : Func := {
  id := ⟨"r2cSink"⟩, args := #[intP "g", boolP "c", intP "k"], results := #[],
  body := println [str "sink", .var "g", .var "c", .var "k"] }
def r2cGraph : UnseqGraph := {
  cells := [intP "$g", boolP "$a", boolP "$b", boolP "$h", boolP "$cand", boolP "$cor", intP "$k"],
  occs := [occ "E_g" (.invoke ["$g"] (.var "gv") []),
           occ "R_a" (.eval "$a" (.var "a")),
           occ "G1" (.guard "$a" false "$cor") ["E_g"],
           occ "R_b" (.eval "$b" (.var "b")) [] (some "G1"),
           occ "G2" (.guard "$b" true "$cand") [] (some "G1"),
           occ "E_h" (.invoke ["$h"] (.var "hv") []) [] (some "G2"),
           occ "C_and" (.eval "$cand" (.var "$h")) [] (some "G2"),
           occ "C_or" (.eval "$cor" (.var "$cand")) [] (some "G1"),
           occ "E_k" (.invoke ["$k"] (.var "kv") []) ["C_or"],
           occ "E_sink" (.invoke [] (.var "sinkv") [.var "$g", .var "$cor", .var "$k"])] }
def r2c (b : Bool) : Program := { funcs := #[
  mainUnit [boolP "a", boolP "b", ⟨"gv", fnTy [.pointer .bool] [.int]⟩, ⟨"hv", fnTy [] [.bool]⟩,
            ⟨"kv", fnTy [] [.int]⟩, ⟨"sinkv", fnTy [.int, .bool, .int] []⟩]
    [.assign (.var "a") (.boolLit false), .assign (.var "b") (.boolLit b),
     .assign (.var "gv") (clos "r2cG" ["a"]), .assign (.var "hv") (clos "r2cH" []),
     .assign (.var "kv") (clos "r2cK" []), .assign (.var "sinkv") (clos "r2cSink" []),
     .unseq r2cGraph (.seqn #[])],
  r2cG, r2cH, r2cK, r2cSink] }

/-! ## R4  `old := a; a[0] += mut()` — mut REBINDS a; the frozen header keeps identity -/

def r4mut : Func := {
  id := ⟨"r4mut"⟩, args := #[⟨"pa", pSlice⟩, ⟨"pb", pSlice⟩], results := #[intP "r"],
  body := .seqn #[storeP "pa" (derefS "pb"), ret "r" (.intLit 1)] }
def r4graph : UnseqGraph := {
  cells := [sliceP "$hdr", intP "$rd", intP "$m", intP "$op"],
  occs := [occ "R_a" (.eval "$hdr" (.var "a")),
           occ "L" (.target "$t" (.addr (.indexAddr (.var "$hdr") (.intLit 0)))),
           occ "Rd" (.load "$rd" "$t"),
           occ "E_mut" (.invoke ["$m"] (.var "mutv") []),
           occ "Op" (.eval "$op" (.add (.var "$rd") (.var "$m")))],
  stores := [("$t", "$op")] }
def r4 : Program := { funcs := #[
  mainUnit [sliceP "a", sliceP "b", sliceP "old", ⟨"mutv", fnTy [pSlice, pSlice] [.int]⟩]
    (makeSlice "a" [10, 20] ++ makeSlice "b" [100, 200] ++
     [.assign (.var "old") (.var "a"), .assign (.var "mutv") (clos "r4mut" ["a", "b"]),
      .unseq r4graph (.seqn #[
        println [str "old", .indexGet (.var "old") (.intLit 0), .indexGet (.var "old") (.intLit 1)],
        println [str "a", .indexGet (.var "a") (.intLit 0), .indexGet (.var "a") (.intLit 1)]])]),
  r4mut] }
-- (`r4with`, below in the audit fix-round section, is the same program around any target graph.)

/-! ## R6  `v := a[f()]` — SPLIT header producer + checked access {10, 20} vs FUSED {20} -/

def r6f : Func := {
  id := ⟨"r6f"⟩, args := #[⟨"pa", pSlice⟩, ⟨"pb", pSlice⟩], results := #[intP "r"],
  body := .seqn #[storeP "pa" (derefS "pb"), ret "r" (.intLit 0)] }
def r6graph (split : Bool) : UnseqGraph :=
  if split then {
    cells := [sliceP "$hdr", intP "$f", intP "$rd"],
    occs := [occ "R_a" (.eval "$hdr" (.var "a")),
             occ "E_f" (.invoke ["$f"] (.var "fv") []),
             occ "Rd" (.eval "$rd" (.indexGet (.var "$hdr") (.var "$f"))),
             occ "T_z" (.target "$t" (.var "z"))],
    stores := [("$t", "$rd")] }
  else {
    cells := [intP "$f", intP "$rd"],
    occs := [occ "E_f" (.invoke ["$f"] (.var "fv") []),
             occ "Rd" (.eval "$rd" (.indexGet (.var "a") (.var "$f"))),
             occ "T_z" (.target "$t" (.var "z"))],
    stores := [("$t", "$rd")] }
def r6 (split : Bool) : Program := { funcs := #[
  mainInt [sliceP "a", sliceP "b", ⟨"fv", fnTy [pSlice, pSlice] [.int]⟩]
    (makeSlice "a" [10] ++ makeSlice "b" [20] ++
     [.assign (.var "fv") (clos "r6f" ["a", "b"]), .unseq (r6graph split) (.seqn #[])]),
  r6f] }

/-! ## Controls C1–C4 -/

def c1g : Func := {
  id := ⟨"c1g"⟩, args := #[⟨"pt", pInt⟩], results := #[intP "r"],
  body := .seqn #[storeP "pt" (.intLit 7), ret "r" (.intLit 1)] }
def c1f : Func := {
  id := ⟨"c1f"⟩, args := #[⟨"pt", pInt⟩, intP "x"], results := #[intP "r"],
  body := ret "r" (.add (.var "x") (derefI "pt")) }
def c1graph : UnseqGraph := {
  cells := [intP "$g", intP "$f"],
  occs := [occ "E_g" (.invoke ["$g"] (.var "gv") []),
           occ "E_f" (.invoke ["$f"] (.var "fv") [.var "$g"])] }
def c1 : Program := { funcs := #[
  mainInt [intP "t", ⟨"gv", fnTy [pInt] [.int]⟩, ⟨"fv", fnTy [pInt, .int] [.int]⟩]
    [.assign (.var "t") (.intLit 0), .assign (.var "gv") (clos "c1g" ["t"]),
     .assign (.var "fv") (clos "c1f" ["t"]), .unseq c1graph (ret "z" (.var "$f"))],
  c1g, c1f] }

def sinkId : Func := {
  id := ⟨"sinkId"⟩, args := #[intP "x"], results := #[intP "r"], body := ret "r" (.var "x") }
def sink2 : Func := {
  id := ⟨"sink2"⟩, args := #[intP "x", intP "y"], results := #[intP "r"], body := ret "r" (.var "x") }
def c2graph : UnseqGraph := {
  cells := [intP "$a", intP "$s"],
  occs := [occ "R_a" (.eval "$a" (.var "a")), occ "E_sink" (.invoke ["$s"] (.var "sinkv") [.var "$a"])] }
def c2 : Program := { funcs := #[
  mainInt [intP "a", ⟨"sinkv", fnTy [.int] [.int]⟩]
    [.assign (.var "a") (.intLit 3), .assign (.var "sinkv") (clos "sinkId" []),
     .unseq c2graph (ret "z" (.var "$s"))],
  sinkId] }
def c3mut : Func := {
  id := ⟨"c3mut"⟩, args := #[⟨"pa", pInt⟩], results := #[intP "r"],
  body := .seqn #[storeP "pa" (.intLit 2), ret "r" (.intLit 0)] }
def c3graph : UnseqGraph := {
  cells := [intP "$a", intP "$m", intP "$s"],
  occs := [occ "R_a" (.eval "$a" (.var "a")), occ "E_mut" (.invoke ["$m"] (.var "mutv") []),
           occ "E_sink" (.invoke ["$s"] (.var "sinkv") [.var "$a", .var "$m"]),
           occ "T_z" (.target "$t" (.var "z"))],
  stores := [("$t", "$s")] }
def c3 : Program := { funcs := #[
  mainInt [intP "a", ⟨"mutv", fnTy [pInt] [.int]⟩, ⟨"sinkv", fnTy [.int, .int] [.int]⟩]
    [.assign (.var "a") (.intLit 1), .assign (.var "mutv") (clos "c3mut" ["a"]),
     .assign (.var "sinkv") (clos "sink2" []), .unseq c3graph (.seqn #[])],
  c3mut, sink2] }
def c4graph : UnseqGraph := {
  cells := [intP "$a", intP "$b"],
  occs := [occ "A" (.eval "$a" (.intLit 0)) ["B"], occ "B" (.eval "$b" (.intLit 0)) ["A"]] }
def c4 : Program := { funcs := #[mainUnit [] [.unseq c4graph (.seqn #[])]] }

/-! ## Malformed graphs (static, refused BY NAME at ENTER) -/

def malformed (g : UnseqGraph) : Program := { funcs := #[mainUnit [intP "x"] [.unseq g (.seqn #[])]] }
def mUnknownSlot : UnseqGraph := { cells := [intP "$a"], occs := [occ "A" (.eval "$a" (.var "$zz"))] }
def mDupResult : UnseqGraph := {
  cells := [intP "$a"],
  occs := [occ "A" (.eval "$a" (.intLit 0)), occ "B" (.eval "$a" (.intLit 1))] }
def mSortLoad : UnseqGraph := {
  cells := [intP "$a", intP "$b"],
  occs := [occ "A" (.eval "$a" (.intLit 0)), occ "B" (.load "$b" "$a")] }
def mSortTargetAsValue : UnseqGraph := {
  cells := [intP "$a"],
  occs := [occ "T" (.target "$t" (.var "x")), occ "A" (.eval "$a" (.var "$t"))] }
def mUnknownAfter : UnseqGraph := { cells := [intP "$a"], occs := [occ "A" (.eval "$a" (.intLit 0)) ["Q"]] }
def mUnproduced : UnseqGraph := { cells := [intP "$a", intP "$b"], occs := [occ "A" (.eval "$a" (.intLit 0))] }

/-! ## Target identity (§3.4): pointer redirection, cell mutation at a stable address, map (Stage E refusal) -/

def ptrMut : Func := {
  id := ⟨"ptrMut"⟩, args := #[⟨"pp", .pointer pInt⟩, ⟨"py", pInt⟩], results := #[intP "r"],
  body := .seqn #[storeP "pp" (.var "py"), ret "r" (.intLit 1)] }
def ptrGraph : UnseqGraph := {
  cells := [⟨"$p", pInt⟩, intP "$rd", intP "$m", intP "$op"],
  occs := [occ "R_p" (.eval "$p" (.var "p")),
           occ "L" (.target "$t" (.addr (.var "$p"))),
           occ "Rd" (.load "$rd" "$t"),
           occ "E_mut" (.invoke ["$m"] (.var "mutv") []),
           occ "Op" (.eval "$op" (.add (.var "$rd") (.var "$m")))],
  stores := [("$t", "$op")] }
def ptr : Program := { funcs := #[
  mainUnit [intP "x", intP "y", ⟨"p", pInt⟩, ⟨"mutv", fnTy [.pointer pInt, pInt] [.int]⟩]
    [.assign (.var "x") (.intLit 10), .assign (.var "y") (.intLit 100), .assign (.var "p") (.ref "x"),
     .assign (.var "mutv") (clos "ptrMut" ["p", "y"]),
     .unseq ptrGraph (println [str "x y", .var "x", .var "y"])],
  ptrMut] }

def cellMut : Func := {
  id := ⟨"cellMut"⟩, args := #[⟨"pa", pSlice⟩], results := #[intP "r"],
  body := .seqn #[storeElem "pa" (.intLit 0) (.intLit 100), ret "r" (.intLit 1)] }
def cellGraph : UnseqGraph := r4graph
def cell : Program := { funcs := #[
  mainUnit [sliceP "a", ⟨"mutv", fnTy [pSlice] [.int]⟩]
    (makeSlice "a" [10] ++
     [.assign (.var "mutv") (clos "cellMut" ["a"]),
      .unseq cellGraph (println [str "a", .indexGet (.var "a") (.intLit 0)])]),
  cellMut] }

def mapGraph : UnseqGraph := {
  cells := [intP "$rd"],
  occs := [occ "L" (.target "$t" (.mapElem (.var "m") (.intLit 1) .int .int)),
           occ "Rd" (.load "$rd" "$t")] }
def mapProg : Program := { funcs := #[
  mainUnit [⟨"m", .map .int .int⟩]
    [.makeMap (.var "m") .int .int none, .mapAssign (.var "m") (.intLit 1) (.intLit 5) .int .int,
     .unseq mapGraph (.seqn #[])]] }

/-! ## Audit fix round (2026-09-16; `docs/2026-09-16_unseq-stage-b-audit.md`) — the
FAIL-OPEN paths F1–F3 as named refusals, N3, the R5 lowering, the R2 machine-side
regression, and the audit's A8 contrast. Graphs are the audit's, re-encoded on this
harness. -/

/-! ### F1 — a SKIPPED producer's binder is never consumed as a value (store and `thenB`) -/

def a4h : Func := pr "a4h" "h ran" 42
/-- A4: the phase-2 store's VALUE binder `$h` is produced only inside the region. -/
def a4Graph : UnseqGraph := {
  cells := [boolP "$z", intP "$h", boolP "$cor"],
  occs := [occ "R_z" (.eval "$z" (.var "z")),
           occ "G" (.guard "$z" false "$cor"),
           occ "E_h" (.invoke ["$h"] (.var "hv") []) [] (some "G"),
           occ "C_or" (.eval "$cor" (.boolLit true)) [] (some "G"),
           occ "T" (.target "$t" (.var "out"))],
  stores := [("$t", "$h")] }
def a4 (z : Bool) : Program := { funcs := #[
  mainUnit [boolP "z", intP "out", ⟨"hv", fnTy [] [.int]⟩]
    [.assign (.var "z") (.boolLit z), .assign (.var "out") (.intLit 7),
     .assign (.var "hv") (clos "a4h" []),
     .unseq a4Graph (println [str "out", .var "out"])],
  a4h] }
/-- A5: `thenB` reads `$h` directly (no store). -/
def a5Graph : UnseqGraph := { a4Graph with stores := [], occs := a4Graph.occs.take 4 }
def a5 (z : Bool) (thenB : Stmt) : Program := { funcs := #[
  mainUnit [boolP "z", ⟨"hv", fnTy [] [.int]⟩]
    [.assign (.var "z") (.boolLit z), .assign (.var "hv") (clos "a4h" []), .unseq a5Graph thenB],
  a4h] }
/-- A8 (the audit's contrast): a phase-2 store through a TARGET binder produced
inside a SKIPPED region — refused by name already before the fix round. -/
def a8Graph : UnseqGraph := {
  cells := [boolP "$z", boolP "$cor", intP "$one"],
  occs := [occ "R_z" (.eval "$z" (.var "z")),
           occ "G" (.guard "$z" false "$cor"),
           occ "T" (.target "$t" (.var "out")) [] (some "G"),
           occ "C_or" (.eval "$cor" (.boolLit true)) [] (some "G"),
           occ "K" (.eval "$one" (.intLit 1))],
  stores := [("$t", "$one")] }
def a8 : Program := { funcs := #[
  mainUnit [boolP "z", intP "out"]
    [.assign (.var "z") (.boolLit true), .assign (.var "out") (.intLit 7),
     .unseq a8Graph (println [str "out", .var "out"])]] }
/-- A3 (audit R2): a use confined to a LATER-skipped region of a binder confined
to an earlier-skipped region — the machine refuses per §1 G as soon as the
producer is skipped; the reference enumerator now refuses it too. -/
def a3Sink : Func := {
  id := ⟨"a3Sink"⟩, args := #[boolP "a", boolP "b"], results := #[],
  body := println [str "sink", .var "a", .var "b"] }
def a3Graph : UnseqGraph := {
  cells := [boolP "$z1", boolP "$h", boolP "$c1", boolP "$z2", boolP "$x", boolP "$c2"],
  occs := [occ "R_z1" (.eval "$z1" (.var "z1")),
           occ "G1" (.guard "$z1" false "$c1"),
           occ "E_h" (.invoke ["$h"] (.var "hv") []) [] (some "G1"),
           occ "C1" (.eval "$c1" (.var "$h")) [] (some "G1"),
           occ "R_z2" (.eval "$z2" (.var "z2")) ["C1"],
           occ "G2" (.guard "$z2" false "$c2"),
           occ "X" (.eval "$x" (.var "$h")) [] (some "G2"),
           occ "C2" (.eval "$c2" (.var "$x")) [] (some "G2"),
           occ "E_sink" (.invoke [] (.var "sinkv") [.var "$c1", .var "$c2"])] }
def a3 : Program := { funcs := #[
  mainUnit [boolP "z1", boolP "z2", ⟨"hv", fnTy [] [.bool]⟩, ⟨"sinkv", fnTy [.bool, .bool] []⟩]
    [.assign (.var "z1") (.boolLit true), .assign (.var "z2") (.boolLit true),
     .assign (.var "hv") (clos "r2ah" []), .assign (.var "sinkv") (clos "a3Sink" []),
     .unseq a3Graph (.seqn #[])],
  r2ah, a3Sink] }

/-! ### F2 — a target plan anchored at the ADDRESS of a slice variable is refused (the header is not frozen) -/

/-- The R4 program around any target graph (the two `println`s show old storage and the current header). -/
def r4with (g : UnseqGraph) : Program := { funcs := #[
  mainUnit [sliceP "a", sliceP "b", sliceP "old", ⟨"mutv", fnTy [pSlice, pSlice] [.int]⟩]
    (makeSlice "a" [10, 20] ++ makeSlice "b" [100, 200] ++
     [.assign (.var "old") (.var "a"), .assign (.var "mutv") (clos "r4mut" ["a", "b"]),
      .unseq g (.seqn #[
        println [str "old", .indexGet (.var "old") (.intLit 0), .indexGet (.var "old") (.intLit 1)],
        println [str "a", .indexGet (.var "a") (.intLit 0), .indexGet (.var "a") (.intLit 1)]])]),
  r4mut] }
/-- C1: the plan spelled `&a[0]` with `.ref "a"` — an admitted atom, but the anchor
is the slice VARIABLE's address: `resolveChain` would re-read its header at the
load and at the store (the forbidden hybrid `old 10 20 / a 11 200`). -/
def c1Graph : UnseqGraph := { r4graph with
  cells := [intP "$rd", intP "$m", intP "$op"],
  occs := [occ "L" (.target "$t" (.addr (.indexAddr (.ref "a") (.intLit 0)))),
           occ "Rd" (.load "$rd" "$t"),
           occ "E_mut" (.invoke ["$m"] (.var "mutv") []),
           occ "Op" (.eval "$op" (.add (.var "$rd") (.var "$m")))] }
/-- C1b: the source local's header READ at the plan step (`.var "a"`) — frozen from then on. -/
def c1bGraph : UnseqGraph := { c1Graph with
  occs := [occ "L" (.target "$t" (.addr (.indexAddr (.var "a") (.intLit 0)))),
           occ "Rd" (.load "$rd" "$t"),
           occ "E_mut" (.invoke ["$m"] (.var "mutv") []),
           occ "Op" (.eval "$op" (.add (.var "$rd") (.var "$m")))] }
/-- An ARRAY variable's address is a stable identity (arrays do not rebind): accepted. -/
def arrGraph : UnseqGraph := {
  cells := [intP "$rd", intP "$m", intP "$op"],
  occs := [occ "L" (.target "$t" (.addr (.indexAddr (.ref "arr") (.intLit 0)))),
           occ "Rd" (.load "$rd" "$t"),
           occ "E_one" (.invoke ["$m"] (.var "onev") []),
           occ "Op" (.eval "$op" (.add (.var "$rd") (.var "$m")))],
  stores := [("$t", "$op")] }
def arrProg : Program := { funcs := #[
  mainUnit [⟨"arr", .array 2 .int⟩, ⟨"onev", fnTy [] [.int]⟩]
    [.assign (.addr (.indexAddr (.ref "arr") (.intLit 0))) (.intLit 10),
     .assign (.addr (.indexAddr (.ref "arr") (.intLit 1))) (.intLit 20),
     .assign (.var "onev") (clos "one" []),
     .unseq arrGraph (println [str "arr", .indexGet (.var "arr") (.intLit 0), .indexGet (.var "arr") (.intLit 1)])],
  pr "one" "one" 1] }

/-! ### F3 — a binder without the `$` reservation is refused (it would shadow a source local) -/

def b4g : UnseqGraph := { cells := [intP "a"], occs := [occ "K" (.eval "a" (.intLit 42))] }
def b4 : Program := { funcs := #[
  mainUnit [intP "a"] [.assign (.var "a") (.intLit 1),
    .unseq b4g (println [str "then a", .var "a"]),
    println [str "after a", .var "a"]]] }
def mBareTarget : UnseqGraph := {
  cells := [intP "$a"],
  occs := [occ "A" (.eval "$a" (.intLit 0)), occ "T" (.target "t" (.var "x"))],
  stores := [("t", "$a")] }

/-! ### N3 — a guard's test/completion cell must be a bool cell (refused at ENTER by name) -/

def k4Graph (testTy outTy : Ty) : UnseqGraph := {
  cells := [⟨"$z", testTy⟩, intP "$h", ⟨"$cor", outTy⟩],
  occs := [occ "R_z" (.eval "$z" (.var "z")), occ "G" (.guard "$z" false "$cor"),
           occ "E_h" (.invoke ["$h"] (.var "hv") []) [] (some "G"),
           occ "C_or" (.eval "$cor" (.var "$h")) [] (some "G")] }
def k4 (testTy outTy : Ty) : Program := { funcs := #[
  mainUnit [boolP "z", ⟨"hv", fnTy [] [.int]⟩]
    [.assign (.var "z") (.boolLit true), .assign (.var "hv") (clos "a4h" []),
     .unseq (k4Graph testTy outTy) (println [str "c", .var "$cor"])],
  a4h] }

/-! ### R5 — the headline lowering `x := a + f()` ↦ `thenB = .initialization x; x = $op` -/

def fv1 : Func := { id := ⟨"fv1"⟩, args := #[], results := #[intP "r"], body := ret "r" (.intLit 2) }
def kGraph : UnseqGraph := {
  cells := [intP "$a", intP "$f", intP "$op"],
  occs := [occ "R_a" (.eval "$a" (.var "a")), occ "E_f" (.invoke ["$f"] (.var "fv") []),
           occ "Op" (.eval "$op" (.add (.var "$a") (.var "$f")))] }
def thenDecl (x : String) : Stmt := .seqn #[.initialization (intP x), .assign (.var x) (.var "$op")]
/-- K2: the sweep in the MIDDLE of a block; `x` declared by `thenB` survives for the rest. -/
def k2 : Program := { funcs := #[
  mainUnit [intP "a", ⟨"fv", fnTy [] [.int]⟩]
    [.assign (.var "a") (.intLit 1), .assign (.var "fv") (clos "fv1" []),
     .unseq kGraph (thenDecl "x"),
     println [str "x", .var "x"],
     .assign (.var "a") (.intLit 10),
     .unseq kGraph (thenDecl "y"),
     println [str "x y", .var "x", .var "y"]],
  fv1] }
/-- K3: the same inside a 2-iteration loop body (a fresh `x` per iteration). -/
def k3 : Program := { funcs := #[
  mainUnit [intP "a", intP "n", ⟨"fv", fnTy [] [.int]⟩]
    [.assign (.var "a") (.intLit 1), .assign (.var "n") (.intLit 0), .assign (.var "fv") (clos "fv1" []),
     .while (.lessCmp (.var "n") (.intLit 2))
       (.seqn #[.unseq kGraph (thenDecl "x"), println [str "x", .var "x"],
                .assign (.var "a") (.add (.var "a") (.intLit 1)), .assign (.var "n") (.add (.var "n") (.intLit 1))])],
  fv1] }

/-! ## Binder lifetime across recursion: `sum(n) = g(n) + sum(n-1)` inside a sweep — per-activation cells -/

def sumG : Func := {
  id := ⟨"sumG"⟩, args := #[intP "n"], results := #[intP "r"], body := ret "r" (.var "n") }
def sumGraph : UnseqGraph := {
  cells := [intP "$g", intP "$n1", intP "$s", intP "$op"],
  occs := [occ "E_g" (.invoke ["$g"] (.var "gv") [.var "n"]),
           occ "K" (.eval "$n1" (.sub (.var "n") (.intLit 1))),
           occ "E_rec" (.invoke ["$s"] (.funcVal ⟨"sum"⟩ #[]) [.var "$n1", .var "gv"]) ["E_g"],
           occ "Op" (.eval "$op" (.add (.var "$g") (.var "$s"))),
           occ "T_r" (.target "$t" (.var "r"))],
  stores := [("$t", "$op")] }
def sumF : Func := {
  id := ⟨"sum"⟩, args := #[intP "n", ⟨"gv", fnTy [.int] [.int]⟩], results := #[intP "r"],
  body := .ifThenElse (.eqCmp .int (.var "n") (.intLit 0)) (ret "r" (.intLit 0))
    (.seqn #[.unseq sumGraph (.seqn #[])]) }
def recursion : Program := { funcs := #[
  mainInt [⟨"gv", fnTy [.int] [.int]⟩]
    [.assign (.var "gv") (clos "sumG" []), .call #[.var "z"] ⟨"sum"⟩ #[.intLit 4, .var "gv"]],
  sumG, sumF] }

/-! ## Replay: three unordered printing events — every order is a schedule, each realized by its rank tape -/

def trGraph : UnseqGraph := {
  cells := [intP "$a", intP "$b", intP "$c"],
  occs := [occ "A" (.invoke ["$a"] (.var "av") []), occ "B" (.invoke ["$b"] (.var "bv") []),
           occ "C" (.invoke ["$c"] (.var "cv") [])] }
def trace : Program := { funcs := #[
  mainUnit [⟨"av", fnTy [] [.int]⟩, ⟨"bv", fnTy [] [.int]⟩, ⟨"cv", fnTy [] [.int]⟩]
    [.assign (.var "av") (clos "prA" []), .assign (.var "bv") (clos "prB" []),
     .assign (.var "cv") (clos "prC" []), .unseq trGraph (.seqn #[])],
  pr "prA" "A" 0, pr "prB" "B" 0, pr "prC" "C" 0] }

/-- The rank tape of an occurrence ORDER (a permutation of the graph's
indices): at each step, the picked occurrence's position in the machine's
own ready list (`UnseqGraph.ready`) — test code over the machine's function,
not a driver. -/
def rankTape (g : UnseqGraph) (order : List Nat) : Option (List Nat) := Id.run do
  let mut st := g.initStatus
  let mut tape : List Nat := []
  for i in order do
    let ready := g.ready st
    match ready.findIdx? (· == i) with
    | some j => tape := tape ++ [j]; st := st.set i .done
    | none => return none
  return some tape

def permutations3 : List (List Nat) :=
  [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]]

/-! ## Main -/

def main (_args : List String) : IO Unit := do
  let checks : List (IO Bool) := [
    -- W1–W6
    expectSet "W1 mut()+a" w1 "main" [okZ 1, okZ 2],
    expectSet "W2 a[b[0]]+mut()" w2 "main" [okZ 10, okZ 30, okZ 40],
    expectSet "W3 a[i]+=mut()" w3 "main" [okOut "w3 11 20\n", okOut "w3 10 21\n"],
    expectSet "W4 a[1]+b[2] both nil" w4 "main" [panicOut (oob 1 0), panicOut (oob 2 0)],
    expectSet "W5 loop: stale binders impossible" w5 "main" [panicOut (oob 0 0) "", panicOut (oob 0 0) "7\n"],
    expectSet "W6 x+inc()+inc()" w6 "main" [okZ 0, okZ 1, okZ 2],
    -- X1–X3
    expectSet "X1 xs[ys[9]], b = zs[7], 2" x1 "main" [panicOut (oob 9 3), panicOut (oob 7 3)],
    expectSet "X2 b2i(z||h())+x, z=false" (x2 false) "main" [okZ 2, okZ 3],
    expectSet "X2 b2i(z||h())+x, z=true" (x2 true) "main" [okZ 2],
    expectSet "X3 x[f()] += <-ch, buffered" (x3 true) "main"
      [panicOut (oob 9 1) "len 0\n", panicOut (oob 9 1) "len 1\n"],
    expectRefusal "X3e x[f()] += <-ch, EMPTY channel: blocked is a refusal apart from the members" (x3 false) "main" "deadlock",
    expectTape "X3e canonical tape: the panic member (the receive never ran)" (x3 false) "main" []
      (panicOut (oob 9 1) "len 0\n"),
    -- R1
    expectSet "R1 x+y+mut(), unreduced" (r1 false) "main" [okZ 0, okZ 1, okZ 2, okZ 3],
    expectSet "R1 REDUCED (R_x→R_y): loses 1 — the refuted reduction, as a NEGATIVE" (r1 true) "main" [okZ 0, okZ 2, okZ 3],
    -- R2
    expectSet "R2a sink(z||h(), k()), z=true" (r2a true true) "main" [okOut "guard k\nguard result true 7\n"],
    expectSet "R2a sink(z||h(), k()), z=false" (r2a false true) "main" [okOut "guard h\nguard k\nguard result true 7\n"],
    expectRefusal "R2a INVALID join: k value-depends on the skipped h" (r2a true false) "main" "confined to a skipped region",
    expectSet "R2b E1 anchored at COMPLETION" (r2b "C_or") "main" [okOut "logical false 0\n"],
    expectSet "R2b E1 anchored at guard ENTRY (refuted)" (r2b "G") "main" [okOut "logical false 0\n", okOut "logical true 0\n"],
    expectSet "R2c nested guards, b=true" (r2c true) "main" [okOut "g\nk\nsink 1 true 7\n", okOut "g\nh\nk\nsink 1 true 7\n"],
    expectSet "R2c nested guards, b=false" (r2c false) "main" [okOut "g\nk\nsink 1 true 7\n", okOut "g\nk\nsink 1 false 7\n"],
    -- R4, R6
    expectSet "R4 old := a; a[0] += mut() (mut rebinds a)" r4 "main" [okOut "old 11 20\na 100 200\n", okOut "old 10 20\na 101 200\n"],
    expectSet "R6 a[f()] SPLIT header/index producers" (r6 true) "main" [okZ 10, okZ 20],
    expectSet "R6 a[f()] FUSED read (the narrowing)" (r6 false) "main" [okZ 20],
    -- Controls
    expectSet "C1 f(g())" c1 "main" [okZ 8],
    expectSet "C2 sink(a)" c2 "main" [okZ 3],
    expectSet "C3 sink(a, mut())" c3 "main" [okZ 1, okZ 2],
    expectRefusal "C4 cycle A↔B" c4 "main" "no ready occurrence",
    -- Singleton picks consume nothing
    expectTape "C1 singleton picks: the tape is untouched" c1 "main" [5, 6] (okZ 8) (some [5, 6]),
    expectTape "C2 singleton picks: the tape is untouched" c2 "main" [7] (okZ 3) (some [7]),
    -- Malformed graphs by name
    expectRefusal "malformed: unknown slot" (malformed mUnknownSlot) "main" "unknown slot",
    expectRefusal "malformed: duplicate result" (malformed mDupResult) "main" "duplicate result",
    expectRefusal "malformed: load through a VALUE binder (sort mismatch)" (malformed mSortLoad) "main" "sort mismatch",
    expectRefusal "malformed: TARGET binder used as a value (sort mismatch)" (malformed mSortTargetAsValue) "main" "sort mismatch",
    expectRefusal "malformed: unknown occurrence reference" (malformed mUnknownAfter) "main" "unknown occurrence reference",
    expectRefusal "malformed: a cell produced by no occurrence" (malformed mUnproduced) "main" "produced by no occurrence",
    -- Target identity
    expectSet "target: pointer redirection (frozen pointee)" ptr "main" [okOut "x y 11 100\n", okOut "x y 10 101\n"],
    expectSet "target: cell mutation at a stable address" cell "main" [okOut "a 11\n", okOut "a 101\n"],
    expectRefusal "target: frozen map-element plan (Stage E)" mapProg "main" "frozen map-element plan",
    -- Recursion
    expectSet "recursion: per-activation binder cells" recursion "main" [okZ 10],
    -- Audit fix round (2026-09-16): F1
    expectRefusal "F1/A4 phase-2 store of a SKIPPED producer's binder (z=true): refused by name" (a4 true) "main" "was not produced",
    expectSet "F1/A4 control (z=false): h runs, 42 stored" (a4 false) "main" [okOut "h ran\nout 42\n"],
    expectRefusal "F1/A5 thenB reads a SKIPPED producer's cell (z=true): refused by name" (a5 true (println [str "h", .var "$h"])) "main" "was not produced",
    expectSet "F1/A5 control (z=false): h runs, thenB reads 42" (a5 false (println [str "h", .var "$h"])) "main" [okOut "h ran\nh 42\n"],
    expectSet "F1 the legitimate join: thenB reads the skipped region's COMPLETION binder (z=true)" (a5 true (println [str "c", .var "$cor"])) "main" [okOut "c true\n"],
    expectSet "F1 the legitimate join, region enabled (z=false)" (a5 false (println [str "c", .var "$cor"])) "main" [okOut "h ran\nc true\n"],
    expectRefusal "A8 store through a TARGET binder from a skipped region: refused by name (pre-existing)" a8 "main" "has not been produced",
    expectRefusal "A3 (R2) a use confined to a LATER-skipped region: refused by name" a3 "main" "confined to a skipped region",
    -- F2
    expectRefusal "F2/C1 R4 plan anchored at &a (a slice VARIABLE's address): refused by name — no hybrid" (r4with c1Graph) "main" "SLICE VARIABLE",
    expectSet "F2/C1b R4 plan with the header READ at the plan step (.var a): the frozen R4 set" (r4with c1bGraph) "main" [okOut "old 11 20\na 100 200\n", okOut "old 10 20\na 101 200\n"],
    expectSet "F2 an ARRAY variable's address is a stable anchor: accepted" arrProg "main" [okOut "one\narr 11 20\n"],
    -- F3
    expectRefusal "F3/B4 a bare (non-$) cell name would shadow the source local: refused by name" b4 "main" "not a reserved `$` slot name",
    expectRefusal "F3 a bare (non-$) target binder: refused by name" (malformed mBareTarget) "main" "not a reserved `$` slot name",
    -- N3
    expectRefusal "N3/K4 guard completion cell typed int: refused by name at ENTER" (k4 .bool .int) "main" "not a bool cell",
    expectRefusal "N3 guard test cell typed int: refused by name at ENTER" (k4 .int .bool) "main" "not a bool cell",
    -- R5
    expectSet "R5/K2 x := a + f() via .initialization in thenB, mid-block, two sweeps" k2 "main" [okOut "x 3\nx y 3 12\n"],
    expectSet "R5/K3 the same in a loop body: a fresh x per iteration" k3 "main" [okOut "x 3\nx 4\n"],
    -- Replay
    expectSet "replay graph: three unordered events" trace "main"
      (permutations3.map fun p => okOut (String.join (p.map fun i => ["A\n", "B\n", "C\n"][i]!)))]
  let replays : List (IO Bool) := permutations3.map fun p =>
    match rankTape trGraph p with
    | none => fail s!"replay: order {p} has no rank tape"
    | some tape =>
        expectTape s!"replay: order {p} via rank tape {tape}" trace "main" tape
          (okOut (String.join (p.map fun i => ["A\n", "B\n", "C\n"][i]!)))
  let mut failuresN := 0
  for c in checks ++ replays do
    if !(← c) then failuresN := failuresN + 1
  if failuresN == 0 then IO.println "Unseq scheduler (Stage B): PASS — every reference set exact, every refusal named"
  else
    IO.eprintln s!"Unseq scheduler (Stage B): FAIL — {failuresN} check(s) failed"
    IO.Process.exit 1

end Tests.UnseqScheduler

def main := Tests.UnseqScheduler.main
