import GoLean.GoCore.Admission
import GoLean.GoCore.StepFn

open GoLean GoLean.GoCore GoLean.GoCore.Admission

namespace A3Adversarial

def f : Func := { id := ⟨"F"⟩, args := #[], results := #[], body := .returnStmt }
def p : Program := { funcs := #[f] }
def withType (t : TypeDef) : Program := { p with typeDefs := p.typeDefs.push (⟨"unused"⟩, t) }
def withBody (s : Stmt) : Program := { p with funcs := #[{f with body := s}] }
def bad : Ty := .defined 999

def probeCases : List (String × Except Error Unit × Except Error Unit) := [
  ("accepted basic entry", checkBoolean p "F" #[], .ok ()),
  ("nested map/function pointer metadata", checkIndices (withType (.defined (.funcType [.map .bool (.pointer bad)] [.chan .recv (.slice bad)] false))), .error .typeIndexBounds),
  ("interface method result metadata", checkIndices (withType (.interfaceDef #[{name := "M", params := #[], results := #[.array 2 (.pointer bad)]}])) , .error .typeIndexBounds),
  ("unreachable function results", checkIndices {p with funcs := #[f, {f with id := ⟨"Hidden"⟩, results := #[{id := "r", typ := .pointer bad}]}]}, .error .typeIndexBounds),
  ("method receiver metadata", checkIndices {p with methods := #[{name := "M", funcId := ⟨"missing"⟩, recv := .pointer bad}]}, .error .typeIndexBounds),
  ("global type metadata", checkIndices {p with globals := #[{name := "g", typ := .pointer bad}]}, .error .typeIndexBounds),
  ("select send head type", checkIndices (withBody (.selectStmt #[(.send (.boolLit true) (.boolLit false) bad, .returnStmt)] none)), .error .typeIndexBounds),
  ("select receive map target type", checkIndices (withBody (.selectStmt #[(.recv #[.mapElem (.boolLit true) (.boolLit false) .bool bad] (.boolLit true) .bool, .returnStmt)] none)), .error .typeIndexBounds),
  ("select default nested optional expression", checkIndices (withBody (.selectStmt #[] (some (.makeSlice (.var "x") .bool (.boolLit true) (some (.length (.boolLit true) (some bad))))))), .error .typeIndexBounds),
  ("type-assert source annotation", checkIndices (withBody (.assign (.var "x") (.typeAssert (.boolLit true) .bool (some bad)))), .error .typeIndexBounds),
  ("array literal child annotation", checkIndices (withBody (.assign (.var "x") (.arrayLit 1 .bool #[(0, .nil (some bad))]))), .error .typeIndexBounds),
  ("metadata names deliberately unchecked", checkBoolean {p with methodSets := #[{key := "arbitrary bad carrier", coverage := .full}], typeDisplays := #[(⟨"missing"⟩, {name := "bogus"})]} "F" #[], .ok ()),
  ("unbound variable explicitly accepted limitation", checkBoolean (withBody (.assign (.var "unbound") (.boolLit true))) "F" #[], .ok ()),
  ("unsupported dead helper rejected", checkBoolean {p with funcs := #[f, {f with id := ⟨"Unused"⟩, body := .unsupported "dead helper"}]} "F" #[], .error .booleanSyntaxPolicy),
  ("Boolean initializer function excluded", checkBoolean {p with funcs := #[f, {f with id := pkgInitFuncId}]} "F" #[], .error .booleanSyntaxPolicy),
  ("wrong entry payload rejected", checkBoolean {p with funcs := #[{f with args := #[{id := "b", typ := .bool}]}]} "F" #[.interface bad (.bool true)], .error .initialArgumentTypes)
]

def largeProgram (n : Nat) : Program :=
  { funcs := ((List.range n).map (fun i => {f with id := ⟨s!"F{i}"⟩})).toArray }

def sameResult : Except Error Unit → Except Error Unit → Bool
  | .ok _, .ok _ => true
  | .error a, .error b => decide (a = b)
  | _, _ => false

def main : IO UInt32 := do
  let mut failed := 0
  for (name, actual, expected) in probeCases do
    if sameResult actual expected then
      IO.println s!"PASS {name}"
    else
      failed := failed + 1
      IO.println s!"FAIL {name}: actual {repr actual}; expected {repr expected}"
  let start ← IO.monoMsNow
  let n := ((← IO.getEnv "A3_REVIEW_FUNCTIONS").bind String.toNat?).getD 3000
  let large := largeProgram n
  let practical := checkBoolean large s!"F{n-1}" #[]
  let elapsed := (← IO.monoMsNow) - start
  IO.println s!"{large.funcs.size}-function compiled checker: {repr practical}; {elapsed} ms"
  if practical matches .error _ then failed := failed + 1
  let tailBad := {large with funcs := large.funcs.push {f with id := ⟨"UnusedBadTail"⟩, body := .unsupported "adversarial tail"}}
  let tailResult := checkBoolean tailBad "F0" #[]
  IO.println s!"Large unreachable unsupported tail: {repr tailResult}"
  unless sameResult tailResult (.error .booleanSyntaxPolicy) do failed := failed + 1
  let run := Machine.runProgramM 100 (withBody (.assign (.var "unbound") (.boolLit true))) "F" #[] []
  IO.println s!"Accepted unbound-variable runtime limitation: {repr run}"
  return if failed = 0 then 0 else 1

end A3Adversarial

def main : IO UInt32 := A3Adversarial.main
