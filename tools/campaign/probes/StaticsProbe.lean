import GoLean
import GoLeanProofs.Specs.TwinProgram

/-! # A4-U12 contact probe: THE STATIC-CELL COMPLEMENT.
Derive the exact `$pkginit` images of static cells [0,31): seed
globals + run `$pkginit` on the pinned twin, dump every low cell
(full repr) plus the transitive addr-referents, and report nextAddr
at each phase. Result of phase A: seeded heap=31, nextAddr=31,
globals=31 — the WHOLE [0,31) range is the static block. -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Examples.RaftTwin (twinLowered)

def bigStream : Choices := List.replicate 4000 0

def twinBase : ExecState :=
  { types := twinLowered.typeDefs.toList, functions := twinLowered.funcs,
    methods := twinLowered.methods, methodSets := twinLowered.methodSets }

def postInit : Except GoError (ExecState × Choices) := do
  let s0 ← seedGlobals twinBase twinLowered.globals
  runPkgInitM 100000000 s0 bigStream

#eval match postInit with
  | .error e => s!"init error: {e.message.take 300}"
  | .ok (s1, ch1) =>
      s!"init done: heap={s1.heap.length} nextAddr={s1.nextAddr} choicesConsumed={4000 - ch1.length}"

-- dump cells [0,31)
#eval match postInit with
  | .error e => s!"init error: {e.message.take 300}"
  | .ok (s1, _) =>
      String.intercalate "\n" ((List.range 31).map (fun i =>
        match s1.heap.lookup (.base ⟨i⟩) with
        | some c => s!"cell {i}: ty={(toString (repr c.declaredTy)).take 100} val={(toString (repr c.value)).take 300}"
        | none => s!"cell {i}: ABSENT"))

partial def refsOf : GoValue → List Loc
  | .addr l => [l]
  | .struct _ fs => fs.toList.flatMap (fun (_, v) => refsOf v)
  | .array a => a.toList.flatMap refsOf
  | .slice s => match s.base with | some l => [l] | none => []
  | .map m => match m.base with | some l => [l] | none => []
  | .mapData kvs => kvs.toList.flatMap (fun (k, v) => refsOf k ++ refsOf v)
  | .interface _ v => refsOf v
  | _ => []

partial def closure (h : Heap) (frontier : List Loc) (seen : List Loc)
    (fuel : Nat) : List Loc :=
  if fuel = 0 then seen else
  match frontier with
  | [] => seen
  | l :: rest =>
      match h.lookup l with
      | some c =>
          let new := (refsOf c.value).filter (fun r => !(seen.contains r))
          closure h (rest ++ new) (seen ++ new) (fuel - 1)
      | none => closure h rest seen (fuel - 1)

-- transitive referents of the whole static block
#eval match postInit with
  | .error e => s!"init error: {e.message.take 300}"
  | .ok (s1, _) =>
      let roots := (List.range 31).map (fun i => (Loc.base ⟨i⟩))
      let all := closure s1.heap roots roots 500
      let outside := all.filter (fun l => match l with
        | Loc.base a => a.id ≥ 31 | _ => true)
      s!"referents outside [0,31): {toString (repr outside)}\n" ++
      String.intercalate "\n" (outside.map (fun l =>
        match s1.heap.lookup l with
        | some c => s!"referent {(toString (repr l)).take 50}: ty={(toString (repr c.declaredTy)).take 90} val={(toString (repr c.value)).take 280}"
        | none => s!"referent {(toString (repr l)).take 50}: ABSENT"))

-- Phase C: init's machine step count via stepFnIter (the kernel-fact shape)
def initσ0 : Except GoError ExecState := seedGlobals twinBase twinLowered.globals
#eval match initσ0 with
  | .error e => s!"seed err {e.message}"
  | .ok s0 =>
    match findFunctionIn? twinBase.functions pkgInitFuncId with
    | none => "no $pkginit"
    | some f =>
      let c0 : Config := .exec f.body [] (.frame [] [] [] [] .stop)
      let rec walk (n : Nat) (σ : ExecState) (c : Config) (ch : Choices) (fuel : Nat) : String :=
        match fuel with
        | 0 => s!"NO STOP by {n}"
        | fuel + 1 =>
          match stepFn σ c ch with
          | .ok (Config.next .stop, σ2, ch2) => s!"init .next .stop at step {n+1}; na={σ2.nextAddr} heap={σ2.heap.length} chLeft={ch2.length}"
          | .ok (c2, σ2, ch2) => walk (n+1) σ2 c2 ch2 fuel
          | .error e => s!"init ERROR at {n+1}: {e.message.take 150}"
      walk 0 s0 c0 [] 100000

/-! ## Phase D (A4-U12 slice 2): the extraction pipeline prototype +
literal emission. The block = the [20,31) roots ++ their transitive
payload referents at their TRUE init addresses (all ≥ 71, above the
leaf fixture range [31,60]) — zero renaming; consumers set
nextAddr₀ = 98. Fail-closed: none on init error, missing cell, or
any referent outside the expected payload set. -/

def staticRootIds : List Nat := [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]
def staticPayloadIds : List Nat := [71, 75, 79, 83, 87, 91, 95, 97]

def staticComplementOf (init : Except GoError (ExecState × Choices)) :
    Option Heap := do
  match init with
  | .error _ => none
  | .ok (s1, _) =>
    -- roots, verbatim
    let mut out : Heap := []
    for i in staticRootIds do
      match s1.heap.lookup (.base ⟨i⟩) with
      | some c =>
        -- every referent must be in the payload set
        for r in refsOf c.value do
          match r with
          | .base a => if !(staticPayloadIds.contains a.id) then none else pure ()
          | _ => none
        out := out ++ [(.base ⟨i⟩, c)]
      | none => none
    -- payloads, verbatim, ref-free
    for i in staticPayloadIds do
      match s1.heap.lookup (.base ⟨i⟩) with
      | some c =>
        if !(refsOf c.value).isEmpty then none else pure ()
        out := out ++ [(.base ⟨i⟩, c)]
      | none => none
    pure out

#eval match staticComplementOf postInit with
  | some h => s!"complement: {h.length} cells (expect 19)"
  | none => "COMPLEMENT EXTRACTION FAILED"

-- emit the literal
#eval show IO Unit from do
  match staticComplementOf postInit with
  | none => IO.println "EXTRACTION FAILED — no literal emitted"
  | some h =>
    let body := "[" ++ String.intercalate ",\n   " (h.map (fun (l, c) =>
      s!"({(repr l).pretty 10000000}, {(repr c).pretty 10000000})")) ++ "]"
    IO.FS.createDirAll "../artifacts/probe/gen"
    IO.FS.writeFile "../artifacts/probe/gen/StaticCells.fragment"
      (s!"def staticComplement : Heap :=\n  {body}\n")
    IO.println s!"fragment written: {body.length} chars"
