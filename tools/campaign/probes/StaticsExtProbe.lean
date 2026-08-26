import GoLean
import GoLeanProofs.Specs.TwinProgram

/-! # A4-U15 slice-1 probe: THE DISPATCH-COMPLEMENT EXTENSION contact.
Cells 16 (`ErrStopped`) / 17 (`ErrProposalDropped`) + their transitive
payload closure, from the same `$pkginit` dump as U12's StaticsProbe.
KEY QUESTION: do the payload addresses collide with the born-re-sited
leaf range [31,~64) (which would force a rename layer), or sit outside
it like the [20,31) payloads (all ≥ 71 — zero renaming)? -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Examples.RaftTwin (twinLowered)

def bigStream : Choices := List.replicate 4000 0

def twinBase : ExecState :=
  { types := twinLowered.typeDefs.toList, functions := twinLowered.funcs,
    methods := twinLowered.methods, methodSets := twinLowered.methodSets }

def postInit : Except GoError (ExecState × Choices) := do
  let s0 ← seedGlobals twinBase twinLowered.globals
  runPkgInitM 100000000 s0 bigStream

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

-- Phase A: dump cells 16/17 in full + their transitive closure.
#eval match postInit with
  | .error e => s!"init error: {e.message.take 300}"
  | .ok (s1, _) =>
      let roots := [Loc.base ⟨16⟩, Loc.base ⟨17⟩]
      let all := closure s1.heap roots roots 500
      let extra := all.filter (fun l => !(roots.contains l))
      s!"closure of 16/17: {toString (repr all)}\nnon-root referents: {toString (repr extra)}\n" ++
      String.intercalate "\n" (all.map (fun l =>
        match s1.heap.lookup l with
        | some c => s!"cell {(toString (repr l)).take 60}: ty={(toString (repr c.declaredTy)).take 110} val={(toString (repr c.value)).take 350}"
        | none => s!"cell {(toString (repr l)).take 60}: ABSENT"))

-- Phase B: collision check — any closure address inside [31,71)?
#eval match postInit with
  | .error e => s!"init error: {e.message.take 300}"
  | .ok (s1, _) =>
      let roots := [Loc.base ⟨16⟩, Loc.base ⟨17⟩]
      let all := closure s1.heap roots roots 500
      let inLeaf := all.filter (fun l => match l with
        | Loc.base a => 31 ≤ a.id && a.id < 71 | _ => false)
      s!"closure addrs in the leaf range [31,71): {toString (repr inLeaf)} (MUST be [] for zero-renaming)"

/-! ## Phase D: fail-closed extraction pipeline + literal emission
(the StaticCells recipe verbatim, roots [16,17], payloads [61,65]). -/

def staticExtRootIds : List Nat := [16, 17]
def staticExtPayloadIds : List Nat := [61, 65]

def staticComplementExtOf (init : Except GoError (ExecState × Choices)) :
    Option Heap :=
  match init with
  | .error _ => none
  | .ok (s1, _) =>
      (staticExtRootIds ++ staticExtPayloadIds).mapM (fun i =>
        (Heap.lookup s1.heap (.base ⟨i⟩)).map (fun c => ((.base ⟨i⟩ : Loc), c)))

#eval match staticComplementExtOf postInit with
  | some h => s!"ext complement: {h.length} cells (expect 4)"
  | none => "EXT EXTRACTION FAILED"

#eval show IO Unit from do
  match staticComplementExtOf postInit with
  | none => IO.println "EXTRACTION FAILED — no literal emitted"
  | some h =>
    let body := "[" ++ String.intercalate ",\n   " (h.map (fun (l, c) =>
      s!"({(repr l).pretty 10000000}, {(repr c).pretty 10000000})")) ++ "]"
    IO.FS.createDirAll "../artifacts/probe/gen"
    IO.FS.writeFile "../artifacts/probe/gen/StaticCellsExt.fragment"
      (s!"def staticComplementExt : Heap :=\n  {body}\n")
    IO.println s!"ext fragment written: {body.length} chars"
