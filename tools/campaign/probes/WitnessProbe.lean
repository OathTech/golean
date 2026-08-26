import GoLean
open GoLean GoLean.GoCore GoLean.GoCore.Machine

def main : IO Unit := do
  let txt ← IO.FS.readFile "baselines/golden/twin-chdriver.wire.json"
  let json ← match Lean.Json.parse txt with
    | .ok j => pure j | .error e => throw (IO.userError s!"parse: {e}")
  let prog ← match NativeToIR.decodeProgram json with
    | .ok p => pure p | .error e => throw (IO.userError s!"decode: {e}")
  let base : ExecState :=
    { types := prog.typeDefs.toList, functions := prog.funcs,
      methods := prog.methods, methodSets := prog.methodSets }
  -- default raftLog cell at 1, raft cell at 0 with raftLog ↦ addr 1
  let tyR : Ty := .defined ⟨"raft.raft"⟩
  let tyL : Ty := .defined ⟨"raft.raftLog"⟩
  match defaultValue base tyR, defaultValue base tyL with
  | .ok rv, .ok lv =>
    IO.println s!"defaults ok"
    match rv with
    | .struct tid fs =>
      IO.println s!"raft default tid={tid.key} fields={fs.size}"
      match StructFields.set fs "raftLog" (.addr (.base ⟨1⟩)) with
      | .ok fs2 =>
        let wσ : ExecState := { base with
          heap := [(.base ⟨0⟩, ⟨some tyR, .struct tid fs2⟩), (.base ⟨1⟩, ⟨some tyL, lv⟩)],
          nextAddr := 2 }
        match enterFrame wσ ⟨"raft.raft.abortLeaderTransfer"⟩ [.addr (.base ⟨0⟩)] with
        | .ok (f, fenv, locs, σ₁) =>
            IO.println s!"enterFrame ok: fenv={repr fenv} locs={locs.length} na={σ₁.nextAddr}"
            match stepFnIter 15 wσ (.retV (.addr (.base ⟨0⟩)) (.callArgsK ⟨"raft.raft.abortLeaderTransfer"⟩ [] [] [] [] .stop)) [] with
            | .ok (c', σ', ch') =>
                IO.println s!"15-step run ok: terminal config next-stop? {match c' with | .next .stop => true | _ => false} na={σ'.nextAddr} ch={ch'.length}"
                -- absRaftNode both sides
                IO.println s!"heap size {σ'.heap.length}"
                match Heap.lookup σ'.heap (.base ⟨0⟩) with
                | some cell =>
                    match cell.value with
                    | .struct _ fs3 =>
                        IO.println s!"post leadTransferee = {repr (StructFields.lookup fs3 "leadTransferee")}"
                        IO.println s!"post Term = {repr (StructFields.lookup fs3 "Term")}"
                    | _ => IO.println "post not struct?!"
                | none => IO.println "no cell"
            | .error e => IO.println s!"run error: {repr e}"
        | .error e => IO.println s!"enterFrame error: {repr e}"
      | .error e => IO.println s!"set error: {repr e}"
    | v => IO.println s!"raft default not struct: {(repr v).pretty 200}"
  | .error e, _ => IO.println s!"defaultValue raft error: {repr e}"
  | _, .error e => IO.println s!"defaultValue raftLog error: {repr e}"
