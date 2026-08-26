import GoLeanProofs.SliceMem
import GoLeanProofs.Specs.Raft.AbsStateV2

/-! # A4-U10 probe 3: #eval-check the SpillTransport witness numbers
BEFORE asking the kernel (the CLAUDE.md decide-family rule). -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.RaftSeam

#eval s!"width(0,1) = {appendSpillWidth 0 1} (expect 32)"
#eval s!"realizedCap(0,1,0) = {GoLean.SliceMem.appendRealizedCap 0 1 0} (expect 4)"
#eval s!"growthCap(0,1) = {appendGrowthCap 0 1} (expect 4)"

def witHeap : GoCore.Heap :=
  [(.base ⟨0⟩, ⟨some (.slice (.int .uint64)), .slice ⟨none, 0, 0, 0⟩⟩),
   (.base ⟨1⟩, ⟨some (.array 1 (.int .uint64)), .array #[.int 7 .uint64]⟩)]

def witσ : ExecState := { wBase with heap := witHeap, nextAddr := 2 }

def witC : Machine.Config :=
  .retV (.slice ⟨some (.base ⟨1⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice (.int .uint64)) 1
      [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨0⟩)] [] [] .stop)

def witExpectedHeap : GoCore.Heap :=
  [(.base ⟨0⟩, ⟨some (.slice (.int .uint64)),
      .slice ⟨some (.base ⟨2⟩), 0, 1, 4⟩⟩),
   (.base ⟨1⟩, ⟨some (.array 1 (.int .uint64)), .array #[.int 7 .uint64]⟩),
   (.base ⟨2⟩, ⟨some (.array 4 (.int .uint64)),
      .array #[.int 7 .uint64, .int 0 .uint64, .int 0 .uint64,
               .int 0 .uint64]⟩)]

#eval match stepFn witσ witC [0, 9, 9] with
  | .ok (c, σ', ch) =>
      let cOk := match c with | .next .stop => true | _ => false
      s!"step ok: cfg-stop={cOk} heap=={σ'.heap == witExpectedHeap} " ++
      s!"na={σ'.nextAddr} (expect 3) ch={ch} (expect [9,9])"
  | .error e => s!"ERROR {e.message}"

-- premise sanity: sliceVisibleValues + builder at the witness state
#eval toString (repr (sliceVisibleValues witσ ⟨some (.base ⟨1⟩), 0, 1, 1⟩))
#eval toString (repr (sliceVisibleValues witσ ⟨none, 0, 0, 0⟩))
#eval toString (repr (buildAppendBackingValue witσ (.int .uint64) #[]
  #[.int 7 .uint64] 4))
#eval toString (repr (Choices.consume [0, 9, 9] (appendSpillWidth 0 1)))
