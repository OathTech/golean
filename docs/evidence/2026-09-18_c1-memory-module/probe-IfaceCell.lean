import GoLean.GoCore.Ops
namespace GoLean.GoCore.Machine
open GoLean

def ctx0 : ProgramCtx := ProgramCtx.ofTables (types := #[])
def ifaceStore : Store :=
  { heap := #[.value (.interface ⟨"any"⟩) (.array #[.int 0 .int, .int 1 .int])] }
def leaf : Loc := .index (.base ⟨0⟩) 0
#eval HeapNormal ctx0 ifaceStore
#eval loadLoc ctx0 ifaceStore leaf
#eval (storeLoc ctx0 ifaceStore leaf (.int 5 .int)).map (fun s => loadLoc ctx0 s leaf)
#eval (storeLoc ctx0 ifaceStore leaf (.int 5 .int)).map (fun s => decide (HeapNormal ctx0 s))

def structStore : Store :=
  { heap := #[.value (.interface ⟨"any"⟩) (.struct ⟨"main.A"⟩ #[("f", .int 0 .int)])] }
def fleaf : Loc := .field (.base ⟨0⟩) ⟨"main.A"⟩ "f"
#eval HeapNormal ctx0 structStore
#eval (storeLoc ctx0 structStore fleaf (.int 5 .int)).map (fun s => loadLoc ctx0 s fleaf)

-- the other identity-class kinds: a `.slice`-declared cell holding an ARRAY
def sliceStore : Store :=
  { heap := #[.value (.slice .int) (.array #[.int 0 .int, .int 1 .int])] }
#eval HeapNormal ctx0 sliceStore
#eval (storeLoc ctx0 sliceStore leaf (.int 5 .int)).map (fun s => loadLoc ctx0 s leaf)

-- a NON-normal control: an `.int`-declared cell holding an array — both refuse
def intStore : Store :=
  { heap := #[.value (.int .int) (.array #[.int 0 .int, .int 1 .int])] }
#eval HeapNormal ctx0 intStore
#eval (storeLoc ctx0 intStore leaf (.int 5 .int)).map (fun s => loadLoc ctx0 s leaf)

-- the leaf is normalized at the identity: a width-wide int stays as given
#eval (storeLoc ctx0 ifaceStore leaf (.int 300 .int8)).map (fun s => loadLoc ctx0 s leaf)
end GoLean.GoCore.Machine
