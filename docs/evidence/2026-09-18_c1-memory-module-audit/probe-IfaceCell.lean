import GoLean.GoCore.Ops
namespace GoLean.GoCore.Machine
open GoLean

-- An `.interface`-declared value cell holding an ARRAY. `isNormalForTyTy (.interface _) _ = true`,
-- so this store satisfies `HeapNormal`. A path write `.index (.base 0) 0` into it:
-- old `storeLoc` (leaf-first: load base → arraySet → store root, normalize at .interface = identity) SUCCEEDS;
-- new `storeLoc` (root-first: `Ty.stepDown (.interface _) (.index _)`) REFUSES.
def ctx0 : ProgramCtx := ProgramCtx.ofTables #[] #[] #[] #[] #[]
def ifaceStore : Store :=
  { heap := #[.value (.interface ⟨"any"⟩) (.array #[.int 0 .int, .int 1 .int])] }
def leaf : Loc := .index (.base ⟨0⟩) 0

#eval HeapNormal ctx0 ifaceStore            -- expect: true (the cell is "normal")
#eval loadLoc ctx0 ifaceStore leaf           -- expect: ok (int 0)   (the old read path is unchanged)
#eval (storeLoc ctx0 ifaceStore leaf (.int 5 .int)).map (fun s => loadLoc ctx0 s leaf)
-- expect (candidate): error "leaf descent: the declared type has no element type"

-- Same shape with a STRUCT under an interface-declared cell and a .field path
def structStore : Store :=
  { heap := #[.value (.interface ⟨"any"⟩) (.struct ⟨"main.A"⟩ #[("f", .int 0 .int)])] }
def fleaf : Loc := .field (.base ⟨0⟩) ⟨"main.A"⟩ "f"
#eval HeapNormal ctx0 structStore
#eval (storeLoc ctx0 structStore fleaf (.int 5 .int)).map (fun s => loadLoc ctx0 s fleaf)
end GoLean.GoCore.Machine
