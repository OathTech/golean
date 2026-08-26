import GoLeanProofs.Specs.Raft.SeedLitVar
import GoLeanProofs.Specs.Raft.SeedPin

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.RaftSeam GoLean.ChoiceErase

def pr {α : Type} [Repr α] (x : α) : String := ((repr x).pretty 110)

def go : IO Unit := do
  let cf := canonStateM twinLatMask seedσ seedRoots
  let mut out := "import GoLeanProofs.Frame.ChoiceCanon\n\n"
  out := out ++ "/-! # seedCForm — GENERATED (SP1; generator\n"
  out := out ++ "`artifacts/probe/SeedCFormGen.lean` — DO NOT EDIT BY HAND).\n\n"
  out := out ++ "The PINNED masked canonical form of the seed representative\n"
  out := out ++ "(`canonStateM twinLatMask seedσ seedRoots`): 207 live cells,\n"
  out := out ++ "flags []. Trust: `SeedPin.seed_cform_pin` kernel-recomputes the\n"
  out := out ++ "canonicalization against this literal on every build; the\n"
  out := out ++ "witness (`SeedWitness.seedVar_cform_pin`) lands the VARIANT\n"
  out := out ++ "run's canonicalization on the SAME literal — equivalence by\n"
  out := out ++ "shared pin (the tree-propagation route: never compare two\n"
  out := out ++ "computed forms head-on). -/\n\n"
  out := out ++ "namespace GoLean.RaftSeam\n\n"
  out := out ++ "open GoLean.ChoiceErase\n\n"
  out := out ++ "set_option maxRecDepth 8000000\n\n"
  out := out ++ s!"def seedCFormRoots : List CVal :=\n  {pr cf.roots}\n\n"
  let cellStrs := cf.cells.map (fun c => s!"⟨{pr c.ty},\n {pr c.val}⟩")
  out := out ++ s!"def seedCFormCells : List CCell :=\n  [" ++ String.intercalate ",\n   " cellStrs ++ "]\n\n"
  out := out ++ s!"def seedCForm : CForm :=\n  ⟨seedCFormRoots, seedCFormCells, []⟩\n\n"
  out := out ++ "end GoLean.RaftSeam\n"
  IO.FS.writeFile "GoLeanProofs/Specs/Raft/SeedCFormLit.lean" out
  IO.println s!"written {out.length} chars; flags={reprStr cf.flags}"

#eval go
