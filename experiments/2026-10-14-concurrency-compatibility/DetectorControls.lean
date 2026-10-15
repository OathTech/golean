import GoLean.GoCore.Race

/-! Executable old/new differential controls. Run this SAME source against an
isolated archived C1 build and the candidate, then byte-compare stdout. Finite
controls support the derivation argument; they are not an equivalence theorem. -/
open GoLean GoLean.GoCore GoLean.GoCore.Machine

def locations : List Loc :=
  let roots := [Loc.base ⟨0⟩, .base ⟨1⟩, .base ⟨65536⟩]
  let layer := fun (l : Loc) =>
    [l.field ⟨""⟩ "", l.field ⟨"A"⟩ "f", l.field ⟨"B"⟩ "f",
     l.field ⟨"A"⟩ "λ", l.index (-1), l.index 0, l.index 1]
  roots ++ roots.flatMap layer ++
    [((Loc.base ⟨0⟩).field ⟨"A"⟩ "f").index (-2),
     ((Loc.base ⟨0⟩).index 0).field ⟨"B"⟩ "f",
     (((Loc.base ⟨0⟩).field ⟨"A"⟩ "f").index 1).field ⟨"Z"⟩ "g"]

def keys : List ShadowKey := locations.flatMap fun l =>
  [.data l, .data l.canon, .chanObj l,
   .syncWord l .mutex .state, .syncWord l .rwmutex .readerCount,
   .syncWord l .waitGroup .sema, .syncWord l .once .done,
   .syncWord l .rwmutex .w, .syncWord l .once .m]

def main : IO Unit := do
  for a in locations do
    for b in locations do IO.println s!"loc {reprStr (compare a b)}"
  for a in keys do
    for b in keys do IO.println s!"key {reprStr (compare a b)}"
  for order in [keys, keys.reverse, keys ++ keys.reverse] do
    let mut shadow : List (ShadowKey × ShadowCell) := []
    let mut epoch := 0
    for key in order do
      epoch := epoch + 1
      shadow := shadowSet shadow key (({} : ShadowCell).record .write 1 epoch)
    IO.println s!"shadow {reprStr shadow}"
    let r : RaceState := { shadow := shadow }
    for key in keys do
      -- Includes overlapping distinct paths as well as exact replacement.
      IO.println s!"access {reprStr (r.accessKey 0 .read key)}"
