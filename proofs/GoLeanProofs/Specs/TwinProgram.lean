import GoLeanProofs.Specs.WirePin

/-!
# The choice-driven raft twin — the frontend's lowering, pinned
(campaign Arc 1, U-c3)

`twinLowered` is the native frontend's ACTUAL lowering of the
choice-driven twin driver (`tools/raftsubject/twin-chdriver.go` +
`twin-lib.go` + the thin main, over the derived subject packages —
the runprobe assembly), decoded at elaboration from the checked-in
wire `baselines/golden/twin-chdriver.wire.json` (sha256 f353c3b2…,
9,310,086 bytes; emission is deterministic — two independent
frontend runs, one sha) by the wire-pin mechanism (`WirePin.lean`):
the term below IS the decoded `Program`, and a wire that fails to
read or decode fails THIS BUILD, loudly. "Proof subject =
decoded(frontend(source))", at library scale.

Statement-side module: no Iris, no semantics imports beyond syntax
(via WirePin's imports).
-/

namespace GoLean.Examples.RaftTwin

set_option maxRecDepth 4000000 in
/-- The frontend's lowering of the choice-driven twin, verbatim
(elaboration-time decode of the pinned wire). `maxRecDepth` raised
for the reflection only — the library's AST is deep, and the derived
`ToExpr` walk recurses with it. -/
def twinLowered : GoLean.GoCore.Program :=
  goldenWire% "baselines/golden/twin-chdriver.wire.json"

end GoLean.Examples.RaftTwin
