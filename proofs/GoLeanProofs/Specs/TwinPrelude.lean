import GoLeanProofs.Specs.TwinCheckpointsF

/-!
# The twin's prelude, kernel-pinned (campaign Arc 2, U4 — assembly
step 1 of the route memo §6.7 item 4 / design note §4)

Two kernel facts anchor the whole fast-run transport:

1. **The prelude equation**: `runProgramSetupM` at the witness fuel
   reduces to the reflected post-prelude tuple — the kernel re-runs
   the seed + `StateWf` + the 1,382 `$pkginit` steps against the
   emitted literals (measured cost class: the U1 K-ladder's
   init-phase rates).
2. **The γ-agreement**: the slow post-prelude state IS `γF` of the
   trie seed — this single equality is what replaces any carried
   trie well-formedness invariant (design note §2/§3): every
   downstream fast segment transports from exactly this state.

The literals are scaffolding-emitted (`twinPreludeF%`); these checks
are what guard them. UNTRUSTED METHOD — never in any statement
closure.
-/

namespace GoLean.Examples.RaftTwin

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.StateWire
open GoLean.FastEval

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 0 in
/-- The reflected post-prelude tuple:
`(c₀, heapT, nextAddr, resultLocs, ch₁)`. -/
def twinPre : Config × HeapT × Nat × List Loc × Choices := twinPreludeF%

/-- The seed fast state, from the prelude tuple. -/
def twinSeedF : ExecStateF :=
  { types := twinLowered.typeDefs.toList
    functions := twinLowered.funcs
    methods := twinLowered.methods
    methodSets := twinLowered.methodSets
    heapT := twinPre.2.1
    nextAddr := twinPre.2.2.1 }

set_option maxHeartbeats 0 in
set_option maxRecDepth 4000000 in
set_option smartUnfolding false in
/-- **The prelude equation** (kernel-checked): the statement's own
`runProgramSetupM` at the witness fuel lands exactly on the reflected
literals, with the slow state spelled as `γF twinSeedF`. -/
theorem twin_prelude_eq :
    runProgramSetupM 711616 twinLowered "twinChoiceVerdict" #[] =
      .ok (twinPre.1, γF twinSeedF, twinPre.2.2.2.1, twinPre.2.2.2.2) := by
  with_unfolding_all rfl

end GoLean.Examples.RaftTwin
