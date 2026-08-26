import GoLeanProofs.Specs.Raft.RoundMaLemma
import GoLeanProofs.Specs.Raft.RoundVoteLemma
import GoLeanProofs.Specs.Raft.RoundMarLemma
import GoLeanProofs.Specs.Raft.RoundVrLemma
import GoLeanProofs.Specs.Raft.SeedPin

/-! A4-U26 slice-1 probe (PROBE FIRST, per charter): the successor-canon
design's decisive questions, #eval'd before anything is built.

Q1. Are the four round kinds' loop-head configs LITERALLY EQUAL?
    (If yes, cross-kind literal chaining is config-compatible and the
    generic induction can share one C0.)
Q2. Do the eight canon states (pre/post x 4 kinds) canonicalize CLEANLY
    at twin-rooted masked forms (flags = [])? A resisting state is a
    chartered stop condition.
Q3. Do any landed cross-kind adjacencies exist at ~m (post of one kind =
    pre of another up to the mask)? Expected NO (doctored fixtures);
    recorded either way.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.RaftSeam
open GoLean.ChoiceErase

deriving instance Repr for GoLean.GoCore.Machine.Cont
deriving instance Repr for GoLean.GoCore.Machine.Config

def tw : List GoValue := [GoValue.addr (.base ⟨121⟩)]

-- ===== Q1: C0 cross-kind equality (repr-string compare, probe-only) =====
#eval do
  let a := toString (repr RoundMa.roundC0)
  let b := toString (repr RoundVote.roundVoteC0)
  let c := toString (repr RoundMar.roundMarC0)
  let d := toString (repr RoundVr.roundVrC0)
  IO.println s!"Q1 C0eq Ma=Vote:{a == b} Ma=Mar:{a == c} Ma=Vr:{a == d}"

-- ===== Q2: canonicalization cleanliness at twin roots, masked =====
def probeForm (tag : String) (σ : ExecState) : IO Unit := do
  let f := canonStateM twinLatMask σ tw
  IO.println s!"Q2 {tag}: cells={f.cells.length} flags={f.flags}"

#eval probeForm "canonMa " RoundMa.canonMa
#eval probeForm "canonMa'" RoundMa.canonMa'
#eval probeForm "canonVote " RoundVote.canonVote
#eval probeForm "canonVote'" RoundVote.canonVote'
#eval probeForm "canonMar " RoundMar.canonMar
#eval probeForm "canonMar'" RoundMar.canonMar'
#eval probeForm "canonVr " RoundVr.canonVr
#eval probeForm "canonVr'" RoundVr.canonVr'

-- ===== Q3: cross-kind ~m adjacency (post vs pre), twin-rooted =====
def cmpForms (tag : String) (σ σ' : ExecState) : IO Unit := do
  let f := canonStateM twinLatMask σ tw
  let g := canonStateM twinLatMask σ' tw
  IO.println s!"Q3 {tag}: eq={toString (repr f) == toString (repr g)}"

-- the real run's plausible adjacency: election completion (anchor 2->3)
-- then commit family (doctored at anchor 3)
#eval cmpForms "Vr'->Mar " RoundVr.canonVr' RoundMar.canonMar
-- vote round post vs vote-resp round pre (anchor 1->2-ish)
#eval cmpForms "Vote'->Vr " RoundVote.canonVote' RoundVr.canonVr
-- append post vs commit pre (Ma' -> Mar)
#eval cmpForms "Ma'->Mar " RoundMa.canonMa' RoundMar.canonMar
