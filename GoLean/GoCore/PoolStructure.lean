import GoLean.GoCore.PoolStatement
import GoLean.GoCore.NPDRF

/-! Structural pool facts. [AGENT Codex, pool grind] 2026-10-05. -/
namespace GoLean.GoCore.PoolStructure
open GoLean GoLean.GoCore GoLean.GoCore.Machine

set_option linter.unusedSimpArgs false in
theorem applyPairing_shape {ctx : ProgramCtx} {s s' : Store} {ts ts' : Array Thread}
    {i : Nat} {bc : Config} {cand : Nat × PairTarget} {tr : AccessTrace}
    (h : applyPairing ctx s ts i bc cand = .ok (ts', s', tr)) :
    ∃ ti tj, ts' = (ts.setIfInBounds i ti).setIfInBounds cand.2.partnerIdx tj := by
  unfold applyPairing at h
  repeat' first
    | simp only [Bind.bind, Except.bind, pure_eq_ok,
        throw, throwThe, MonadExceptOf.throw] at h
    | split at h
  all_goals try simp only [Bind.bind, Except.bind, pure_eq_ok,
    throw, throwThe, MonadExceptOf.throw] at h
  all_goals cases h
  all_goals simp_all only [PairTarget.partnerIdx]
  all_goals exact ⟨_, _, rfl⟩

set_option linter.unusedSimpArgs false in
theorem applyPairing_trace {ctx : ProgramCtx} {s s' : Store} {ts ts' : Array Thread}
    {i : Nat} {bc : Config} {cand : Nat × PairTarget} {tr : AccessTrace}
    (h : applyPairing ctx s ts i bc cand = .ok (ts', s', tr)) :
    (∃ e, MemEvent.attributed cand.2.partnerIdx e ∈ tr) ∨
      MemEvent.hb (.rendezvous cand.2.partnerIdx) ∈ tr := by
  unfold applyPairing at h
  repeat' first
    | simp only [Bind.bind, Except.bind, pure_eq_ok,
        throw, throwThe, MonadExceptOf.throw] at h
    | split at h
  all_goals cases h
  all_goals simp_all only [PairTarget.partnerIdx]
  all_goals simp only [pairSendEvents, pairRecvEvents]
  all_goals first
    | (split <;> simp)
    | simp

end GoLean.GoCore.PoolStructure
