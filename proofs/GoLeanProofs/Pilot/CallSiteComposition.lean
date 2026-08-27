import GoLeanProofs.Pilot.BecomeFollowerSpec

/-!
# W1 pilot LEG B: the two-function composition — becomeFollower's
`CallSpec` consumed at a call site via the call rule

The pilot gate's second leg (clean-proof plan §W1): a CALLER-side
statement span produced from the CALLEE's `CallSpec` by the
statement-level call rule (`Spec.stmtSpec_call`): the caller's
argument-evaluation segment (six machine steps at the resultless
call-statement shape, discharged ∀-state by `rfl`-conditioned steps)
chains into the callee's whole span, yielding the `StmtSpec` of the
call statement — the composition mechanics W3's handler-into-driver
assembly rests on, exercised end-to-end.

**Honest scope (the leg's findings, reported prominently in the W1
log):**
- The caller shape here is the PASSIVE-arguments call statement
  (receiver by static address, scalar literals) — a real lowered
  shape, but not one of the subject's actual becomeFollower call
  sites: every real caller (`Step`, `stepLeader`, `restore`, …) is a
  large handler whose own span is W3 production work; its
  argument-evaluation premise is discharged by its own windows, the
  same way this leg discharges the passive shape.
- The FRAME half of the planned leg (consuming a spec at a FOREIGN
  placement) is NOT demonstrated here — the design-note §3 finding:
  `FrameSim` transport can never deliver the caller's env/k (they
  live exactly in the frame region), so framed consumption requires
  the PLUG RULE (wp_bind as a theorem, StepSim-scale) or same-
  placement layouts; recorded as the summit finding gating W3.
- Sequential chaining of TWO handler specs additionally needs
  FOOTPRINT-CARRIER postconditions (the reader-only postcondition
  does not re-establish the next spec's footprint precondition) —
  exactly the invariant `I`'s job in the plan's W2.5 design gate;
  recorded, not silently absorbed.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

/-- The argument-evaluation segment for the passive call shape: six
machine steps from the call statement to the drained call
configuration, at EVERY state, continuation, and stream — state- and
tape-passive (the `hargs` premise of the call rule). -/
private theorem bf_args_segment (leadArg : Int)
    (hlead : IntKind.normalize .uint64 leadArg = leadArg)
    (env : LocalEnv) (σ : ExecState) (k : Machine.Cont) (ch : Choices) :
    stepFnIter 6 σ
      (.exec (.call #[] ⟨"raft.raft.becomeFollower"⟩
        #[.locLit (.base ⟨0⟩), .intLit 0 .uint64,
          .intLit leadArg .uint64]) env k) ch
      = .ok (.retV (.int leadArg .uint64)
          (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
            [.addr (.base ⟨0⟩), .int 0 .uint64] [] env k), σ, ch) := by
  have h1 : stepFn σ
      (.exec (.call #[] ⟨"raft.raft.becomeFollower"⟩
        #[.locLit (.base ⟨0⟩), .intLit 0 .uint64,
          .intLit leadArg .uint64]) env k) ch
      = .ok (.evalE (.locLit (.base ⟨0⟩)) env
          (.callArgsK ⟨"raft.raft.becomeFollower"⟩ [] []
            [.intLit 0 .uint64, .intLit leadArg .uint64] env k),
          σ, ch) := rfl
  have h2 : stepFn σ
      (.evalE (.locLit (.base ⟨0⟩)) env
        (.callArgsK ⟨"raft.raft.becomeFollower"⟩ [] []
          [.intLit 0 .uint64, .intLit leadArg .uint64] env k)) ch
      = .ok (.retV (.addr (.base ⟨0⟩))
          (.callArgsK ⟨"raft.raft.becomeFollower"⟩ [] []
            [.intLit 0 .uint64, .intLit leadArg .uint64] env k),
          σ, ch) := rfl
  have h3 : stepFn σ
      (.retV (.addr (.base ⟨0⟩))
        (.callArgsK ⟨"raft.raft.becomeFollower"⟩ [] []
          [.intLit 0 .uint64, .intLit leadArg .uint64] env k)) ch
      = .ok (.evalE (.intLit 0 .uint64) env
          (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
            [.addr (.base ⟨0⟩)] [.intLit leadArg .uint64] env k),
          σ, ch) := rfl
  have h4 : stepFn σ
      (.evalE (.intLit 0 .uint64) env
        (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
          [.addr (.base ⟨0⟩)] [.intLit leadArg .uint64] env k)) ch
      = .ok (.retV (.int 0 .uint64)
          (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
            [.addr (.base ⟨0⟩)] [.intLit leadArg .uint64] env k),
          σ, ch) := rfl
  have h5 : stepFn σ
      (.retV (.int 0 .uint64)
        (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
          [.addr (.base ⟨0⟩)] [.intLit leadArg .uint64] env k)) ch
      = .ok (.evalE (.intLit leadArg .uint64) env
          (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
            [.addr (.base ⟨0⟩), .int 0 .uint64] [] env k),
          σ, ch) := rfl
  have h6 : stepFn σ
      (.evalE (.intLit leadArg .uint64) env
        (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
          [.addr (.base ⟨0⟩), .int 0 .uint64] [] env k)) ch
      = .ok (.retV (.int leadArg .uint64)
          (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
            [.addr (.base ⟨0⟩), .int 0 .uint64] [] env k),
          σ, ch) := by
    have hraw : stepFn σ
        (.evalE (.intLit leadArg .uint64) env
          (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
            [.addr (.base ⟨0⟩), .int 0 .uint64] [] env k)) ch
        = .ok (.retV (.int (IntKind.normalize .uint64 leadArg) .uint64)
            (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
              [.addr (.base ⟨0⟩), .int 0 .uint64] [] env k),
            σ, ch) := rfl
    rw [hraw, hlead]
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_one h1) (stepFnIter_one h2)) (stepFnIter_one h3))
    (stepFnIter_one h4)) (stepFnIter_one h5)) (stepFnIter_one h6)

/-- **LEG B — the two-function composition**: the `StmtSpec` of a
caller's becomeFollower call statement, produced from the callee's
`CallSpec` by the call rule. The caller's span (the statement from
`.exec … k` to `.next k`) contains the WHOLE callee span — two
functions composed through the judgment. -/
theorem becomeFollower_call_stmtSpec (vote lead state ldT leadArg : Int)
    (hvote : IntKind.normalize .uint64 vote = vote)
    (hlead : IntKind.normalize .uint64 leadArg = leadArg) :
    Spec.StmtSpec
      (fun _ σ => BfPre vote lead state ldT leadArg σ)
      (.call #[] ⟨"raft.raft.becomeFollower"⟩
        #[.locLit (.base ⟨0⟩), .intLit 0 .uint64, .intLit leadArg .uint64])
      (fun _ σ' => absRaftNode σ' ⟨0⟩
        = some (specBecomeFollower ⟨0, vote, lead, state, 1, 1⟩ 0
            leadArg)) :=
  Spec.stmtSpec_call
    (hargs := fun env σ _ k ch =>
      ⟨6, bf_args_segment leadArg hlead env σ k ch⟩)
    (himp := fun _ _ h => h)
    (hcallee := becomeFollower_callSpec vote lead state ldT leadArg
      hvote hlead)

end GoLean.RaftSeam
