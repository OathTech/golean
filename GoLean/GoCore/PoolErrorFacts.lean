import GoLean.GoCore.PoolStatement

/-! Pool error helper proofs. [AGENT Codex, pool grind] 2026-10-05. -/

namespace GoLean.GoCore.PoolErrorFacts

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable {ctx : ProgramCtx}

private theorem chanCell_strict {s : Store} {loc : Loc} :
    ErrP Stop.Strict (chanCell s loc) := by errp

local macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact chanCell_strict)

private theorem readyClauses_strict {s : Store} : ∀ (evs : List EvClause),
    ErrP Stop.Strict (readyClauses s evs) := by
  intro evs
  induction evs with
  | nil => unfold readyClauses; errp
  | cons cl rest ih => unfold readyClauses; errp

local macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact readyClauses_strict _)

private theorem commitClause_strict {s : Store} {env : LocalEnv} {k : Cont} {cl : EvClause} :
    ErrP Stop.Strict (commitClause ctx s env k cl) := by errp

local macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact commitClause_strict)

private theorem spawnStep_strict {s : Store} {cv : GoValue} {args : List GoValue}
    {k : Cont} {ch : Choices} : ErrP Stop.Strict (spawnStep ctx s cv args k ch) := by
  errp

private theorem arrivalPlan_strict {s : Store} {ts : Array Thread} {i : Nat}
    {c : Config} {ch : Choices} : ErrP Stop.Strict (arrivalPlan ctx s ts i c ch) := by
  errp

private theorem applyPairing_strict {s : Store} {ts : Array Thread} {i : Nat}
    {bc : Config} {cand : Nat × PairTarget} :
    ErrP Stop.Strict (applyPairing ctx s ts i bc cand) := by
  errp

private theorem storeLoc_strict {s : Store} {loc : Loc} {v : GoValue} :
    ErrP Stop.Strict (storeLoc ctx s loc v) := by
  refine ErrP.strict_of_noPanic ?_ (storeLoc_noPanic _ _ _)
  errp

local macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact storeLoc_strict)

private theorem resumeThread_strict {s : Store} {c : Config}
    (hw : wakeReady ctx s c = true) : ErrP Stop.Strict (resumeThread ctx s c) := by
  unfold resumeThread
  split <;> errp
  intro e he
  simp [wakeReady, he] at hw

local macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact spawnStep_strict)
local macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact arrivalPlan_strict)
local macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact applyPairing_strict)

private theorem wakeReady_of_schedPick {m : MultiConfig} {i : Nat} {c : Config}
    (hs : schedPick ctx m i) (hi : m.threads[i]? = some (.running c none))
    (hb : isBlockedConfig c = true) : wakeReady ctx m.shared c = true := by
  have hmem : i ∈ runnableIdxs ctx m.shared m.threads := by
    unfold schedPick at hs
    split at hs
    · split at hs
      · exact hs
      · subst i
        have hat : Thread.atBoundary (.running c none) = true := by
          cases c <;> simp_all [isBlockedConfig, Thread.atBoundary, Config.atBoundary]
        simp_all
    · contradiction
  have hr := (List.mem_filter.mp hmem).2
  simp only [hi, threadRunnable, hb, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hr
  exact hr.2

theorem stepThread_strict {m : MultiConfig} {i : Nat} {ch : Choices}
    (hs : schedPick ctx m i) : ErrP Stop.Strict (stepThread ctx m.shared m.threads i ch) := by
  unfold stepThread
  split
  · errp
  · errp
  · errp
  · rename_i c hi
    split
    · rename_i hb
      exact ErrP.bind (resumeThread_strict (wakeReady_of_schedPick hs hi hb)) (fun _ => ErrP.pure)
    · rename_i hb
      have hnb : c.blockedB = false := by
        cases c <;> simp_all [Config.blockedB, isBlockedConfig]
      split
      · errp
      · rename_i hab
        have hf : ∀ ch, ErrP Stop.Strict (stepFn ctx m.shared c ch) :=
          fun _ => stepFn_strict hab hnb
        errp

end GoLean.GoCore.PoolErrorFacts
