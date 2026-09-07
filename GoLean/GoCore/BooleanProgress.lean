import GoLean.GoCore.BooleanInvariant

/-! Progress for the actual sequential machine in the Boolean profile.
All helper-success facts below are derived from the typed heap/environment,
not assumed as reachable safety or future execution. -/
namespace GoLean.GoCore.BooleanRuntime
open BooleanTyping Admission Machine

theorem expression_progress {Γ e env k s} (hc : Covers Γ env)
    (he : EnvRoots s env) (ht : ExprTyped Γ e) :
    ∃ c' t, Step (.evalE e env k) s c' t := by
  cases ht with
  | var hx =>
      obtain ⟨loc, hl⟩ := hc _ hx
      obtain ⟨b, hb⟩ := (he.lookup hl).load
      exact ⟨_, s, .evalVar hl hb⟩
  | literal b => exact ⟨_, s, .evalBoolLit⟩
  | not h => exact ⟨_, s, .evalStrict rfl⟩
  | and h₁ h₂ => exact ⟨_, s, .evalAnd⟩
  | or h₁ h₂ => exact ⟨_, s, .evalOr⟩

theorem statement_progress {Γ stmt env k s} (hc : Covers Γ env)
    (he : EnvRoots s env) (hh : BoolHeap s) (ht : ControlStmt false Γ stmt) :
    ∃ c' t, Step (.exec stmt env k) s c' t := by
  cases ht with
  | seqn hs => exact ⟨_, s, .seqn⟩
  | block ht hs =>
      obtain ⟨env', t, ha, _⟩ := block_setup hc he hh ht
      exact ⟨_, t, .block ha⟩
  | assign hx he => exact ⟨_, s, .assignFirst rfl⟩
  | branch he ht hf => exact ⟨_, s, .ifStmt⟩
  | ret => exact ⟨_, s, .signalStmt rfl⟩

theorem sequence_head_progress {Γ stmt rest env k s} (hc : Covers Γ env)
    (he : EnvRoots s env) (hh : BoolHeap s) (ht : ControlStmt true Γ stmt) :
    ∃ c' t, Step (.exec stmt env (.seq rest env k)) s c' t := by
  cases ht with
  | seqn hs => exact ⟨_, s, .seqn⟩
  | block ht hs =>
      obtain ⟨env', t, ha, _⟩ := block_setup hc he hh ht
      exact ⟨_, t, .block ha⟩
  | initialization ht =>
      exact ⟨_, _, .initialization (by rw [ht]; rfl) rfl⟩
  | assign hx he => exact ⟨_, s, .assignFirst rfl⟩
  | branch he ht hf => exact ⟨_, s, .ifStmt⟩
  | ret => exact ⟨_, s, .signalStmt rfl⟩

theorem bool_return_progress {k s} (h : BoolCont (BoolRoot s) (EnvRoots s) k) (b : Bool) :
    ∃ c' t, Step (.retV (.bool b) k) s c' t := by
  cases h with
  | not he hk =>
      exact ⟨_, s, .strictApply (r := .ok (.bool (!b), s)) rfl rfl⟩
  | and hc he ht hk =>
      cases b
      · exact ⟨_, s, .andFalse⟩
      · exact ⟨_, s, .andTrue⟩
  | or hc he ht hk =>
      cases b
      · exact ⟨_, s, .orFalse⟩
      · exact ⟨_, s, .orTrue⟩
  | coerce hk => exact ⟨_, s, .boolCoerce⟩
  | branch hc he ht hf hk =>
      cases b
      · exact ⟨_, s, .ifFalse⟩
      · exact ⟨_, s, .ifTrue⟩
  | rhs hl he hk => exact ⟨_, s, .rhsStores (r := .ok [.bool b]) rfl rfl⟩

theorem control_progress {s c} (hh : BoolHeap s) (h : TypedControl s c) :
    c = .next .stop ∨ ∃ c' t, Step c s c' t := by
  cases h with
  | terminal => exact .inl rfl
  | next hk =>
      apply Or.inr
      cases hk with
      | barrier => exact ⟨_, s, .frameFall⟩
      | @seq Γ env ss k hc he ht hk =>
          cases ss
          · exact ⟨_, s, .seqDone⟩
          · exact ⟨_, s, .seqNext⟩
  | exec hc he ht hk => exact .inr (statement_progress hc he hh ht)
  | execSeq hc he ht hrest hk => exact .inr (sequence_head_progress hc he hh ht)
  | evalBool hc he ht hk => exact .inr (expression_progress hc he ht)
  | evalRef hc he hx hk =>
      obtain ⟨loc, hl⟩ := hc _ hx
      exact .inr ⟨_, s, .evalRef hl⟩
  | @retBool b k hk => exact .inr (bool_return_progress hk b)
  | retAddr hl hk =>
      cases hk with
      | target hc he ht hk => exact .inr ⟨_, s, .tgtOpRhs rfl⟩
  | @store loc b env k hl he hk =>
      obtain ⟨t, ht, _⟩ := store_extension hh hl b
      have hs : storeTarget s (.chain (.addr loc) [] []) (.bool b) = .ok t := ht
      exact .inr ⟨_, t, .storeStep (r := .ok t) (by rw [hs]; rfl) rfl⟩
  | storeDone he hk => exact .inr ⟨_, s, .storeDone⟩
  | returning hk =>
      apply Or.inr
      cases hk with
      | barrier => exact ⟨_, s, .frameReturn⟩
      | seq hc he ht hk => exact ⟨_, s, .signal rfl⟩

theorem Inv.progress {context results s c} (h : Inv context results s c) :
    c = .next .stop ∨ ∃ c' t, Step c s c' t := control_progress h.heap h.control

end GoLean.GoCore.BooleanRuntime
