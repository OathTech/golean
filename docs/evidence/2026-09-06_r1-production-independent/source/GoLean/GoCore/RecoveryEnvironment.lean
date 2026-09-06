import GoLean.GoCore.RecoveryStore

/-! Mixed environments retain the actual first matching storage location.
Hidden bindings are separately bounded: a shadowed pointer cannot evade the
structural machine invariant merely because ordinary lookup skips it. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

def BindingsTyped (world : World) (env : LocalEnv) : Prop :=
  ∀ scope ∈ env, ∀ binding ∈ scope, ∃ sort, AddressTyped world sort binding.2

structure EnvTyped (world : World) (Γ : Context) (env : LocalEnv) : Prop where
  bindings : BindingsTyped world env
  lookup : ∀ name ty, RecoveryTyping.lookup Γ name = some ty →
    ∃ loc, env.lookup name = some loc ∧ AddressAt world ty loc

theorem BindingsTyped.mono {world next env} (h : BindingsTyped world env)
    (ext : Extends world next) : BindingsTyped next env := by
  intro scope hs binding hb
  obtain ⟨sort, hl⟩ := h scope hs binding hb
  exact ⟨sort, hl.mono ext⟩

theorem BindingsTyped.push {world env} (h : BindingsTyped world env) :
    BindingsTyped world env.pushScope := by
  intro scope hs binding hb
  simp only [LocalEnv.pushScope, List.mem_cons] at hs
  rcases hs with rfl | hs
  · simp at hb
  · exact h scope hs binding hb

theorem BindingsTyped.declare {world env loc sort} (h : BindingsTyped world env)
    (hl : AddressTyped world sort loc) (name : String) :
    BindingsTyped world (env.declare name loc) := by
  cases env with
  | nil =>
    intro scope hs binding hb
    simp only [LocalEnv.declare, List.mem_singleton] at hs
    subst scope
    simp only [List.mem_singleton] at hb
    subst binding
    exact ⟨sort, hl⟩
  | cons scope rest =>
    intro sc hsc binding hb
    simp only [LocalEnv.declare, List.mem_cons] at hsc
    rcases hsc with rfl | hsc
    · simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨sort, hl⟩
      · exact h scope (by simp) binding hb
    · exact h sc (by simp [hsc]) binding hb

theorem EnvTyped.mono {world next Γ env} (h : EnvTyped world Γ env)
    (ext : Extends world next) : EnvTyped next Γ env := by
  refine ⟨h.bindings.mono ext, ?_⟩
  intro name ty ht
  obtain ⟨loc, hl, ha⟩ := h.lookup name ty ht
  exact ⟨loc, hl, ha.mono ext⟩

theorem EnvTyped.empty (world : World) : EnvTyped world [] [] := by
  constructor
  · intro scope hs
    simp at hs
  · intro name ty ht
    simp [RecoveryTyping.lookup] at ht

theorem EnvTyped.push {world Γ env} (h : EnvTyped world Γ env) :
    EnvTyped world (RecoveryTyping.push Γ #[]) env.pushScope := by
  refine ⟨h.bindings.push, ?_⟩
  intro name ty ht
  have old : RecoveryTyping.lookup Γ name = some ty := by
    simpa [RecoveryTyping.push, RecoveryTyping.lookup, scopeLookup] using ht
  obtain ⟨loc, hl, ha⟩ := h.lookup name ty old
  exact ⟨loc, by simpa [LocalEnv.pushScope, LocalEnv.lookup, GoLean.GoCore.Scope.lookup]
    using hl, ha⟩

theorem EnvTyped.declare {world Γ env loc} (h : EnvTyped world Γ env)
    (p : Param) (hl : AddressAt world p.typ loc) :
    EnvTyped world (RecoveryTyping.declare Γ p) (env.declare p.id loc) := by
  obtain ⟨sort, hty, ha⟩ := hl
  refine ⟨h.bindings.declare ha p.id, ?_⟩
  intro name ty ht
  rw [RecoveryTyping.lookup_declare] at ht
  rw [BooleanRuntime.lookup_declare]
  by_cases hn : p.id = name
  · simp only [hn, ↓reduceIte, Option.some.injEq] at ht ⊢
    subst ty
    exact ⟨loc, rfl, sort, hty, ha⟩
  · simp only [hn, ↓reduceIte] at ht ⊢
    exact h.lookup name ty ht

theorem EnvTyped.has {world Γ env name sort} (h : EnvTyped world Γ env)
    (hn : Has Γ name sort) :
    ∃ loc, env.lookup name = some loc ∧ AddressTyped world sort loc := by
  obtain ⟨ty, ht, hs⟩ := hn
  obtain ⟨loc, hl, ha⟩ := h.lookup name ty ht
  exact ⟨loc, hl, ha.sorted hs⟩

theorem EnvTyped.load {world Γ env s name sort} (h : EnvTyped world Γ env)
    (heap : HeapTyped world s) (hn : Has Γ name sort) :
    ∃ loc v, env.lookup name = some loc ∧ loadLoc s loc = .ok v ∧
      ValueTyped world sort v := by
  obtain ⟨loc, hl, ha⟩ := h.has hn
  obtain ⟨v, hv, ht⟩ := heap.load ha
  exact ⟨loc, v, hl, hv, ht⟩

end GoLean.GoCore.RecoveryRuntime
