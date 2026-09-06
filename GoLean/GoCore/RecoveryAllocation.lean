import GoLean.GoCore.RecoveryEnvironment
import GoLean.GoCore.RecoveryStatements

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

def declareMany (Γ : Context) : List Param → Context
  | [] => Γ
  | p :: ps => declareMany (RecoveryTyping.declare Γ p) ps

inductive ParamsValues (world : World) : List Param → List GoValue → Prop
  | nil : ParamsValues world [] []
  | cons {p ps v vs} : ValueAt world p.typ v → ParamsValues world ps vs →
      ParamsValues world (p :: ps) (v :: vs)

theorem ParamsValues.mono {world next ps vs} (h : ParamsValues world ps vs)
    (ext : Extends world next) : ParamsValues next ps vs := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih => exact .cons (hv.mono ext) ih

theorem ParamsValues.length {world ps vs} (h : ParamsValues world ps vs) :
    ps.length = vs.length := by
  induction h <;> simp_all

/-- Only Boolean and empty-interface storage is zero initialized; a live
root reference is never fabricated from a pointer's nil zero value. -/
theorem default_storage {ty} (h : StorageType ty) (world : World) (s : ExecState) :
    ∃ sort v, defaultValue s ty = .ok v ∧ TypeClass ty sort ∧ ValueTyped world sort v := by
  rcases h with hb | hp
  · cases hb
    exact ⟨.boolean, .bool false, rfl, .boolean, .boolean false⟩
  · cases hp with
    | payload hi => exact ⟨.payload, .nil, rfl, .payload hi, .nil⟩

theorem allocDecls_typed (ps : List Param) {world Γ env s}
    (heap : HeapTyped world s) (henv : EnvTyped world Γ env)
    (types : ∀ p ∈ ps, StorageType p.typ) :
    ∃ next env' s', allocDecls env s ps = .ok (env', s') ∧
      Extends world next ∧ HeapTyped next s' ∧ EnvTyped next (declareMany Γ ps) env' ∧
      BooleanRuntime.SameContext s s' ∧ s'.heap.size = s.heap.size + ps.length := by
  induction ps generalizing world Γ env s with
  | nil => exact ⟨world, env, s, rfl, .refl world, heap, henv, rfl, by simp⟩
  | cons p ps ih =>
    obtain ⟨sort, v, hd, ht, hv⟩ := default_storage (types p (by simp)) world s
    have ext := Extends.push world sort
    have nh := heap.alloc ht hv
    have ne := (henv.mono ext).declare p
      ⟨sort, ht, heap.allocated_address (ty := p.typ) (v := v)⟩
    obtain ⟨next, env', s', run, extension, heap', envtyped, ctx, size⟩ :=
      ih nh ne (fun q hq => types q (by simp [hq]))
    refine ⟨next, env', s', ?_, ext.trans extension, heap', envtyped, ?_, ?_⟩
    · simpa [allocDecls, hd, Bind.bind, Except.bind] using run
    · exact (show BooleanRuntime.SameContext s (s.alloc v p.typ).2 from rfl).trans ctx
    · simpa [ExecState.alloc, ExecState.allocCell, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using size

/-- Binding typed values allocates distinct parameter slots. Captured root
values remain aliases of their original Boolean cell, not copies of it. -/
theorem bindParams_typed {world Γ env s ps vs}
    (heap : HeapTyped world s) (henv : EnvTyped world Γ env)
    (values : ParamsValues world ps vs) :
    ∃ next env' s', bindParams env s ps vs = .ok (env', s') ∧
      Extends world next ∧ HeapTyped next s' ∧ EnvTyped next (declareMany Γ ps) env' ∧
      BooleanRuntime.SameContext s s' ∧ s'.heap.size = s.heap.size + ps.length := by
  induction ps generalizing world Γ env s vs with
  | nil =>
    cases values
    exact ⟨world, env, s, rfl, .refl world, heap, henv, rfl, by simp⟩
  | cons p ps ih =>
    cases values with
    | @cons _ _ v vs hv rest =>
      obtain ⟨sort, ht, hv⟩ := hv
      have ext := Extends.push world sort
      have nh := heap.alloc ht hv
      have ne := (henv.mono ext).declare p
        ⟨sort, ht, heap.allocated_address (ty := p.typ) (v := v)⟩
      obtain ⟨next, env', s', run, extension, heap', envtyped, ctx, size⟩ :=
        ih nh ne (ParamsValues.mono rest ext)
      refine ⟨next, env', s', ?_, ext.trans extension, heap', envtyped, ?_, ?_⟩
      · simpa [bindParams, normalize_typed ht, Bind.bind, Except.bind] using run
      · exact (show BooleanRuntime.SameContext s (s.alloc v p.typ).2 from rfl).trans ctx
      · simpa [ExecState.alloc, ExecState.allocCell, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using size

end GoLean.GoCore.RecoveryRuntime
