import GoLean.GoCore.BooleanControl
import GoLean.GoCore.BooleanStore
import GoLean.GoCore.MachineSound

/-! Boolean machine invariant and local memory preservation facts. The
control predicate is structural, with actual lookups and typed root cells.
`MachineWf` supplies address bounds and the existing vacuous iterator
normalization field; it is not an integer-normalization invariant. -/
namespace GoLean.GoCore.BooleanRuntime
open BooleanTyping Admission Machine

abbrev TypedControl (s : ExecState) (c : Config) := Control (BoolRoot s) (EnvRoots s) c

/-- Static admission supplies current computation typing at the actual
entry barrier; setup separately supplies these concrete environment facts. -/
theorem initial_control {f : Func} {s : ExecState} {env : LocalEnv}
    (hf : FunctionTyped f) (hc : Covers (initialContext f) env) (he : EnvRoots s env) :
    TypedControl s (.exec f.body env (.frame [] [] [] [] .stop)) :=
  .exec hc he (ControlStmt.of_static hf.2.2.2.1) .barrier

/-- All stores in this profile retain Boolean cells, and allocation retains
every old root address. This does not say that old Boolean values agree. -/
structure Extension (s t : ExecState) : Prop where
  heap : BoolHeap t
  context : SameContext s t
  size : s.heap.size ≤ t.heap.size

theorem Extension.refl {s} (h : BoolHeap s) : Extension s s := ⟨h, rfl, Nat.le_refl _⟩

theorem Extension.root {s t} (h : Extension s t) {loc} (hl : BoolRoot s loc) :
    BoolRoot t loc := by
  obtain ⟨a, rfl, ha⟩ := hl.bound
  exact h.heap.root (Nat.lt_of_lt_of_le ha h.size)

theorem Extension.env {s t} (h : Extension s t) {env} (he : EnvRoots s env) :
    EnvRoots t env := by
  intro scope hs binding hb
  exact h.root (he scope hs binding hb)

theorem Extension.control {s t c} (h : Extension s t) (hc : TypedControl s c) :
    TypedControl t c := hc.mono (fun _ => h.root) (fun _ => h.env)

theorem Extension.alloc {s} (h : BoolHeap s) (b : Bool) :
    Extension s (s.alloc (.bool b) .bool).2 := by
  refine ⟨h.alloc b, rfl, ?_⟩
  simp [ExecState.alloc, ExecState.allocCell]

theorem store_extension {s loc} (hs : BoolHeap s) (hl : BoolRoot s loc) (b : Bool) :
    ∃ t, storeLoc s loc (.bool b) = .ok t ∧ Extension s t := by
  obtain ⟨a, old, rfl, ha⟩ := hl
  let hbound := (Array.getElem?_eq_some_iff.mp ha).1
  refine ⟨{s with heap := s.heap.set a (.value .bool (.bool b)) hbound},
    store_bool ha b, hs.set a b hbound, rfl, ?_⟩
  simp

theorem bound_flatten (Γ : Context) (name : String) :
    Bound Γ name ↔ name ∈ Γ.flatten := by
  simp [Bound, List.mem_flatten]

theorem Covers.names {Γ env} (h : Covers Γ env) : NamesPresent Γ.flatten env := by
  intro name hn
  exact h name ((bound_flatten Γ name).mpr hn)

theorem Covers.of_names {Γ env} (h : NamesPresent Γ.flatten env) : Covers Γ env := by
  intro name hn
  exact h name ((bound_flatten Γ name).mp hn)

theorem Covers.push_scope {Γ env} (h : Covers Γ env) : Covers Γ env.pushScope := by
  intro name hn
  obtain ⟨loc, hl⟩ := h name hn
  exact ⟨loc, by simpa [LocalEnv.pushScope, LocalEnv.lookup, Scope.lookup] using hl⟩

theorem Covers.declare {Γ env} (h : Covers Γ env) (name : String) (loc : Loc) :
    Covers (declare Γ name) (env.declare name loc) := by
  intro needle hn
  rw [bound_declare] at hn
  by_cases heq : name = needle
  · exact ⟨loc, by simp [lookup_declare, heq]⟩
  · obtain ⟨old, hold⟩ := h needle (hn.resolve_left (Ne.symm heq))
    exact ⟨old, by simp [lookup_declare, heq, hold]⟩

theorem block_setup {Γ env s ps} (hc : Covers Γ env) (he : EnvRoots s env)
    (hs : BoolHeap s) (ht : BoolParams ps) :
    ∃ env' t, allocDecls env.pushScope s ps.toList = .ok (env', t) ∧
      Covers (push Γ ps) env' ∧ EnvRoots t env' ∧ Extension s t := by
  obtain ⟨env', t, ha, hh, he', hn⟩ :=
    allocDecls_bool ps.toList ht hs he.push hc.push_scope.names
  obtain ⟨hctx, hsize⟩ := allocDecls_shape ps.toList ha
  refine ⟨env', t, ha, ?_, he', hh, hctx, ?_⟩
  · intro name hname
    rw [bound_push] at hname
    exact hn name ((List.mem_append).mpr
      (hname.imp id ((bound_flatten Γ name).mp)))
  · omega

/-- The fixed context and externally pinned result locations come from the
real driver setup. Their preservation is separate from continuation typing. -/
structure Inv (context : ExecState) (results : List Loc) (s : ExecState) (c : Config) : Prop where
  sameContext : SameContext context s
  heap : BoolHeap s
  pinned : ∀ loc ∈ results, BoolRoot s loc
  control : TypedControl s c
  machineWf : MachineWf s c

theorem Inv.readout {context results s c} (h : Inv context results s c) :
    ∃ bs : List Bool, loadMany s results = .ok (bs.map GoValue.bool) ∧ bs.length = results.length :=
  loadMany_bool h.pinned

end GoLean.GoCore.BooleanRuntime
