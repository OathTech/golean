import GoLean.GoCore.BooleanStore
import GoLean.GoCore.RecoveryExpressions
import GoLean.GoCore.RecoveryStatements
import GoLean.GoCore.RecoveryTypingCore
import Lean

/-! Structural mixed storage for the recovery profile. The explicit schema
types addresses independently of cell contents; the heap invariant then
connects every schema entry to an actual cell. A root-reference value must
name a Boolean schema entry, so pointer-slot typing alone is insufficient.
These definitions contain no evaluator success or future-safety premise. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

abbrev World := Array ValueSort

def AddressTyped (world : World) (sort : ValueSort) (loc : Loc) : Prop :=
  ∃ a : Nat, loc = .base ⟨a⟩ ∧ world[a]? = some sort

inductive ValueTyped (world : World) : ValueSort → GoValue → Prop
  | boolean (b : Bool) : ValueTyped world .boolean (.bool b)
  | root {a : Nat} : world[a]? = some .boolean →
      ValueTyped world .root (.addr (.base ⟨a⟩))
  | nil : ValueTyped world .payload .nil
  | boxed (bytes : GoString) :
      ValueTyped world .payload (.interface .string (.string bytes))
  | string (bytes : GoString) : ValueTyped world .string (.string bytes)

structure HeapTyped (world : World) (s : ExecState) : Prop where
  size : world.size = s.heap.size
  cells : ∀ (a : Nat) (sort : ValueSort), world[a]? = some sort →
    ∃ ty v, s.heap[a]? = some (.value ty v) ∧ TypeClass ty sort ∧ ValueTyped world sort v

/-- A world extension preserves the type of every existing address. It says
nothing about the value currently stored at that address. -/
def Extends (world next : World) : Prop :=
  ∀ (a : Nat) (sort : ValueSort), world[a]? = some sort → next[a]? = some sort

theorem Extends.refl (world : World) : Extends world world := fun _ _ h => h
theorem Extends.trans {w₀ w₁ w₂} (h₁ : Extends w₀ w₁) (h₂ : Extends w₁ w₂) :
    Extends w₀ w₂ := fun a sort h => h₂ a sort (h₁ a sort h)

theorem Extends.push (world : World) (sort : ValueSort) : Extends world (world.push sort) := by
  intro a old h
  have ha := (Array.getElem?_eq_some_iff.mp h).1
  simpa [Array.getElem?_push, Nat.ne_of_lt ha] using h

theorem AddressTyped.mono {world next sort loc} (h : AddressTyped world sort loc)
    (ext : Extends world next) : AddressTyped next sort loc := by
  obtain ⟨a, hl, ha⟩ := h
  exact ⟨a, hl, ext a sort ha⟩

theorem ValueTyped.mono {world next sort v} (h : ValueTyped world sort v)
    (ext : Extends world next) : ValueTyped next sort v := by
  cases h with
  | boolean b => exact .boolean b
  | root ha => exact .root (ext _ _ ha)
  | nil => exact .nil
  | boxed bytes => exact .boxed bytes
  | string bytes => exact .string bytes

theorem HeapTyped.empty {s : ExecState} (h : s.heap = #[]) : HeapTyped #[] s := by
  refine ⟨by simp [h], ?_⟩
  intro a sort ha
  simp at ha

theorem HeapTyped.address_bound {world s sort loc} (h : HeapTyped world s)
    (hl : AddressTyped world sort loc) :
    ∃ a : Nat, loc = .base ⟨a⟩ ∧ a < s.heap.size := by
  obtain ⟨a, he, ha⟩ := hl
  exact ⟨a, he, h.size ▸ (Array.getElem?_eq_some_iff.mp ha).1⟩

theorem HeapTyped.load {world s sort loc} (h : HeapTyped world s)
    (hl : AddressTyped world sort loc) :
    ∃ v, loadLoc s loc = .ok v ∧ ValueTyped world sort v := by
  obtain ⟨a, rfl, ha⟩ := hl
  obtain ⟨ty, v, hc, _, hv⟩ := h.cells a sort ha
  exact ⟨v, by simp [loadLoc, Heap.lookup, hc]; rfl, hv⟩

theorem HeapTyped.boolean_root {world s loc} (h : HeapTyped world s)
    (hl : AddressTyped world .boolean loc) : BooleanRuntime.BoolRoot s loc := by
  obtain ⟨a, rfl, ha⟩ := hl
  obtain ⟨ty, v, hc, ht, hv⟩ := h.cells a .boolean ha
  cases ht
  cases hv with
  | boolean b => exact ⟨a, b, rfl, hc⟩

theorem HeapTyped.live_reference {world s v} (h : HeapTyped world s)
    (hv : ValueTyped world .root v) :
    ∃ loc, v = .addr loc ∧ BooleanRuntime.BoolRoot s loc := by
  cases hv with
  | @root a ha => exact ⟨.base ⟨a⟩, rfl, h.boolean_root ⟨a, rfl, ha⟩⟩

theorem HeapTyped.alloc {world s sort ty v} (h : HeapTyped world s)
    (ht : TypeClass ty sort) (hv : ValueTyped world sort v) :
    HeapTyped (world.push sort) (s.alloc v ty).2 := by
  refine ⟨by simpa [ExecState.alloc, ExecState.allocCell] using h.size, ?_⟩
  intro a kind ha
  by_cases he : a = world.size
  · subst a
    have hk : kind = sort := by simpa using ha.symm
    subst kind
    exact ⟨ty, v, by simp [ExecState.alloc, ExecState.allocCell, h.size],
      ht, hv.mono (Extends.push world sort)⟩
  · have hold : world[a]? = some kind := by
      simpa [Array.getElem?_push, he] using ha
    obtain ⟨oldTy, oldV, hc, hty, hv⟩ := h.cells a kind hold
    exact ⟨oldTy, oldV, by
      simpa [ExecState.alloc, ExecState.allocCell, Array.getElem?_push, ← h.size, he] using hc,
      hty, hv.mono (Extends.push world sort)⟩

theorem HeapTyped.allocated_address {world s sort ty v} (h : HeapTyped world s) :
    AddressTyped (world.push sort) sort (s.alloc v ty).1 := by
  exact ⟨world.size, by simp [ExecState.alloc, ExecState.allocCell, h.size], by simp⟩

/-- Normalization is the actual store path. Its identity behavior alone is
not a typing theorem; typed writes separately require `ValueTyped`. -/
theorem normalize_typed {ty sort} (ht : TypeClass ty sort) (s : ExecState) (v : GoValue) :
    normalizeValueForTy s ty v = .ok v := by
  cases ht <;> rfl

theorem typeClass_unique {ty left right} (hl : TypeClass ty left)
    (hr : TypeClass ty right) : left = right := by
  cases hl <;> cases hr <;> rfl

theorem HeapTyped.set {world s sort ty v a} (h : HeapTyped world s)
    (ha : world[a]? = some sort) (ht : TypeClass ty sort)
    (hv : ValueTyped world sort v) (bound : a < s.heap.size) :
    HeapTyped world {s with heap := s.heap.set a (.value ty v) bound} := by
  refine ⟨by simpa using h.size, ?_⟩
  intro i kind hi
  by_cases he : a = i
  · subst i
    have hk : kind = sort := Option.some.inj (hi.symm.trans ha)
    subst kind
    exact ⟨ty, v, by simp, ht, hv⟩
  · obtain ⟨oldTy, oldV, hc, hty, hval⟩ := h.cells i kind hi
    exact ⟨oldTy, oldV, by simpa [Array.getElem?_set, he] using hc, hty, hval⟩

/-- Every correctly sorted write succeeds on the real typed-cell path and
preserves the address schema, including all existing captured aliases. -/
theorem HeapTyped.store {world s sort loc v} (h : HeapTyped world s)
    (hl : AddressTyped world sort loc) (hv : ValueTyped world sort v) :
    ∃ s', storeLoc s loc v = .ok s' ∧ HeapTyped world s' ∧
      BooleanRuntime.SameContext s s' ∧ s'.heap.size = s.heap.size := by
  obtain ⟨a, rfl, ha⟩ := hl
  obtain ⟨ty, old, hc, ht, _⟩ := h.cells a sort ha
  have bound := (Array.getElem?_eq_some_iff.mp hc).1
  have cell := (Array.getElem?_eq_some_iff.mp hc).2
  refine ⟨{s with heap := s.heap.set a (.value ty v) bound}, ?_,
    h.set ha ht hv bound, ?_, by simp⟩
  · simp [storeLoc, ExecState.updateCell, bound, cell, normalize_typed ht]
    rfl
  · rfl

def AddressAt (world : World) (ty : Ty) (loc : Loc) : Prop :=
  ∃ sort, TypeClass ty sort ∧ AddressTyped world sort loc

def ValueAt (world : World) (ty : Ty) (v : GoValue) : Prop :=
  ∃ sort, TypeClass ty sort ∧ ValueTyped world sort v

theorem AddressAt.mono {world next ty loc} (h : AddressAt world ty loc)
    (ext : Extends world next) : AddressAt next ty loc := by
  obtain ⟨sort, ht, hl⟩ := h
  exact ⟨sort, ht, hl.mono ext⟩

theorem AddressAt.sorted {world ty sort loc} (h : AddressAt world ty loc)
    (ht : TypeClass ty sort) : AddressTyped world sort loc := by
  obtain ⟨kind, hk, hl⟩ := h
  cases typeClass_unique hk ht
  exact hl

theorem ValueAt.mono {world next ty v} (h : ValueAt world ty v)
    (ext : Extends world next) : ValueAt next ty v := by
  obtain ⟨sort, ht, hv⟩ := h
  exact ⟨sort, ht, hv.mono ext⟩

theorem ValueAt.sorted {world ty sort v} (h : ValueAt world ty v)
    (ht : TypeClass ty sort) : ValueTyped world sort v := by
  obtain ⟨kind, hk, hv⟩ := h
  cases typeClass_unique hk ht
  exact hv

end GoLean.GoCore.RecoveryRuntime

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

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

inductive ValuesTyped (world : World) : List ValueSort → List GoValue → Prop
  | nil : ValuesTyped world [] []
  | cons {sort sorts v vs} : ValueTyped world sort v → ValuesTyped world sorts vs →
      ValuesTyped world (sort :: sorts) (v :: vs)

theorem ValuesTyped.mono {world next sorts vs} (h : ValuesTyped world sorts vs)
    (ext : Extends world next) : ValuesTyped next sorts vs := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih => exact .cons (hv.mono ext) ih

theorem ValuesTyped.length {world sorts vs} (h : ValuesTyped world sorts vs) :
    sorts.length = vs.length := by induction h <;> simp_all

inductive StrictTyped : StrictOp → List ValueSort → ValueSort → Prop
  | not : StrictTyped .not [.boolean] .boolean
  | eqBoolean : StrictTyped (.eqCmp .bool) [.boolean, .boolean] .boolean
  | neqBoolean : StrictTyped (.neqCmp .bool) [.boolean, .boolean] .boolean
  | eqPayload {ty} : TypeClass ty .payload →
      StrictTyped (.eqCmp ty) [.payload, .payload] .boolean
  | neqPayload {ty} : TypeClass ty .payload →
      StrictTyped (.neqCmp ty) [.payload, .payload] .boolean
  | deref : StrictTyped (.deref .bool) [.root] .boolean
  | box {ty} : TypeClass ty .payload →
      StrictTyped (.toInterface ty .string) [.string] .payload
  | nil {ty} : NilType ty → StrictTyped (.nilLit ty) [] .payload

theorem eq_boolean (s : ExecState) (l r : Bool) :
    valueEq s .bool (.bool l) (.bool r) = .ok (l == r) := by
  unfold valueEq
  simp [TypeEnv.resolve, pure, Except.pure]

/-- The storage invariant allows only nil or a boxed string. Both dynamic
cases are comparable; admission separately restricts source comparison to nil. -/
theorem eq_payload {world ty l r} (s : ExecState) (ht : TypeClass ty .payload)
    (hl : ValueTyped world .payload l) (hr : ValueTyped world .payload r) :
    ∃ b, valueEq s ty l r = .ok b := by
  cases ht with
  | payload hi =>
    cases hl <;> cases hr
    · exact ⟨true, by unfold valueEq; simp [TypeEnv.resolve]; rfl⟩
    · exact ⟨false, by unfold valueEq; simp [TypeEnv.resolve]; rfl⟩
    · exact ⟨false, by unfold valueEq; simp [TypeEnv.resolve]; rfl⟩
    · rename_i left right
      refine ⟨left == right, ?_⟩
      have hd : (Ty.string != Ty.string) = false := rfl
      simp [valueEq, TypeEnv.resolve, tyUncomparable, tyUncomparableTy, pure, Except.pure, hd]

theorem apply_nil {ty} (ht : NilType ty) (s : ExecState) :
    applyStrictOp s (.nilLit ty) [] = .ok (.nil, s) := by
  cases ht with
  | untyped => rfl
  | typed hp => cases hp; rfl

/-- Actual strict-operator application for the whole runtime type surface.
It neither writes the state nor consults a choice stream. -/
theorem StrictTyped.apply {op sorts sort world s vs} (ht : StrictTyped op sorts sort)
    (heap : HeapTyped world s) (hv : ValuesTyped world sorts vs) :
    ∃ v, applyStrictOp s op vs = .ok (v, s) ∧ ValueTyped world sort v := by
  cases ht with
  | not =>
    cases hv with
    | cons h rest =>
      cases rest
      cases h with
      | boolean b => exact ⟨.bool (!b), rfl, .boolean (!b)⟩
  | eqBoolean =>
    cases hv with
    | cons h rest =>
      cases rest with
      | cons h' rest =>
        cases rest
        cases h with
        | boolean l =>
          cases h' with
          | boolean r => exact ⟨.bool (l == r), by simp [applyStrictOp, eq_boolean]; rfl,
              .boolean (l == r)⟩
  | neqBoolean =>
    cases hv with
    | cons h rest =>
      cases rest with
      | cons h' rest =>
        cases rest
        cases h with
        | boolean l =>
          cases h' with
          | boolean r => exact ⟨.bool (!(l == r)), by simp [applyStrictOp, eq_boolean]; rfl,
              .boolean (!(l == r))⟩
  | eqPayload ht =>
    cases hv with
    | cons h rest =>
      cases rest with
      | cons h' rest =>
        cases rest
        obtain ⟨b, hb⟩ := eq_payload s ht h h'
        exact ⟨.bool b, by simp [applyStrictOp, hb]; rfl, .boolean b⟩
  | neqPayload ht =>
    cases hv with
    | cons h rest =>
      cases rest with
      | cons h' rest =>
        cases rest
        obtain ⟨b, hb⟩ := eq_payload s ht h h'
        exact ⟨.bool (!b), by simp [applyStrictOp, hb]; rfl, .boolean (!b)⟩
  | deref =>
    cases hv with
    | cons h rest =>
      cases rest
      cases h with
      | @root a ha =>
        obtain ⟨v, hl, hv⟩ := heap.load ⟨a, rfl, ha⟩
        exact ⟨v, by simp [applyStrictOp, valueAsLoc, hl]; rfl, hv⟩
  | box ht =>
    cases hv with
    | cons h rest =>
      cases rest
      cases h with
      | string bytes => exact ⟨.interface .string (.string bytes), rfl, .boxed bytes⟩
  | nil ht =>
    cases hv
    exact ⟨.nil, apply_nil ht s, .nil⟩

end GoLean.GoCore.RecoveryRuntime

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

/-- Sort-preserving first-match inclusion, unlike Boolean name membership. -/
def Included (Γ Δ : Context) : Prop := ∀ name sort, Has Γ name sort → Has Δ name sort

theorem Included.refl (Γ : Context) : Included Γ Γ := fun _ _ h => h
theorem Included.trans {Γ Δ Ξ} (h : Included Γ Δ) (h' : Included Δ Ξ) :
    Included Γ Ξ := fun name sort hn => h' name sort (h name sort hn)

theorem lookup_append (Γ Δ : Context) (name : String) :
    RecoveryTyping.lookup (Γ ++ Δ) name =
      (RecoveryTyping.lookup Γ name).orElse (fun _ => RecoveryTyping.lookup Δ name) := by
  induction Γ with
  | nil => rfl
  | cons scope rest ih =>
    simp only [List.cons_append, RecoveryTyping.lookup]
    cases scopeLookup scope name <;> simp [ih]

theorem Included.declare {Γ Δ} (h : Included Γ Δ) (p : Param) :
    Included (RecoveryTyping.declare Γ p) (RecoveryTyping.declare Δ p) := by
  rintro name sort ⟨ty, hl, ht⟩
  rw [RecoveryTyping.lookup_declare] at hl
  by_cases hn : p.id = name
  · exact ⟨ty, by simpa [RecoveryTyping.lookup_declare, hn] using hl, ht⟩
  · have old : Has Γ name sort := ⟨ty, by simpa [hn] using hl, ht⟩
    obtain ⟨ty', hl', ht'⟩ := h name sort old
    exact ⟨ty', by simpa [RecoveryTyping.lookup_declare, hn] using hl', ht'⟩

theorem Included.push {Γ Δ} (h : Included Γ Δ) (ps : Array Param) :
    Included (RecoveryTyping.push Γ ps) (RecoveryTyping.push Δ ps) := by
  rintro name sort ⟨ty, hl, ht⟩
  simp only [RecoveryTyping.push, RecoveryTyping.lookup] at hl ⊢
  cases hs : scopeLookup (ps.toList.map (fun p => (p.id, p.typ))) name with
  | some ty' => exact ⟨ty, by simpa [RecoveryTyping.lookup, hs] using hl, ht⟩
  | none =>
    obtain ⟨ty', hl', ht'⟩ := h name sort ⟨ty, by simpa [hs] using hl, ht⟩
    exact ⟨ty', by simpa [RecoveryTyping.lookup, hs] using hl', ht'⟩

theorem Included.append_left (Γ Δ : Context) : Included Γ (Γ ++ Δ) := by
  rintro name sort ⟨ty, hl, ht⟩
  exact ⟨ty, by simp [lookup_append, hl], ht⟩

theorem AddressTyped.unique {world left right loc}
    (hl : AddressTyped world left loc) (hr : AddressTyped world right loc) : left = right := by
  obtain ⟨a, rfl, ha⟩ := hl
  obtain ⟨b, hb, hbr⟩ := hr
  cases hb
  exact Option.some.inj (ha.symm.trans hbr)

theorem EnvTyped.compatible {world Γ Δ env} (h : EnvTyped world Γ env)
    (h' : EnvTyped world Δ env) {name left right}
    (hl : Has Γ name left) (hr : Has Δ name right) : left = right := by
  obtain ⟨loc, he, ha⟩ := h.has hl
  obtain ⟨loc', he', ha'⟩ := h'.has hr
  have hloc : loc = loc' := Option.some.inj (he.symm.trans he')
  subst loc'
  exact ha.unique ha'

theorem EnvTyped.append {world Γ Δ env} (h : EnvTyped world Γ env)
    (h' : EnvTyped world Δ env) : EnvTyped world (Γ ++ Δ) env := by
  refine ⟨h.bindings, ?_⟩
  intro name ty ht
  rw [lookup_append] at ht
  cases hh : RecoveryTyping.lookup Γ name with
  | none => exact h'.lookup name ty (by simpa [hh] using ht)
  | some ty' =>
    have he : ty' = ty := by simpa [hh] using ht
    subst ty'
    exact h.lookup name ty hh

/-- Shared actual lookup makes the two static contexts compatible. This
lemma is used only when combining neutral statement lists: a declaration
can overwrite a name's sort and does not preserve arbitrary right contexts. -/
theorem EnvTyped.included_append_right {world Γ Δ env} (h : EnvTyped world Γ env)
    (h' : EnvTyped world Δ env) : Included Δ (Γ ++ Δ) := by
  rintro name sort ⟨ty, hl, ht⟩
  cases hh : RecoveryTyping.lookup Γ name with
  | none => exact ⟨ty, by simp [lookup_append, hh, hl], ht⟩
  | some ty' =>
    obtain ⟨loc, _, kind, hk, _⟩ := h.lookup name ty' hh
    have he : kind = sort := h.compatible h' ⟨ty', hh, hk⟩ ⟨ty, hl, ht⟩
    subst kind
    exact ⟨ty', by simp [lookup_append, hh], hk⟩

theorem expr_weaken {Γ Δ e sort} (h : ExprTyped Γ e sort) (inc : Included Γ Δ) :
    ExprTyped Δ e sort := by
  induction h with
  | var hn => exact .var (inc _ _ hn)
  | boolean b => exact .boolean b
  | string s => exact .string s
  | nil hn => exact .nil hn
  | not _ ih => exact .not ih
  | and _ _ ih ih' => exact .and ih ih'
  | or _ _ ih ih' => exact .or ih ih'
  | ref hn => exact .ref (inc _ _ hn)
  | deref _ ih => exact .deref ih
  | box ht _ ih => exact .box ht ih
  | recover => exact .recover
  | eqBool ht _ _ ih ih' => exact .eqBool ht ih ih'
  | neqBool ht _ _ ih ih' => exact .neqBool ht ih ih'
  | eqNil ht _ _ hn ih ih' => exact .eqNil ht ih ih' hn
  | neqNil ht _ _ hn ih ih' => exact .neqNil ht ih ih' hn

theorem exprAt_weaken {Γ Δ e ty} (h : ExprAt Γ e ty) (inc : Included Γ Δ) :
    ExprAt Δ e ty := by
  cases h with
  | typed ht he => exact .typed ht (expr_weaken he inc)

theorem target_weaken {Γ Δ target sort} (h : TargetTyped Γ target sort)
    (inc : Included Γ Δ) : TargetTyped Δ target sort := by
  cases h with
  | var hn => exact .var (inc _ _ hn)
  | addr he => exact .addr (expr_weaken he inc)

theorem targetAt_weaken {Γ Δ target ty} (h : TargetAt Γ target ty)
    (inc : Included Γ Δ) : TargetAt Δ target ty := by
  cases h with
  | typed ht ha => exact .typed ht (target_weaken ha inc)

theorem arguments_weaken {Γ Δ es ps} (h : Arguments Γ es ps) (inc : Included Γ Δ) :
    Arguments Δ es ps := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (exprAt_weaken he inc) ih

theorem targets_weaken {Γ Δ targets ps} (h : Targets Γ targets ps) (inc : Included Γ Δ) :
    Targets Δ targets ps := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (targetAt_weaken he inc) ih

theorem captures_weaken {Γ Δ es} (h : Captures Γ es) (inc : Included Γ Δ) :
    Captures Δ es := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (expr_weaken he inc) ih

end GoLean.GoCore.RecoveryRuntime

/-! Runtime source typing erases duplicate-key rejection, retaining actual
first-match types and declaration effects. General weakening preserves sorts;
it does not assert that old sorts survive new declarations. -/
namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping

mutual
inductive ControlStmt (fs : Array Func) : Bool → Context → Stmt → Prop
  | seqn {inSequence Γ ss} : ControlStmts fs Γ ss.toList →
      ControlStmt fs inSequence Γ (.seqn ss)
  | block {inSequence Γ ps ss} : StorageParams ps → DistinctParams ps →
      ControlStmts fs (push Γ ps) ss.toList → ControlStmt fs inSequence Γ (.block ps ss)
  | initialization {Γ p} : StorageType p.typ → ControlStmt fs true Γ (.initialization p)
  | assign {inSequence Γ a e} : Assignment Γ a e → ControlStmt fs inSequence Γ (.assign a e)
  | branch {inSequence Γ e t f} : ExprTyped Γ e .boolean →
      ControlStmt fs false Γ t → ControlStmt fs false Γ f →
      declarationCount t = 0 → declarationCount f = 0 →
      ControlStmt fs inSequence Γ (.ifThenElse e t f)
  | call {inSequence Γ targets fid args} : DirectCall fs Γ targets fid args →
      ControlStmt fs inSequence Γ (.call targets fid args)
  | closureCall {inSequence Γ targets callee args} : ClosureCall fs Γ targets args callee →
      ControlStmt fs inSequence Γ (.callValue targets callee args)
  | deferCall {inSequence Γ callee args} : DeferredCall fs Γ args callee →
      ControlStmt fs inSequence Γ (.deferCall callee args)
  | panic {inSequence Γ e} : PanicArgument Γ e → ControlStmt fs inSequence Γ (.panicStmt e)
  | ret {inSequence Γ} : ControlStmt fs inSequence Γ .returnStmt
inductive ControlStmts (fs : Array Func) : Context → List Stmt → Prop
  | nil {Γ} : ControlStmts fs Γ []
  | cons {Γ s ss} : ControlStmt fs true Γ s → ControlStmts fs (afterStmt Γ s) ss →
      ControlStmts fs Γ (s :: ss)
end

theorem ControlStmt.of_static {fs inSequence Γ s} (h : Statement fs inSequence Γ s) :
    ControlStmt fs inSequence Γ s := by
  induction h using Statement.rec (motive_2 := fun Γ ss _ => ControlStmts fs Γ ss) with
  | seqn _ ih => exact .seqn ih
  | block ht hd _ ih => exact .block ht hd ih
  | initialization ht _ => exact .initialization ht
  | assign ht => exact .assign ht
  | branch he _ _ nt nf ih ih' => exact .branch he ih ih' nt nf
  | call ht => exact .call ht
  | closureCall ht => exact .closureCall ht
  | deferCall ht => exact .deferCall ht
  | panic ht => exact .panic ht
  | ret => exact .ret
  | nil => exact .nil
  | cons _ _ ih ih' => exact .cons ih ih'

theorem ControlStmts.of_static {fs Γ ss} (h : Statements fs Γ ss) :
    ControlStmts fs Γ ss := by
  induction h using Statements.rec
    (motive_1 := fun inSequence Γ s _ => ControlStmt fs inSequence Γ s) with
  | seqn _ ih => exact .seqn ih
  | block ht hd _ ih => exact .block ht hd ih
  | initialization ht _ => exact .initialization ht
  | assign ht => exact .assign ht
  | branch he _ _ nt nf ih ih' => exact .branch he ih ih' nt nf
  | call ht => exact .call ht
  | closureCall ht => exact .closureCall ht
  | deferCall ht => exact .deferCall ht
  | panic ht => exact .panic ht
  | ret => exact .ret
  | nil => exact .nil
  | cons _ _ ih ih' => exact .cons ih ih'

mutual
theorem afterStmt_included (Γ Δ : Context) (s : Stmt) (h : Included Γ Δ) :
    Included (afterStmt Γ s) (afterStmt Δ s) := by
  cases s <;> try exact h
  case seqn ss => exact afterStmts_included Γ Δ ss.toList h
  case initialization p => exact h.declare p
termination_by structural s
theorem afterStmts_included (Γ Δ : Context) (ss : List Stmt) (h : Included Γ Δ) :
    Included (afterStmts Γ ss) (afterStmts Δ ss) := by
  cases ss with
  | nil => exact h
  | cons s ss => exact afterStmts_included _ _ ss (afterStmt_included Γ Δ s h)
termination_by structural ss
end

theorem assignment_weaken {Γ Δ a e} (h : Assignment Γ a e) (inc : Included Γ Δ) :
    Assignment Δ a e := by
  cases h with
  | typed ha he => exact .typed (target_weaken ha inc) (expr_weaken he inc)

theorem directCall_weaken {fs Γ Δ targets fid args} (h : DirectCall fs Γ targets fid args)
    (inc : Included Γ Δ) : DirectCall fs Δ targets fid args := by
  obtain ⟨f, hf, ha, ht⟩ := h
  exact ⟨f, hf, arguments_weaken ha inc, targets_weaken ht inc⟩

theorem closureCall_weaken {fs Γ Δ targets args callee}
    (h : ClosureCall fs Γ targets args callee) (inc : Included Γ Δ) :
    ClosureCall fs Δ targets args callee := by
  cases h with
  | known hf hc ha ht =>
    exact .known hf (captures_weaken hc inc) (arguments_weaken ha inc) (targets_weaken ht inc)

theorem deferredCall_weaken {fs Γ Δ args callee}
    (h : DeferredCall fs Γ args callee) (inc : Included Γ Δ) :
    DeferredCall fs Δ args callee := by
  cases h with
  | known hf hc ha => exact .known hf (captures_weaken hc inc) (arguments_weaken ha inc)

theorem panicArgument_weaken {Γ Δ e} (h : PanicArgument Γ e) (inc : Included Γ Δ) :
    PanicArgument Δ e := by
  cases h with
  | stringBox ht he => exact .stringBox ht (expr_weaken he inc)

theorem ControlStmt.weaken {fs inSequence Γ s} (h : ControlStmt fs inSequence Γ s)
    (Δ : Context) (inc : Included Γ Δ) : ControlStmt fs inSequence Δ s := by
  revert Δ
  induction h using ControlStmt.rec
    (motive_2 := fun Γ ss _ => ∀ Δ, Included Γ Δ → ControlStmts fs Δ ss) with
  | seqn _ ih => intro Δ inc; exact .seqn (ih Δ inc)
  | block ht hd _ ih => intro Δ inc; exact .block ht hd (ih (push Δ _) (inc.push _))
  | initialization ht => intro Δ _; exact .initialization ht
  | assign ht => intro Δ inc; exact .assign (assignment_weaken ht inc)
  | branch he _ _ nt nf ih ih' =>
    intro Δ inc
    exact .branch (expr_weaken he inc) (ih Δ inc) (ih' Δ inc) nt nf
  | call ht => intro Δ inc; exact .call (directCall_weaken ht inc)
  | closureCall ht => intro Δ inc; exact .closureCall (closureCall_weaken ht inc)
  | deferCall ht => intro Δ inc; exact .deferCall (deferredCall_weaken ht inc)
  | panic ht => intro Δ inc; exact .panic (panicArgument_weaken ht inc)
  | ret => intro Δ _; exact .ret
  | nil => exact .nil
  | @cons Γ s ss _ _ ih ih' =>
    rename_i Δ inc
    exact .cons (ih Δ inc) (ih' (afterStmt Δ s) (afterStmt_included Γ Δ s inc))

theorem ControlStmts.weaken {fs Γ ss} (h : ControlStmts fs Γ ss)
    (Δ : Context) (inc : Included Γ Δ) : ControlStmts fs Δ ss := by
  induction ss generalizing Γ Δ with
  | nil => exact .nil
  | cons s ss ih =>
    cases h with
    | cons h h' => exact .cons (h.weaken Δ inc) (ih h' _ (afterStmt_included Γ Δ s inc))

theorem afterStmts_append (Γ : Context) (ss ts : List Stmt) :
    afterStmts Γ (ss ++ ts) = afterStmts (afterStmts Γ ss) ts := by
  induction ss generalizing Γ with
  | nil => rfl
  | cons s ss ih => exact ih (afterStmt Γ s)

theorem ControlStmts.append {fs Γ ss ts} (h : ControlStmts fs Γ ss)
    (h' : ControlStmts fs (afterStmts Γ ss) ts) : ControlStmts fs Γ (ss ++ ts) := by
  induction ss generalizing Γ with
  | nil => exact h'
  | cons s ss ih =>
    cases h with
    | cons hs hss => exact .cons hs (ih hss h')

end GoLean.GoCore.RecoveryRuntime
