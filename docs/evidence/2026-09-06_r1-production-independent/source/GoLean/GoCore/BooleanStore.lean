import GoLean.GoCore.Machine

/-! Runtime facts for the scoped Boolean profile. These predicates inspect
actual heap cells and environment lookup; none is defined by execution
success. They are separate from the syntax/admission judgment. -/
namespace GoLean.GoCore.BooleanRuntime
open Machine

/-- A root location containing a Boolean at declared Boolean type. -/
def BoolRoot (s : ExecState) (loc : Loc) : Prop :=
  ∃ (a : Nat) (b : Bool), loc = .base ⟨a⟩ ∧
    s.heap[a]? = some (.value .bool (.bool b))

/-- Every allocated cell in the Boolean-only profile has its actual type. -/
def BoolHeap (s : ExecState) : Prop :=
  ∀ a, a < s.heap.size → ∃ b : Bool,
    s.heap[a]? = some (.value .bool (.bool b))

/-- Every stored binding references a typed root, including hidden outer
bindings and shadowed bindings within one scope. Lookup coverage alone does
not imply this invariant: a hidden dangling location must also be excluded. -/
def EnvRoots (s : ExecState) (env : LocalEnv) : Prop :=
  ∀ scope ∈ env, ∀ binding ∈ scope, BoolRoot s binding.2

@[simp] theorem default_bool (s : ExecState) :
    defaultValue s .bool = .ok (.bool false) := rfl

@[simp] theorem normalize_bool (s : ExecState) (b : Bool) :
    normalizeValueForTy s .bool (.bool b) = .ok (.bool b) := rfl

theorem BoolRoot.load {s loc} (h : BoolRoot s loc) :
    ∃ b : Bool, loadLoc s loc = .ok (.bool b) := by
  obtain ⟨a, b, rfl, hb⟩ := h
  exact ⟨b, by simp [loadLoc, Heap.lookup, hb]; rfl⟩

theorem BoolRoot.bound {s loc} (h : BoolRoot s loc) :
    ∃ a : Nat, loc = .base ⟨a⟩ ∧ a < s.heap.size := by
  obtain ⟨a, b, hl, hb⟩ := h
  exact ⟨a, hl, (Array.getElem?_eq_some_iff.mp hb).1⟩

theorem BoolHeap.root {s : ExecState} (h : BoolHeap s) {a : Nat}
    (ha : a < s.heap.size) : BoolRoot s (.base ⟨a⟩) := by
  obtain ⟨b, hb⟩ := h a ha
  exact ⟨a, b, rfl, hb⟩

theorem BoolHeap.empty {s : ExecState} (h : s.heap = #[]) : BoolHeap s := by
  intro a ha
  simp [h] at ha

theorem BoolRoot.alloc_new (s : ExecState) (b : Bool) :
    BoolRoot (s.alloc (.bool b) .bool).2 (s.alloc (.bool b) .bool).1 := by
  exact ⟨s.heap.size, b, rfl, by simp [ExecState.alloc, ExecState.allocCell]⟩

theorem BoolRoot.alloc {s loc} (h : BoolRoot s loc) (b : Bool) :
    BoolRoot (s.alloc (.bool b) .bool).2 loc := by
  obtain ⟨a, old, hl, hb⟩ := h
  have ha := (Array.getElem?_eq_some_iff.mp hb).1
  exact ⟨a, old, hl, by simpa [ExecState.alloc, ExecState.allocCell,
    Array.getElem?_push, Nat.ne_of_lt ha] using hb⟩

theorem BoolHeap.alloc {s} (h : BoolHeap s) (b : Bool) :
    BoolHeap (s.alloc (.bool b) .bool).2 := by
  intro a ha
  change a < (s.heap.push (.value .bool (.bool b))).size at ha
  simp only [Array.size_push] at ha
  by_cases hlt : a < s.heap.size
  · obtain ⟨old, hb⟩ := h a hlt
    exact ⟨old, by simpa [ExecState.alloc, ExecState.allocCell,
      Array.getElem?_push, Nat.ne_of_lt hlt] using hb⟩
  · have heq : a = s.heap.size := by omega
    subst a
    exact ⟨b, by simp [ExecState.alloc, ExecState.allocCell]⟩

theorem EnvRoots.nil (s : ExecState) : EnvRoots s [] := by
  intro scope h
  simp at h

theorem scope_lookup_root {s : ExecState} {scope : Scope}
    (h : ∀ binding ∈ scope, BoolRoot s binding.2) {name : String} {loc : Loc}
    (hl : scope.lookup name = some loc) : BoolRoot s loc := by
  induction scope with
  | nil => simp [Scope.lookup] at hl
  | cons binding rest ih =>
    obtain ⟨key, root⟩ := binding
    simp only [Scope.lookup] at hl
    split at hl
    · cases hl
      exact h (key, loc) (by simp)
    · exact ih (fun binding hb => h binding (by simp [hb])) hl

theorem EnvRoots.lookup {s env} (h : EnvRoots s env) {name loc}
    (hl : env.lookup name = some loc) : BoolRoot s loc := by
  induction env with
  | nil => simp [LocalEnv.lookup] at hl
  | cons scope rest ih =>
    simp only [LocalEnv.lookup] at hl
    cases hs : scope.lookup name with
    | none =>
      rw [hs] at hl
      exact ih (fun sc hsc => h sc (by simp [hsc])) hl
    | some root =>
      rw [hs] at hl
      cases hl
      exact scope_lookup_root (h scope (by simp)) hs

theorem EnvRoots.push {s env} (h : EnvRoots s env) :
    EnvRoots s env.pushScope := by
  intro scope hs binding hb
  simp only [LocalEnv.pushScope, List.mem_cons] at hs
  rcases hs with rfl | hs
  · simp at hb
  · exact h scope hs binding hb

theorem lookup_declare (env : LocalEnv) (name : String) (loc : Loc)
    (needle : String) :
    (env.declare name loc).lookup needle =
      if name = needle then some loc else env.lookup needle := by
  by_cases hn : name = needle
  · cases env <;> simp [LocalEnv.declare, LocalEnv.lookup, Scope.lookup, hn]
  · cases env <;> simp [LocalEnv.declare, LocalEnv.lookup, Scope.lookup, hn]

theorem EnvRoots.declare {s env loc} (h : EnvRoots s env)
    (hl : BoolRoot s loc) (name : String) :
    EnvRoots s (env.declare name loc) := by
  cases env with
  | nil =>
    intro scope hs binding hb
    simp only [LocalEnv.declare, List.mem_singleton] at hs
    subst scope
    simp only [List.mem_singleton] at hb
    subst binding
    exact hl
  | cons scope rest =>
    intro sc hsc binding hb
    simp only [LocalEnv.declare, List.mem_cons] at hsc
    rcases hsc with rfl | hsc
    · simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hl
      · exact h scope (by simp) binding hb
    · exact h sc (by simp [hsc]) binding hb

theorem EnvRoots.alloc {s env} (h : EnvRoots s env) (b : Bool) :
    EnvRoots (s.alloc (.bool b) .bool).2 env := by
  intro scope hs binding hb
  exact (h scope hs binding hb).alloc b

/-- Exact result of a Boolean store, using the real typed-cell write path. -/
theorem store_bool {s : ExecState} {a : Nat} {old : Bool}
    (h : s.heap[a]? = some (.value .bool (.bool old))) (b : Bool) :
    storeLoc s (.base ⟨a⟩) (.bool b) =
      .ok { s with heap := (s.heap.set a (.value .bool (.bool b))
        (Array.getElem?_eq_some_iff.mp h).1) } := by
  have ha := (Array.getElem?_eq_some_iff.mp h).1
  have hc := (Array.getElem?_eq_some_iff.mp h).2
  simp [storeLoc, ExecState.updateCell, ha, hc, normalize_bool]
  rfl

theorem BoolRoot.set {s : ExecState} {loc : Loc} (h : BoolRoot s loc)
    (a : Nat) (b : Bool) (ha : a < s.heap.size) :
    BoolRoot {s with heap := s.heap.set a (.value .bool (.bool b)) ha} loc := by
  obtain ⟨i, old, hl, hi⟩ := h
  by_cases heq : a = i
  · subst i
    exact ⟨a, b, hl, by simp⟩
  · exact ⟨i, old, hl, by simpa [Array.getElem?_set, heq] using hi⟩

theorem BoolHeap.set {s : ExecState} (h : BoolHeap s)
    (a : Nat) (b : Bool) (ha : a < s.heap.size) :
    BoolHeap {s with heap := s.heap.set a (.value .bool (.bool b)) ha} := by
  intro i hi
  have hi' : i < s.heap.size := by simpa using hi
  obtain ⟨j, v, hj, hv⟩ := (h.root hi').set a b ha
  cases hj
  exact ⟨v, hv⟩

theorem EnvRoots.set {s env} (h : EnvRoots s env)
    (a : Nat) (b : Bool) (ha : a < s.heap.size) :
    EnvRoots {s with heap := s.heap.set a (.value .bool (.bool b)) ha} env := by
  intro scope hs binding hb
  exact (h scope hs binding hb).set a b ha

/-- Names whose storage has been installed, independent of its current value. -/
def NamesPresent (names : List String) (env : LocalEnv) : Prop :=
  ∀ name ∈ names, ∃ loc, env.lookup name = some loc

/-- All non-heap fields of the existing state agree. B7 will make this
an immutable context parameter rather than repeated state equalities. -/
def SameContext (s t : ExecState) : Prop :=
  {s with heap := #[]} = {t with heap := #[]}

theorem SameContext.refl (s : ExecState) : SameContext s s := rfl

theorem SameContext.trans {s t u} (h : SameContext s t) (h' : SameContext t u) :
    SameContext s u := Eq.trans h h'

theorem allocDecls_shape (ps : List Param) {s s' : ExecState} {env env' : LocalEnv}
    (h : allocDecls env s ps = .ok (env', s')) :
    SameContext s s' ∧ s'.heap.size = s.heap.size + ps.length := by
  induction ps generalizing s env with
  | nil =>
    change Except.ok (env, s) = .ok (env', s') at h
    cases Except.ok.inj h
    exact ⟨rfl, by simp⟩
  | cons p ps ih =>
    cases hv : defaultValue s p.typ with
    | error e => simp [allocDecls, hv, Bind.bind, Except.bind] at h
    | ok v =>
      simp only [allocDecls, hv, Bind.bind, Except.bind] at h
      obtain ⟨hc, hn⟩ := ih h
      refine ⟨(show SameContext s (s.alloc v p.typ).2 from rfl).trans hc, ?_⟩
      simpa [ExecState.alloc, ExecState.allocCell, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hn

theorem bindParams_shape (ps : List Param) (vs : List GoValue)
    {s s' : ExecState} {env env' : LocalEnv}
    (h : bindParams env s ps vs = .ok (env', s')) :
    SameContext s s' ∧ s'.heap.size = s.heap.size + ps.length := by
  induction ps generalizing s env vs with
  | nil =>
    cases vs with
    | nil =>
      change Except.ok (env, s) = .ok (env', s') at h
      cases Except.ok.inj h
      exact ⟨rfl, by simp⟩
    | cons v vs => simp [bindParams, stuck, throw, throwThe, MonadExceptOf.throw] at h
  | cons p ps ih =>
    cases vs with
    | nil => simp [bindParams, stuck, throw, throwThe, MonadExceptOf.throw] at h
    | cons v vs =>
      cases hv : normalizeValueForTy s p.typ v with
      | error e => simp [bindParams, hv, Bind.bind, Except.bind] at h
      | ok v' =>
        simp only [bindParams, hv, Bind.bind, Except.bind] at h
        obtain ⟨hc, hn⟩ := ih vs h
        refine ⟨(show SameContext s (s.alloc v' p.typ).2 from rfl).trans hc, ?_⟩
        simpa [ExecState.alloc, ExecState.allocCell, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hn

theorem NamesPresent.declare {names env} (h : NamesPresent names env)
    (name : String) (loc : Loc) : NamesPresent (name :: names) (env.declare name loc) := by
  intro needle hn
  rw [lookup_declare]
  by_cases heq : name = needle
  · exact ⟨loc, by simp [heq]⟩
  · have hn' : needle ∈ names := by simpa [eq_comm, heq] using hn
    obtain ⟨old, hold⟩ := h needle hn'
    exact ⟨old, by simp [heq, hold]⟩

theorem NamesPresent.mono {names names' env} (h : NamesPresent names env)
    (hsub : ∀ n ∈ names', n ∈ names) : NamesPresent names' env := by
  intro n hn
  exact h n (hsub n hn)

/-- Every declared Boolean local is initialized by the actual allocator.
Old and new names remain present even when a declaration shadows a name. -/
theorem allocDecls_bool (ps : List Param) {s : ExecState} {env : LocalEnv}
    {names : List String} (ht : ∀ p ∈ ps, p.typ = .bool)
    (hs : BoolHeap s) (he : EnvRoots s env) (hn : NamesPresent names env) :
    ∃ env' s', allocDecls env s ps = .ok (env', s') ∧ BoolHeap s' ∧
      EnvRoots s' env' ∧ NamesPresent (ps.map Param.id ++ names) env' := by
  induction ps generalizing s env names with
  | nil => exact ⟨env, s, rfl, hs, he, hn⟩
  | cons p ps ih =>
    have hp : p.typ = .bool := ht p (by simp)
    have hps : ∀ q ∈ ps, q.typ = .bool := fun q hq => ht q (by simp [hq])
    obtain ⟨env', s', hr, hs', he', hn'⟩ := ih hps (hs.alloc false)
      ((he.alloc false).declare (BoolRoot.alloc_new s false) p.id)
      (hn.declare p.id (s.alloc (.bool false) .bool).1)
    refine ⟨env', s', ?_, hs', he', hn'.mono ?_⟩
    · simpa only [allocDecls, hp, default_bool, Bind.bind, Except.bind,
        Pure.pure, Except.pure] using hr
    · intro n hmem
      simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using hmem

/-- Binding genuinely Boolean arguments succeeds; normalization success on
its own would not establish their type. -/
theorem bindParams_bool (ps : List Param) (bs : List Bool)
    {s : ExecState} {env : LocalEnv} {names : List String}
    (ht : ∀ p ∈ ps, p.typ = .bool) (hlen : ps.length = bs.length)
    (hs : BoolHeap s) (he : EnvRoots s env) (hn : NamesPresent names env) :
    ∃ env' s', bindParams env s ps (bs.map GoValue.bool) = .ok (env', s') ∧
      BoolHeap s' ∧ EnvRoots s' env' ∧
      NamesPresent (ps.map Param.id ++ names) env' := by
  induction ps generalizing bs s env names with
  | nil =>
    have hb : bs = [] := by simpa using hlen.symm
    subst bs
    exact ⟨env, s, rfl, hs, he, hn⟩
  | cons p ps ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hp : p.typ = .bool := ht p (by simp)
      have hps : ∀ q ∈ ps, q.typ = .bool := fun q hq => ht q (by simp [hq])
      have hlen' : ps.length = bs.length := by simpa using hlen
      obtain ⟨env', s', hr, hs', he', hn'⟩ := ih bs hps hlen' (hs.alloc b)
        ((he.alloc b).declare (BoolRoot.alloc_new s b) p.id)
        (hn.declare p.id (s.alloc (.bool b) .bool).1)
      refine ⟨env', s', ?_, hs', he', hn'.mono ?_⟩
      · simpa only [List.map_cons, bindParams, hp, normalize_bool, Bind.bind,
          Except.bind, Pure.pure, Except.pure] using hr
      · intro n hmem
        simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using hmem

theorem pinResultLocs_bool (ps : List Param) {s : ExecState} {env : LocalEnv}
    (he : EnvRoots s env) (hn : NamesPresent (ps.map Param.id) env) :
    ∃ locs, pinResultLocs env ps = .ok locs ∧ locs.length = ps.length ∧
      ∀ loc ∈ locs, BoolRoot s loc := by
  induction ps with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons p ps ih =>
    obtain ⟨loc, hl⟩ := hn p.id (by simp)
    obtain ⟨locs, hr, hlen, hroots⟩ := ih (hn.mono (by intro n h; simp [h]))
    refine ⟨loc :: locs, ?_, by simp [hlen], ?_⟩
    · simp [pinResultLocs, hl, hr]; rfl
    · intro root hroot
      simp only [List.mem_cons] at hroot
      rcases hroot with rfl | hroot
      · exact he.lookup hl
      · exact hroots root hroot

/-- Readout needs pinned valid roots, independently of the current frame. -/
theorem loadMany_bool {s : ExecState} {locs : List Loc}
    (h : ∀ loc ∈ locs, BoolRoot s loc) :
    ∃ bs : List Bool, loadMany s locs = .ok (bs.map GoValue.bool) ∧
      bs.length = locs.length := by
  induction locs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons loc locs ih =>
    obtain ⟨b, hb⟩ := (h loc (by simp)).load
    obtain ⟨bs, hbs, hlen⟩ := ih (fun l hl => h l (by simp [hl]))
    exact ⟨b :: bs, by simp [loadMany, hb, hbs]; rfl, by simp [hlen]⟩

end GoLean.GoCore.BooleanRuntime
