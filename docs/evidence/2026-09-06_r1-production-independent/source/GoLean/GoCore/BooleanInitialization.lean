import GoLean.GoCore.BooleanSetup
import GoLean.GoCore.BooleanTyping

/-! Exact initialized storage for the scoped Boolean profile.

The canonical state/environment definitions describe allocation order directly.
The helper equations and `setup_typed_exact` prove that the REAL binder,
allocator and program driver construct them. They are not alternative
evaluators, fixture whitelists, or successful-execution premises.
Structural control typing and bounded execution safety are connected separately.
-/
namespace GoLean.GoCore.BooleanRuntime
open Machine

def boolCell (b : Bool) : HeapCell := .value .bool (.bool b)

/-- Install consecutive root addresses using actual lexical declaration. -/
def declareRoots (env : LocalEnv) (start : Nat) : List String → LocalEnv
  | [] => env
  | name :: names => declareRoots (env.declare name (.base ⟨start⟩)) (start + 1) names

theorem declareRoots_append (env : LocalEnv) (start : Nat) (xs ys : List String) :
    declareRoots env start (xs ++ ys) =
      declareRoots (declareRoots env start xs) (start + xs.length) ys := by
  induction xs generalizing env start with
  | nil => simp [declareRoots]
  | cons x xs ih => simpa [declareRoots, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using ih (env.declare x (.base ⟨start⟩)) (start + 1)

theorem declareRoots_lookup_absent (env : LocalEnv) (start : Nat)
    (names : List String) (name : String) (h : name ∉ names) :
    (declareRoots env start names).lookup name = env.lookup name := by
  induction names generalizing env start with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [declareRoots, ih _ _ h.2, lookup_declare,
      if_neg (Ne.symm h.1)]

/-- Distinct binding keys retain their own allocated location, despite the
reverse order in which declarations are stored in the scope. -/
theorem declareRoots_lookup (env : LocalEnv) (start : Nat) (names : List String)
    (h : names.Nodup) (i : Nat) (hi : i < names.length) :
    (declareRoots env start names).lookup names[i] = some (.base ⟨start + i⟩) := by
  induction names generalizing env start i with
  | nil => simp at hi
  | cons x xs ih =>
    have hd := List.nodup_cons.mp h
    cases i with
    | zero =>
      simpa [declareRoots, lookup_declare] using
        declareRoots_lookup_absent (env.declare x (.base ⟨start⟩)) (start + 1) xs x hd.1
    | succ i =>
      simpa [declareRoots, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (env.declare x (.base ⟨start⟩)) (start + 1) hd.2 i (by simpa using hi)

/-- The real argument binder's complete environment and heap result. -/
theorem bindParams_exact (ps : List Param) (bs : List Bool)
    (env : LocalEnv) (s : ExecState)
    (ht : ∀ p ∈ ps, p.typ = .bool) (hlen : ps.length = bs.length) :
    bindParams env s ps (bs.map GoValue.bool) =
      .ok (declareRoots env s.heap.size (ps.map Param.id),
        {s with heap := s.heap ++ (bs.map boolCell).toArray}) := by
  induction ps generalizing bs env s with
  | nil =>
    have hb : bs = [] := by simpa using hlen.symm
    subst bs
    simp [bindParams, declareRoots, pure, Except.pure]
  | cons p ps ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hp := ht p (by simp)
      have hr := ih bs (env.declare p.id (.base ⟨s.heap.size⟩))
        (s.alloc (.bool b) .bool).2
        (fun q hq => ht q (by simp [hq])) (by simpa using hlen)
      simpa only [List.map_cons, bindParams, hp, normalize_bool,
        Bind.bind, Except.bind, Pure.pure, Except.pure,
        declareRoots, ExecState.alloc, ExecState.allocCell, Array.size_push,
        boolCell, List.push_append_toArray] using hr

/-- The real local allocator's complete result, including every zero value. -/
theorem allocDecls_exact (ps : List Param) (env : LocalEnv) (s : ExecState)
    (ht : ∀ p ∈ ps, p.typ = .bool) :
    allocDecls env s ps =
      .ok (declareRoots env s.heap.size (ps.map Param.id),
        {s with heap := s.heap ++ (List.replicate ps.length (boolCell false)).toArray}) := by
  induction ps generalizing env s with
  | nil => simp [allocDecls, declareRoots, pure, Except.pure]
  | cons p ps ih =>
    have hp := ht p (by simp)
    have hr := ih (env.declare p.id (.base ⟨s.heap.size⟩))
      (s.alloc (.bool false) .bool).2 (fun q hq => ht q (by simp [hq]))
    simpa only [List.map_cons, List.length_cons, allocDecls, hp, default_bool,
      Bind.bind, Except.bind, Pure.pure, Except.pure,
      declareRoots, ExecState.alloc, ExecState.allocCell, Array.size_push,
      boolCell, List.push_append_toArray, List.replicate_succ] using hr

theorem pinResultLocs_of_lookup (ps : List Param) (env : LocalEnv) (root : Nat → Loc)
    (h : ∀ i (hi : i < ps.length), env.lookup ps[i].id = some (root i)) :
    pinResultLocs env ps = .ok ((List.range ps.length).map root) := by
  induction ps generalizing root with
  | nil => rfl
  | cons p ps ih =>
    have hh := h 0 (by simp)
    change env.lookup p.id = some (root 0) at hh
    have hr := ih (fun i => root (i + 1)) (by
      intro i hi
      exact h (i + 1) (by simpa using Nat.succ_lt_succ hi))
    simp [pinResultLocs, hh, hr, List.range_succ_eq_map, List.map_map,
      Function.comp_def]
    rfl

def initialNames (f : Func) : List String :=
  (f.args.toList ++ f.results.toList).map Param.id

def initialEnv (f : Func) : LocalEnv := declareRoots [] 0 (initialNames f)

def initialResults (f : Func) : List Loc :=
  (List.range f.results.size).map (fun i => .base ⟨f.args.size + i⟩)

def initialState (p : Program) (f : Func) (bs : List Bool) : ExecState :=
  { programState p with
    heap := (bs.map boolCell ++ List.replicate f.results.size (boolCell false)).toArray }

theorem initialEnv_argument {f : Func} (hd : (initialNames f).Nodup)
    (i : Nat) (hi : i < f.args.size) :
    (initialEnv f).lookup f.args[i].id = some (.base ⟨i⟩) := by
  have hh := declareRoots_lookup [] 0 (initialNames f) hd i
    (by simp [initialNames]; omega)
  simpa [initialEnv, initialNames, List.getElem_append_left, hi] using hh

theorem initialEnv_result {f : Func} (hd : (initialNames f).Nodup)
    (i : Nat) (hi : i < f.results.size) :
    (initialEnv f).lookup f.results[i].id = some (.base ⟨f.args.size + i⟩) := by
  have hh := declareRoots_lookup [] 0 (initialNames f) hd (f.args.size + i)
    (by simp [initialNames]; omega)
  simpa [initialEnv, initialNames, List.getElem_append_right, hi] using hh

theorem initialEnv_pins {f : Func} (hd : (initialNames f).Nodup) :
    pinResultLocs (initialEnv f) f.results.toList = .ok (initialResults f) := by
  apply pinResultLocs_of_lookup
  intro i hi
  simpa using initialEnv_result hd i (by simpa using hi)

theorem initialState_argument (p : Program) (f : Func) (bs : List Bool)
    (i : Nat) (hi : i < bs.length) :
    loadLoc (initialState p f bs) (.base ⟨i⟩) = .ok (.bool bs[i]) := by
  simp [loadLoc, Heap.lookup, initialState, List.getElem?_append_left,
    hi, boolCell]

theorem initialState_result (p : Program) (f : Func) (bs : List Bool)
    (hlen : bs.length = f.args.size) (i : Nat) (hi : i < f.results.size) :
    loadLoc (initialState p f bs) (.base ⟨f.args.size + i⟩) = .ok (.bool false) := by
  simp [loadLoc, Heap.lookup, initialState, hi, hlen, boolCell]

theorem EnvRoots.locSup_le {s : ExecState} {env : LocalEnv} (h : EnvRoots s env) :
    LocalEnv.locSup env ≤ s.nextAddr := by
  rw [localEnvLocSup_eq, supBy_le_iff]
  intro scope hs
  rw [scopeLocSup_eq, supBy_le_iff]
  intro binding hb
  obtain ⟨a, ha, hbound⟩ := (h scope hs binding hb).bound
  simp only [ha, Loc.locSup, Loc.rootBase, ExecState.nextAddr]
  omega

theorem BoolHeap.heapLocSup {s : ExecState} (h : BoolHeap s) : Heap.locSup s.heap = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [Heap.locSup_le_iff]
  intro cell hc
  obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hc
  obtain ⟨b, hb⟩ := h i hi
  have hv := (Array.getElem?_eq_some_iff.mp hb).2
  rw [← he, hv]
  exact Nat.le_refl _

theorem booleanState_wf {p : Program} {s : ExecState}
    (hp : Admission.BooleanSyntax p) (hh : BoolHeap s)
    (hc : SameContext (programState p) s) : StateWf s := by
  have hf : s.functions = p.funcs := (congrArg ExecState.functions hc).symm
  simp [StateWf, ExecState.locSup, hh.heapLocSup, hf, booleanSyntax_funcListSup hp]

theorem booleanEntry_wf {p : Program} {s : ExecState} {f : Func} {env : LocalEnv}
    (hp : Admission.BooleanSyntax p) (hf : f ∈ p.funcs.toList)
    (hh : BoolHeap s) (he : EnvRoots s env)
    (hc : SameContext (programState p) s) :
    MachineWf s (.exec f.body env (.frame [] [] [] [] .stop)) := by
  refine ⟨booleanState_wf hp hh hc, ?_, Config.itersNormalized_true _ _⟩
  have hb := boolStmt_locSup (hp.2.2 f hf).2.2.2.2.2
  simpa [ConfigWf, Config.locSup, Cont.locSup, locListSup,
    LocalEnv.locSup, targetPlansSup, deferListSup, hb] using he.locSup_le

/-- Strong scoped admission yields canonical actual setup and all structural
storage/address premises for the Boolean control invariant. This no-initializer
profile consumes neither setup fuel nor choices. No later execution is assumed. -/
theorem setup_typed_exact {p : Program} {name : String} {bs : List Bool}
    (h : BooleanTyping.TypedBooleanAdmission p name (bs.map GoValue.bool).toArray)
    (fuel : Nat) (ch : Choices) :
    ∃ f : Func, findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      BooleanTyping.FunctionTyped f ∧
      runProgramSetupM fuel p name (bs.map GoValue.bool).toArray ch =
        .ok (.exec f.body (initialEnv f) (.frame [] [] [] [] .stop),
          initialState p f bs, initialResults f, ch) ∧
      MachineWf (initialState p f bs)
        (.exec f.body (initialEnv f) (.frame [] [] [] [] .stop)) ∧
      BoolHeap (initialState p f bs) ∧ EnvRoots (initialState p f bs) (initialEnv f) ∧
      NamesPresent (initialNames f) (initialEnv f) ∧
      (∀ loc ∈ initialResults f, BoolRoot (initialState p f bs) loc) ∧
      SameContext (programState p) (initialState p f bs) ∧
      bs.length = f.args.size := by
  obtain ⟨f, env, s, locs, hf, hsetup, hh, he, hn, hr, hl, hc, hsize⟩ :=
    setup_boolean h.1 fuel ch
  have hft := h.2 f (findFunction_mem hf)
  have harity : f.args.size = bs.length := by
    have ha := h.1.2.1
    simp only [Admission.Entry, hf] at ha
    simpa using ha.1
  let env₁ := declareRoots [] 0 (f.args.toList.map Param.id)
  let s₁ : ExecState := {programState p with heap := (bs.map boolCell).toArray}
  have hbind : bindParams [] (programState p) f.args.toList (bs.map GoValue.bool) =
      .ok (env₁, s₁) := by
    simpa [env₁, s₁, programState] using
      bindParams_exact f.args.toList bs [] (programState p) hft.1 (by simpa using harity)
  have halloc : allocDecls env₁ s₁ f.results.toList =
      .ok (initialEnv f, initialState p f bs) := by
    have ha := allocDecls_exact f.results.toList env₁ s₁ hft.2.1
    simpa [initialEnv, initialNames, initialState, env₁, s₁, declareRoots_append,
      List.map_append, ← List.append_toArray, harity] using ha
  have hpin := initialEnv_pins hft.2.2.1
  have hg : p.globals = #[] := Array.eq_empty_of_size_eq_zero h.1.2.2.1
  have hreserved := reservedPrefix_runtime h.1.1.1
  have hw := programState_wf h.1.2.2
  have hinit := booleanSyntax_no_init h.1.2.2
  have hseed := seedGlobals_empty p
  dsimp only [programState] at hseed hw hbind
  have hexact : runProgramSetupM fuel p name (bs.map GoValue.bool).toArray ch =
      .ok (.exec f.body (initialEnv f) (.frame [] [] [] [] .stop),
        initialState p f bs, initialResults f, ch) := by
    simp [runProgramSetupM, hf, harity, hreserved, hg,
      hseed, hw, runPkgInitM, hinit, hbind, halloc, hpin,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [hexact] at hsetup
  have heq := Except.ok.inj hsetup
  have hstate : initialState p f bs = s := congrArg (fun x => x.2.1) heq
  have henv : initialEnv f = env := by
    have heqconfig := congrArg (fun x => x.1) heq
    cases heqconfig
    rfl
  have hlocs : initialResults f = locs := congrArg (fun x => x.2.2.1) heq
  refine ⟨f, hf, hft, hexact, ?_⟩
  rw [hstate, henv, hlocs]
  exact ⟨booleanEntry_wf h.1.2.2 (findFunction_mem hf) hh he hc,
    hh, he, hn, hr, hc, harity.symm⟩

theorem initialResults_distinct (f : Func) : (initialResults f).Nodup := by
  apply List.Pairwise.map _ ?_ List.nodup_range
  intro i j hne h
  have he : f.args.size + i = f.args.size + j := congrArg Loc.rootBase h
  exact hne (Nat.add_left_cancel he)

end GoLean.GoCore.BooleanRuntime
