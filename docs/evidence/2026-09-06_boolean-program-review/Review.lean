import GoLean.GoCore.BooleanSetup
import GoLean.GoCore.BooleanTyping
import GoLean.GoCore.BooleanSafety
import GoLean.GoCore.MultiSound
import GoLean.GoCore.ProgramTrace
import GoLean.GoCore.Trace
import Tests.BooleanTypingFixture

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

namespace GoLean.GoCore.BooleanRuntime
open BooleanTyping Admission Machine

/-- Scoped admission supplies the actual driver entry invariant for every
Boolean argument array. Setup fuel and choices remain arbitrary. -/
theorem setup_typed {p : Program} {name : String} {args : Array GoValue}
    (h : TypedBooleanAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ (f : Func) (env : LocalEnv) (s : ExecState) (locs : List Loc),
      findFunctionIn? p.funcs ⟨name⟩ = some f ∧ FunctionTyped f ∧
      runProgramSetupM fuel p name args ch =
        .ok (.exec f.body env (.frame [] [] [] [] .stop), s, locs, ch) ∧
      Inv (programState p) locs s (.exec f.body env (.frame [] [] [] [] .stop)) ∧
      locs.length = f.results.size := by
  obtain ⟨f, env, s, locs, hf, hsetup, hh, he, hn, hr, hl, hc, _⟩ :=
    setup_boolean h.1 fuel ch
  have ht := h.2 f (findFunction_mem hf)
  have hcover : Covers (initialContext f) env := Covers.of_names (by
    simpa [initialContext] using hn)
  exact ⟨f, env, s, locs, hf, ht, hsetup,
    ⟨hc, hh, hr, initial_control ht hcover he,
      booleanEntry_wf h.1.2.2 (findFunction_mem hf) hh he hc⟩, hl⟩

/-- The canonical initialized values and locations establish the same
invariant used for all-successor preservation and progress. -/
theorem setup_typed_exact_inv {p : Program} {name : String} {bs : List Bool}
    (h : TypedBooleanAdmission p name (bs.map GoValue.bool).toArray)
    (fuel : Nat) (ch : Choices) :
    ∃ f : Func, findFunctionIn? p.funcs ⟨name⟩ = some f ∧ FunctionTyped f ∧
      runProgramSetupM fuel p name (bs.map GoValue.bool).toArray ch =
        .ok (.exec f.body (initialEnv f) (.frame [] [] [] [] .stop),
          initialState p f bs, initialResults f, ch) ∧
      Inv (programState p) (initialResults f) (initialState p f bs)
        (.exec f.body (initialEnv f) (.frame [] [] [] [] .stop)) ∧
      bs.length = f.args.size := by
  obtain ⟨f, hf, ht, hs, hw, hh, he, hn, hr, hc, ha⟩ := setup_typed_exact h fuel ch
  have hcover : Covers (initialContext f) (initialEnv f) := Covers.of_names (by
    simpa [initialContext, initialNames] using hn)
  exact ⟨f, hf, ht, hs, ⟨hc, hh, hr, initial_control ht hcover he, hw⟩, ha⟩

/-- The actual sequential whole-program driver either reads Boolean results
at the declared arity, with empty output, or exhausts its supplied fuel.
This theorem gives no lower bound sufficient for termination. -/
theorem runProgram_typed {p : Program} {name : String} {args : Array GoValue}
    (h : TypedBooleanAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ f : Func, findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      ((∃ bs : List Bool, bs.length = f.results.size ∧
        runProgramM fuel p name args ch = .ok { values := (bs.map GoValue.bool).toArray }) ∨
       runProgramM fuel p name args ch = .error .fuelOut) := by
  obtain ⟨f, env, s, locs, hf, _, hs, hi, hl⟩ := setup_typed h fuel ch
  refine ⟨f, hf, ?_⟩
  rcases hi.run_ok_or_fuelOut fuel ch with ⟨t, ch', hr⟩ | hr
  · obtain ⟨bs, hb, hlen⟩ := hi.run_readout hr
    exact .inl ⟨bs, hlen.trans hl, by simp [runProgramM, hs, hr, hb,
      Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
  · exact .inr (by simp [runProgramM, hs, hr, Bind.bind, Except.bind])

theorem Control.not_blocked {root roots c} (h : Control root roots c) :
    isBlockedConfig c = false := by cases h <;> rfl

theorem Control.no_abort {root roots c} (h : Control root roots c) :
    c.abort? = none := by cases h <;> rfl

theorem Control.no_spawn {root roots c} (h : Control root roots c) :
    spawnPlan c = none := by
  cases h <;> try rfl
  case retBool hk => cases hk <;> rfl
  case retAddr hl hk => cases hk <;> rfl

theorem Control.no_select {root roots c} (h : Control root roots c) :
    selectApplyPlan c = none := by
  cases h <;> try rfl
  case retBool hk => cases hk <;> rfl
  case retAddr hl hk => cases hk <;> rfl

theorem Control.no_registry {root roots c} (h : Control root roots c) (s : ExecState) :
    c.registryCommits s = false := by
  cases h <;> try rfl
  case retBool hk => cases hk <;> rfl
  case retAddr hl hk => cases hk <;> rfl

theorem Control.no_flag {root roots c} (h : Control root roots c)
    (s : ExecState) (c' : Config) : c.afterStepFlag s c' = none := by
  simp [Config.afterStepFlag, h.no_spawn, h.no_registry]

theorem Control.terminal_iff {root roots c} (_h : Control root roots c) :
    c.isTerminal = true ↔ c = .next .stop := by
  cases c <;> try simp [Config.isTerminal]
  case next k => cases k <;> simp only [reduceCtorEq]

theorem Control.main_outcome {root roots c} (h : Control root roots c)
    (hn : c ≠ .next .stop) (s : ExecState) :
    (MultiConfig.mk #[Thread.running c none] s 0).mainOutcome? = none := by
  cases h <;> try rfl
  · contradiction
  · rename_i k hk
    cases hk <;> rfl

theorem Control.singleton_thread {root roots c} (h : Control root roots c)
    (s : ExecState) (ch : Choices) :
    stepThread s #[.running c none] 0 ch = (stepFn s c ch).map
      (fun r => (#[.running r.1 none], r.2.1, r.2.2, ⟨0, .privateStep, [], []⟩)) := by
  unfold stepThread
  have h0 : (#[Thread.running c none] : Array Thread)[0]? = some (.running c none) := rfl
  rw [h0]
  simp only [h.not_blocked, Bool.false_eq_true, reduceIte, h.no_abort, h.no_spawn]
  rw [arrivalPlan_singleton]
  simp only [Bind.bind, Except.bind, h.no_select, h.silent]
  cases hstep : stepFn s c ch with
  | error e => rfl
  | ok r =>
      obtain ⟨c', s', ch'⟩ := r
      simp [Except.map, Thread.afterStep, h.no_flag]

theorem Control.singleton_step {root roots c} (h : Control root roots c)
    (hn : c ≠ .next .stop) (s : ExecState) (ch : Choices) :
    stepMulti ⟨#[.running c none], s, 0⟩ ch = (stepFn s c ch).map
      (fun r => (⟨#[.running r.1 none], r.2.1, 0⟩, r.2.2, ⟨0, .privateStep, [], []⟩)) := by
  have hd : c.isTerminal = false := Bool.eq_false_iff.mpr (fun ht => hn (h.terminal_iff.mp ht))
  have hrun : threadRunnable s (.running c none) = true := by
    simp [threadRunnable, hd, h.not_blocked]
  have hinto : stepThreadInto ⟨#[.running c none], s, 0⟩ 0 ch =
      (stepFn s c ch).map (fun r =>
        (⟨#[.running r.1 none], r.2.1, 0⟩, r.2.2, ⟨0, .privateStep, [], []⟩)) := by
    unfold stepThreadInto
    show (stepThread s #[.running c none] 0 ch).bind _ = _
    rw [h.singleton_thread]
    cases stepFn s c ch <;> simp [Except.bind, Except.map]
  unfold stepMulti
  have h0 : (#[Thread.running c none] : Array Thread)[0]? = some (.running c none) := rfl
  simp only [h0]
  by_cases hb : Thread.atBoundary (.running c none) = true
  · simp only [hb, reduceIte]
    rw [schedSlots_singleton hrun]
    dsimp only
    rw [show Choices.consumeAtE (Thread.boundarySite (.running c none)) [0].length ch =
        (0, ch, []) from Choices.consumeAtE_le_one (by simp)]
    simp only [List.getElem?_cons_zero, Bind.bind, Except.bind]
    rw [hinto]
    cases stepFn s c ch <;> simp [Except.map]
  · simp only [Bool.not_eq_true] at hb
    simp only [hb, Bool.false_eq_true, reduceIte]
    exact hinto

theorem Control.runConfig_zero {root roots c} (h : Control root roots c)
    (hn : c ≠ .next .stop) (s : ExecState) (ch : Choices) :
    runConfig 0 s c ch = .error .fuelOut := by
  cases h <;> try rfl
  · contradiction
  · rename_i k hk
    cases hk <;> rfl

/-- The shipped output-folding singleton driver agrees at the SAME fuel,
store and choice stream with the actual sequential driver. No event output
or choice consumption occurs, including on the exhaustion path. -/
theorem Inv.pool_eq_runConfig {context results s c} (h : Inv context results s c)
    (fuel : Nat) (ch : Choices) (rs : RaceState) (out : GoString) :
    execProgLoopOut fuel ⟨#[.running c none], s, 0⟩ rs ch out =
      (out, runConfig fuel s c ch) := by
  induction fuel generalizing s c ch with
  | zero =>
      by_cases ht : c = .next .stop
      · subst c; rfl
      · have hd : c.isTerminal = false := Bool.eq_false_iff.mpr
          (fun hterm => ht (h.control.terminal_iff.mp hterm))
        have hrun : threadRunnable s (.running c none) = true := by
          simp [threadRunnable, hd, h.control.not_blocked]
        rw [h.control.runConfig_zero ht]
        unfold execProgLoopOut
        simp [h.control.main_outcome ht, runnableIdxs_singleton hrun, MultiConfig.panicMsg?,
          throw, throwThe, MonadExceptOf.throw]
  | succ fuel ih =>
      rcases control_advances h.heap h.control with rfl | ha
      · rfl
      · obtain ⟨d, u, hu, _, _⟩ := ha ch
        have hn : c ≠ .next .stop := by intro he; subst c; simp [stepFn] at hu
        have hd : c.isTerminal = false := Bool.eq_false_iff.mpr
          (fun ht => hn (h.control.terminal_iff.mp ht))
        have hrun : threadRunnable s (.running c none) = true := by
          simp [threadRunnable, hd, h.control.not_blocked]
        have hm := h.control.singleton_step hn s ch
        rw [hu] at hm
        simp only [Except.map] at hm
        rw [runConfig_eq_loop, execStmtLoop_step hu, ← runConfig_eq_loop]
        unfold execProgLoopOut
        simp [h.control.main_outcome hn, runnableIdxs_singleton hrun, MultiConfig.panicMsg?,
          hm, raceUpdate_single, ih (h.step (stepFn_sound hu))]

/-- Actual whole-program driver correspondence in the admitted Boolean
domain. The output-folding driver preserves empty output even on fuel-out. -/
theorem runProgramPool_eq_sequential {p : Program} {name : String} {args : Array GoValue}
    (h : TypedBooleanAdmission p name args) (fuel : Nat) (ch : Choices) :
    runProgramPoolOutM fuel p name args ch =
      (runProgramM fuel p name args ch).mapError (fun e => (e, GoString.empty)) := by
  obtain ⟨f, env, s, locs, _, _, hs, hi, _⟩ := setup_typed h fuel ch
  simp only [runProgramPoolOutM, hs, hi.pool_eq_runConfig, runProgramM,
    Bind.bind, Except.bind]
  cases hr : runConfig fuel s (.exec f.body env (.frame [] [] [] [] .stop)) ch with
  | error e => rfl
  | ok v =>
      obtain ⟨sf, chf⟩ := v
      dsimp only
      cases loadMany sf locs <;> rfl

/-- Typed readout or explicit fuel exhaustion for the SHIPPED driver,
uniformly over every supplied choice stream. No panic or model refusal is
hidden in the success alternative; both paths have proved empty output. -/
theorem runProgramPool_typed {p : Program} {name : String} {args : Array GoValue}
    (h : TypedBooleanAdmission p name args) (fuel : Nat) (ch : Choices) :
    ∃ f : Func, findFunctionIn? p.funcs ⟨name⟩ = some f ∧
      ((∃ bs : List Bool, bs.length = f.results.size ∧
        runProgramPoolOutM fuel p name args ch =
          .ok { values := (bs.map GoValue.bool).toArray, output := GoString.empty }) ∨
       runProgramPoolOutM fuel p name args ch = .error (.fuelOut, GoString.empty)) := by
  obtain ⟨f, hf, hr⟩ := runProgram_typed h fuel ch
  refine ⟨f, hf, ?_⟩
  rw [runProgramPool_eq_sequential h]
  rcases hr with ⟨bs, hb, hr⟩ | hr
  · exact .inl ⟨bs, hb, by rw [hr]; rfl⟩
  · exact .inr (by rw [hr]; rfl)

theorem runProgramPool_no_refusal {p : Program} {name : String} {args : Array GoValue}
    (h : TypedBooleanAdmission p name args) (fuel : Nat) (ch : Choices)
    (reason : Refusal) (out : GoString) :
    runProgramPoolOutM fuel p name args ch ≠ .error (.refusal reason, out) := by
  obtain ⟨_, _, hr⟩ := runProgramPool_typed h fuel ch
  rcases hr with ⟨_, _, hr⟩ | hr <;> rw [hr] <;> simp

theorem Control.no_seq_consumption {root roots c} (h : Control root roots c)
    (s : ExecState) : seqConsumption s c = none := by
  cases h <;> try rfl
  case next hk => cases hk <;> rfl
  case retBool hk => cases hk <;> rfl
  case retAddr hl hk => cases hk <;> rfl
  case exec hc he hs hk => cases hs <;> rfl
  case execSeq hc he hs ht hk => cases hs <;> rfl
  case returning hk => cases hk <;> rfl

/-- A successful sequential run supplies an exact bounded trace on the
original stream, a typed final invariant, actual readout and the shipped
pool execution. All conclusions use that SAME stream, not existentially
reselected choices. Functional clients may supply a separate termination
witness; generic safety is already available without this success premise. -/
theorem Inv.success_contract {context results s c fuel ch sf chf}
    (h : Inv context results s c) (hr : runConfig fuel s c ch = .ok (sf, chf)) :
    chf = ch ∧ ∃ n : Nat, n ≤ fuel ∧
      GoLean.Semantics.Trace n s c ch sf (.next .stop) ch ∧
      Inv context results sf (.next .stop) ∧
      (∃ bs : List Bool, loadMany sf results = .ok (bs.map GoValue.bool) ∧
        bs.length = results.length) ∧
      GoLean.Semantics.Pool.Run fuel ⟨#[.running c none], s, 0⟩ {} ch GoString.empty
        (GoString.empty, .ok (sf, ch)) := by
  have hc := h.run_choices hr
  subst chf
  obtain ⟨n, hn, ht⟩ := GoLean.Semantics.run_ok_iff.mp
    (by simpa only [runConfig_eq_loop] using hr)
  exact ⟨rfl, n, hn, ht, h.steps ht.erase, h.run_readout hr,
    GoLean.Semantics.Pool.run_iff.mp (by rw [h.pool_eq_runConfig, hr])⟩

end GoLean.GoCore.BooleanRuntime
namespace GoLean.GoCore.BooleanRuntime.ProgramTests
open Machine BooleanTyping

set_option maxRecDepth 4096

theorem argument_admitted (b : Bool) :
    TypedBooleanAdmission BooleanTyping.Tests.nativeFixture "Argument" #[.bool b] := by
  apply checkTypedBoolean_sound
  cases b <;> with_unfolding_all rfl

theorem argument_result (b : Bool) (ch : Choices) :
    runProgramPoolOutM 64 BooleanTyping.Tests.nativeFixture "Argument" #[.bool b] ch =
      .ok { values := #[.bool b], output := GoString.empty } := by
  rw [runProgramPool_eq_sequential (argument_admitted b)]
  cases b <;> with_unfolding_all rfl

theorem zero_fuel_is_exhaustion (b : Bool) (ch : Choices) :
    runProgramPoolOutM 0 BooleanTyping.Tests.nativeFixture "Argument" #[.bool b] ch =
      .error (.fuelOut, GoString.empty) := by
  rw [runProgramPool_eq_sequential (argument_admitted b)]
  cases b <;> with_unfolding_all rfl

theorem nested_shadow_result (ch : Choices) :
    runProgramPoolOutM 128 BooleanTyping.Tests.nativeFixture "Shadow" #[] ch =
      .ok { values := #[.bool false], output := GoString.empty } := by
  rw [runProgramPool_eq_sequential (checkTypedBoolean_sound BooleanTyping.Tests.native_shadow)]
  with_unfolding_all rfl

theorem branch_result (ch : Choices) :
    runProgramPoolOutM 64 BooleanTyping.Tests.nativeFixture "Branches" #[] ch =
      .ok { values := #[.bool false], output := GoString.empty } := by
  rw [runProgramPool_eq_sequential (checkTypedBoolean_sound BooleanTyping.Tests.native_branches)]
  with_unfolding_all rfl

theorem zero_local_and_result (ch : Choices) :
    runProgramPoolOutM 64 BooleanTyping.Tests.nativeFixture "Zero" #[] ch =
      .ok { values := #[.bool false], output := GoString.empty } := by
  rw [runProgramPool_eq_sequential (checkTypedBoolean_sound BooleanTyping.Tests.native_zero)]
  with_unfolding_all rfl

/-- The driver must retain an existing byte prefix, including NUL and SOH,
and the entire choice tape when classifying an already normal terminal. -/
theorem terminal_at_zero_fuel (ch : Choices) :
    execProgLoopOut 0 ⟨#[.running (.next .stop) none], {}, 0⟩ {} ch
      ⟨#[0, 1, 10, 13]⟩ = (⟨#[0, 1, 10, 13]⟩, .ok ({}, ch)) := by rfl

end GoLean.GoCore.BooleanRuntime.ProgramTests

namespace GoLean.GoCore.BooleanRuntime.IndependentBridgeReview
open Machine BooleanTyping

def ready : Config := .next (.frame [] [] [] [] .stop)

theorem ready_inv : Inv {} [] {} ready := by
  refine ⟨rfl, ?_, by simp, .next .barrier, ?_⟩
  · intro i hi
    simp at hi
  · decide +kernel

-- Exact boundary: one actual barrier step, no slack fuel, arbitrary tape.
theorem last_step_at_exact_fuel (ch : Choices) (out : GoString) (race : RaceState) :
    execProgLoopOut 1 ⟨#[.running ready none], {}, 0⟩ race ch out =
      (out, .ok ({}, ch)) := by
  rw [ready_inv.pool_eq_runConfig]
  rfl

theorem same_state_at_insufficient_fuel (ch : Choices) (out : GoString) :
    execProgLoopOut 0 ⟨#[.running ready none], {}, 0⟩ {} ch out =
      (out, .error .fuelOut) := by
  rw [ready_inv.pool_eq_runConfig]
  rfl

-- Reaching normal completion at fuel zero differs from raw stepping it.
theorem raw_terminal_does_not_step (s : ExecState) (ch : Choices) :
    ¬ ∃ c' s' ch', stepFn s (.next .stop) ch = .ok (c', s', ch') := by
  simp [stepFn]

-- Generic safety requires only admission, without a successful-run premise.
theorem generic_driver_safety {p : Program} {name : String} {args : Array GoValue}
    (ha : TypedBooleanAdmission p name args) (fuel : Nat) (ch : Choices)
    (refusal : Refusal) (out : GoString) :
    runProgramPoolOutM fuel p name args ch ≠ .error (.refusal refusal, out) :=
  runProgramPool_no_refusal ha fuel ch refusal out

-- Successful-trace consumers get the original tape, not fresh witnesses.
theorem exact_trace_tape (ch : Choices) :
    ∃ n, n ≤ 1 ∧ GoLean.Semantics.Trace n {} ready ch {} (.next .stop) ch := by
  have hr : runConfig 1 {} ready ch = .ok ({}, ch) := by rfl
  obtain ⟨_, n, hn, ht, _⟩ := ready_inv.success_contract hr
  exact ⟨n, hn, ht⟩

end GoLean.GoCore.BooleanRuntime.IndependentBridgeReview
