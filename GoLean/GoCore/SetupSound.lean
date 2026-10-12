import GoLean.GoCore.SetupStatement
import GoLean.GoCore.Equations
import GoLean.GoCore.Prefix

/-!
# Proofs for the setup equations G-R1–G-R4 (`SetupStatement.lean`)

[AGENT worker, lane `core/setup-equations-1005`] 2026-10-05; authority and the request as in
`SetupStatement.lean`'s header. Every `<name>_stmt` of G-R1–G-R3 is discharged here as
`theorem <name> : <name>_stmt`, the statement unchanged. Phase 3 (the logic team's approval of G-R4
with answers (a)–(d), 2026-10-05, relayed): G-R4 `runInitConfig_eq_execStmtLoop` — induction on the
fuel through the init loop's one-layer unfolding (`runInitConfig_unfold`, the twin of
`MachineSound.lean`'s `execStmtLoop_unfold`) — then its four `run_*_iff` corollaries (each the
equation followed by `Prefix.lean`'s sequential statement) and the `runPkgInitM` wrapper pair.

The seeding equation rests on ONE loop lemma (`seedLoop`): `seedGlobals`'s `for g in globals, i in
[0:globals.size]` is a `forIn` over the globals with the index range threaded as a `Stream`
(`#print seedGlobals`); the lemma characterizes it by induction over the globals list, carrying
«the stream's position IS the heap's size». The `{}`-store forms of `Equations.lean` are shown to be
the instances at the empty store by the `example`s at the end (their pinned theorems are
unchanged).
-/

namespace GoLean.GoCore.SetupSound

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.SetupStatement
open GoLean.GoCore.Equations (seedGlobals_nil runPkgInitM_none pinResultLocs_eq_of_lookup)

/-! ## `List.mapM` over `Except`, read back -/

private theorem mapM_ok_length {α β : Type} {f : α → Except Stop β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → l'.length = l.length
  | [], l', h => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; rfl
  | a :: l, l', h => by
      rw [List.mapM_cons] at h
      cases ha : f a with
      | error e => simp [ha, Bind.bind, Except.bind] at h
      | ok b =>
        cases hl : l.mapM f with
        | error e => simp [ha, hl, Bind.bind, Except.bind] at h
        | ok bs =>
          simp only [ha, hl, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp [mapM_ok_length hl]

private theorem mapM_ok_getElem {α β : Type} {f : α → Except Stop β} :
    ∀ {l : List α} {l' : List β} (h : l.mapM f = .ok l') (i : Nat) (hi : i < l.length),
      f l[i] = .ok (l'[i]'(by rw [mapM_ok_length h]; exact hi))
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | a :: l, l', h, i, hi => by
      rw [List.mapM_cons] at h
      cases ha : f a with
      | error e => simp [ha, Bind.bind, Except.bind] at h
      | ok b =>
        cases hl : l.mapM f with
        | error e => simp [ha, hl, Bind.bind, Except.bind] at h
        | ok bs =>
          simp only [ha, hl, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          subst h
          cases i with
          | zero => simpa using ha
          | succ i => simpa using mapM_ok_getElem hl i (Nat.lt_of_succ_lt_succ hi)

private theorem mapM_ok_mem {α β : Type} {f : α → Except Stop β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → ∀ b ∈ l', ∃ a ∈ l, f a = .ok b
  | [], l', h, b, hb => by
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; simp at hb
  | a :: l, l', h, b, hb => by
      rw [List.mapM_cons] at h
      cases ha : f a with
      | error e => simp [ha, Bind.bind, Except.bind] at h
      | ok b₀ =>
        cases hl : l.mapM f with
        | error e => simp [ha, hl, Bind.bind, Except.bind] at h
        | ok bs =>
          simp only [ha, hl, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          subst h
          rcases List.mem_cons.mp hb with rfl | hb
          · exact ⟨a, List.mem_cons_self .., ha⟩
          · obtain ⟨a', ha', hfa⟩ := mapM_ok_mem hl b hb
            exact ⟨a', List.mem_cons_of_mem _ ha', hfa⟩

/-! ## The seeding loop -/

/-- The index range `seedGlobals` threads, at position `k` with bound `stop`. -/
private def seedRange (k stop : Nat) : Std.Legacy.Range :=
  { start := k, stop := stop, step := 1, step_pos := Nat.zero_lt_one }

/-- The loop body of `seedGlobals`, as elaborated (`#print seedGlobals`), named so the loop can be
characterized by induction over the globals. `seedGlobals_eq_loop` is `rfl`. -/
private def seedStep (ctx : ProgramCtx) (g : GlobalDef) (p : Store × Std.Legacy.Range) :
    Except Stop (ForInStep (Store × Std.Legacy.Range)) :=
  let s := p.1
  let r := p.2
  match Std.Stream.next? r with
  | none => pure (.done (s, r))
  | some (i, r') => do
      let v ← defaultValue ctx g.typ
      let (loc, s') ← Store.alloc ctx s v g.typ
      if loc != .base ⟨i⟩ then
        throw (.internal s!"global {g.name} seeded at {repr loc}, expected base {i}")
      pure (.yield (s', r'))

private theorem seedGlobals_eq_loop (ctx : ProgramCtx) (globals : Array GlobalDef) :
    seedGlobals ctx {} globals
      = (do
          let r ← forIn globals (({} : Store), seedRange 0 globals.size) (seedStep ctx)
          pure r.1) := rfl

private theorem seedRange_next (k stop : Nat) (h : k < stop) :
    Std.Stream.next? (seedRange k stop) = some (k, seedRange (k + 1) stop) := by
  simp [seedRange, Std.Stream.next?, h]

/-- Seeding a store from an arbitrary store `s` whose heap size IS the stream's position: the loop
pushes the zero cells in order (or refuses with the first refused zero value), and the stream
advances by the count. -/
private theorem seedLoop (ctx : ProgramCtx) :
    ∀ (gs : List GlobalDef) (s : Store) (stop : Nat), s.heap.size + gs.length ≤ stop →
      forIn gs (s, seedRange s.heap.size stop) (seedStep ctx)
        = (fun cells => (({ heap := s.heap ++ cells.toArray } : Store),
            seedRange (s.heap.size + gs.length) stop)) <$> gs.mapM (zeroCell ctx)
  | [], s, stop, _ => by
      simp [List.forIn_nil, List.mapM_nil, Functor.map, Except.map, pure, Except.pure]
  | g :: gs, s, stop, h => by
      rw [List.forIn_cons, List.mapM_cons]
      have hnext := seedRange_next s.heap.size stop (by simp at h; omega)
      simp only [seedStep, hnext]
      cases hd : defaultValue ctx g.typ with
      | error e =>
          simp [hd, zeroCell, Bind.bind, Except.bind, Functor.map, Except.map]
      | ok z =>
          have hn := defaultValue_normalize hd
          have halloc : Store.alloc ctx s z g.typ
              = .ok (.base ⟨s.heap.size⟩, { heap := s.heap.push (.value g.typ z) }) := by
            simp [Store.alloc, hn, Store.allocCell, Bind.bind, Except.bind, pure, Except.pure]
          have ih := seedLoop ctx gs { heap := s.heap.push (.value g.typ z) } stop
            (by simp only [Array.size_push]; simp at h; omega)
          simp only [Array.size_push] at ih
          simp only [halloc, Bind.bind, Except.bind, bne_self_eq_false, Bool.false_eq_true,
            ↓reduceIte, pure, Except.pure]
          rw [ih]
          cases gs.mapM (zeroCell ctx) with
          | error e => simp [zeroCell, hd, Functor.map, Except.map]
          | ok cells =>
              simp only [zeroCell, hd, Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq]
              refine ⟨?_, ?_⟩
              · congr 1
                apply Array.ext'
                simp [Array.toList_append]
              · simp [seedRange, Nat.add_assoc, Nat.add_comm 1]

/-! ## G-R2 -/

theorem seedGlobals_cells : seedGlobals_cells_stmt := by
  intro ctx globals
  rw [seedGlobals_eq_loop, ← Array.forIn_toList]
  have h := seedLoop ctx globals.toList {} globals.size (by simp)
  simp only [Array.size_empty] at h
  rw [h]
  cases globals.toList.mapM (zeroCell ctx) with
  | error e => simp [Functor.map, Except.map, Bind.bind, Except.bind]
  | ok cells => simp [Functor.map, Except.map, Bind.bind, Except.bind, pure, Except.pure]

theorem seedGlobals_heap_size : seedGlobals_heap_size_stmt := by
  intro ctx globals s₀ h
  rw [seedGlobals_cells] at h
  cases hm : globals.toList.mapM (zeroCell ctx) with
  | error e => simp [hm, Functor.map, Except.map] at h
  | ok cells =>
      simp only [hm, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      simp [mapM_ok_length hm]

theorem seedGlobals_cell : seedGlobals_cell_stmt := by
  intro ctx globals s₀ h i hi
  rw [seedGlobals_cells] at h
  cases hm : globals.toList.mapM (zeroCell ctx) with
  | error e => simp [hm, Functor.map, Except.map] at h
  | ok cells =>
      simp only [hm, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      have hi' : i < globals.toList.length := by simpa using hi
      have hz := mapM_ok_getElem hm i hi'
      simp only [zeroCell, Array.getElem_toList] at hz
      cases hd : defaultValue ctx globals[i].typ with
      | error e => simp [hd, Functor.map, Except.map] at hz
      | ok z =>
          refine ⟨z, rfl, ?_⟩
          simp only [hd, Functor.map, Except.map, Except.ok.injEq] at hz
          simp [Heap.lookup, List.getElem?_toArray, List.getElem?_eq_getElem
            (show i < cells.length by rw [mapM_ok_length hm]; exact hi'), ← hz]

private theorem heapCellsSup_eq_zero :
    ∀ {l : List HeapCell}, (∀ c ∈ l, HeapCell.locSup c = 0) → heapCellsSup l = 0
  | [], _ => rfl
  | c :: l, h => by
      simp only [heapCellsSup, h c (List.mem_cons_self ..),
        heapCellsSup_eq_zero (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
      rfl

theorem seedGlobals_wf : seedGlobals_wf_stmt := by
  intro ctx globals s₀ h
  rw [seedGlobals_cells] at h
  cases hm : globals.toList.mapM (zeroCell ctx) with
  | error e => simp [hm, Functor.map, Except.map] at h
  | ok cells =>
      simp only [hm, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      have hcell : ∀ c ∈ cells, HeapCell.locSup c = 0 ∧ HeapCell.normal ctx.types c = true := by
        intro c hc
        obtain ⟨g, -, hg⟩ := mapM_ok_mem hm c hc
        simp only [zeroCell] at hg
        cases hd : defaultValue ctx g.typ with
        | error e => simp [hd, Functor.map, Except.map] at hg
        | ok z =>
            simp only [hd, Functor.map, Except.map, Except.ok.injEq] at hg
            subst hg
            exact ⟨defaultValue_locSup hd, by simpa [HeapCell.normal] using defaultValue_isNormal hd⟩
      refine ⟨?_, ?_⟩
      · show Heap.locSup cells.toArray ≤ Store.nextAddr _
        simp only [Heap.locSup, Store.nextAddr, heapCellsSup_eq_zero (fun c hc => (hcell c hc).1)]
        exact Nat.zero_le _
      · show Heap.normalB ctx.types cells.toArray = true
        simp only [Heap.normalB, List.all_eq_true]
        exact fun c hc => (hcell c hc).2

/-! ## G-R1 -/

theorem runProgramSetup_init : runProgramSetup_init_stmt := by
  intro fuel program name args choices func s₀ s₁ choices₁ env frameEnv s₂ s₃ resultLocs
    hf harity hres hseed hinit hb ha hp
  have hwf : StateWf ⟨program⟩ s₀ := seedGlobals_wf hseed
  simp [runProgramSetupM, hf, harity, hres, hseed, hwf, hinit, hb, ha, hp, Bind.bind, Except.bind]

/-! ## G-R3 -/

theorem setup_lookup_arg_from : setup_lookup_arg_from_stmt := by
  intro program func args env frameEnv s₁ s₂ s₃ hb ha hdistinct i hi
  have hd : namesDistinct (func.args.toList.map (·.id) ++ func.results.toList.map (·.id)) = true := by
    simpa [Array.toList_append, List.map_append] using hdistinct
  obtain ⟨hda, -, hdisj⟩ := namesDistinct_append hd
  have hi' : i < func.args.toList.length := by simpa using hi
  have hmem : func.args.toList[i].id ∈ func.args.toList.map (·.id) :=
    List.mem_map.mpr ⟨_, List.getElem_mem hi', rfl⟩
  rw [← Array.getElem_toList (h := hi'), allocDecls_lookup_preserve _ _ _ ha (hdisj _ hmem)]
  exact bindParams_lookup _ _ _ _ hb hda i hi'

theorem setup_lookup_result_from : setup_lookup_result_from_stmt := by
  intro program func args env frameEnv s₁ s₂ s₃ hb ha hdistinct j hj
  have hd : namesDistinct (func.args.toList.map (·.id) ++ func.results.toList.map (·.id)) = true := by
    simpa [Array.toList_append, List.map_append] using hdistinct
  obtain ⟨-, hdr, -⟩ := namesDistinct_append hd
  have hj' : j < func.results.toList.length := by simpa using hj
  have hsize := bindParams_heap_size _ _ _ _ hb
  rw [← Array.getElem_toList (h := hj'), allocDecls_lookup _ _ _ ha hdr j hj', hsize]
  simp [entrySlot, Nat.add_assoc]

theorem setup_resultLocs_from : setup_resultLocs_from_stmt := by
  intro program func args env frameEnv s₁ s₂ s₃ resultLocs hb ha hdistinct hp
  have := pinResultLocs_eq_of_lookup frameEnv func.results.toList
    (fun j => entrySlot s₁ (func.args.size + j)) (fun j hj => by
      have hj' : j < func.results.size := by simpa using hj
      have := setup_lookup_result_from hb ha hdistinct j hj'
      simpa [Array.getElem_toList] using this)
  rw [this] at hp
  simp only [Except.ok.injEq] at hp
  simpa using hp.symm

theorem setup_heap_size_from : setup_heap_size_from_stmt := by
  intro program func args env frameEnv s₁ s₂ s₃ hb ha
  have h1 := bindParams_heap_size _ _ _ _ hb
  have h2 := allocDecls_heap_size _ _ _ ha
  simp at h1 h2
  omega

/-! ## G-R4 — the init loop and the entry loop -/

section InitLoop

open GoLean.GoCore.ExecutionStatement (Prefix Blocked ZeroCost zeroCost_cases execStmtLoop_nonZero
  execStmtLoop_blocked)

/-- The one-layer unfolding of `runInitConfig`, as an equation (the twin of `execStmtLoop_unfold`). -/
private theorem runInitConfig_unfold (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config)
    (ch : Choices) :
    runInitConfig ctx fuel s c ch
      = (match c with
         | .next .stop => .ok (s, ch)
         | .blockedSend _ _ _ => throw .deadlock
         | .blockedRecv _ _ _ _ _ => throw .deadlock
         | .blockedSelect _ _ _ => throw .deadlock
         | .blockedSync _ _ _ _ => throw .deadlock
         | c =>
             match initPrintRefusal? c with
             | some e => throw e
             | none =>
               match fuel with
               | 0 => throw .fuelOut
               | fuel + 1 => do
                   let (c', s', choices', _) ← stepFn ctx s c ch
                   runInitConfig ctx fuel s' c' choices') := by
  rw [runInitConfig.eq_def]
  rfl

/-- The init loop at a blocked configuration is the deadlock at every fuel (no guard is consulted). -/
private theorem runInitConfig_blocked {ctx : ProgramCtx} {fuel : Nat} {s : Store} {c : Config}
    {ch : Choices} (hb : Blocked c) : runInitConfig ctx fuel s c ch = .error (.terminal .deadlock) := by
  rcases hb with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
    (rw [runInitConfig_unfold]; rfl)

/-- The init loop at a non-zero-cost configuration whose guard is silent: the entry loop's own shape
— fuel-out at 0, one `stepFn` call then the init loop at `fuel + 1`. -/
private theorem runInitConfig_nonZero {ctx : ProgramCtx} {fuel : Nat} {s : Store} {c : Config}
    {ch : Choices} (hz : ¬ ZeroCost c) (hp : initPrintRefusal? c = none) :
    runInitConfig ctx fuel s c ch =
      (match fuel with
       | 0 => .error .fuelOut
       | f + 1 => (stepFn ctx s c ch).bind fun r => runInitConfig ctx f r.2.1 r.1 r.2.2.1) := by
  rw [runInitConfig_unfold]
  unfold ZeroCost Blocked at hz
  split
  · exact absurd (.inl rfl) hz
  · exact absurd (.inr (.inl ⟨_, _, _, rfl⟩)) hz
  · exact absurd (.inr (.inr (.inl ⟨_, _, _, _, _, rfl⟩))) hz
  · exact absurd (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) hz
  · exact absurd (.inr (.inr (.inr (.inr ⟨_, _, _, _, rfl⟩)))) hz
  · rw [hp]
    cases fuel with
    | zero => rfl
    | succ f => simp only [Bind.bind]

/-- **G-R4.** Induction on the fuel, generalizing the store, configuration and tape: at a zero-cost
configuration both loops agree outright; otherwise the no-print premise at `n = 0` silences the
guard, both loops fall to the same fuel match, and on a successful step the premise transfers to
the successor through `Prefix.step`. -/
theorem runInitConfig_eq_execStmtLoop : runInitConfig_eq_execStmtLoop_stmt := by
  intro ctx fuel
  induction fuel with
  | zero =>
    intro σ c ch hnp
    rcases zeroCost_cases c with rfl | hb | hz
    · rw [runInitConfig_unfold, execStmtLoop_unfold]
    · rw [runInitConfig_blocked hb, execStmtLoop_blocked hb]
    · rw [runInitConfig_nonZero hz (hnp 0 σ c ch [] .done (Nat.le_refl 0)), execStmtLoop_nonZero hz]
  | succ f ih =>
    intro σ c ch hnp
    rcases zeroCost_cases c with rfl | hb | hz
    · rw [runInitConfig_unfold, execStmtLoop_unfold]
    · rw [runInitConfig_blocked hb, execStmtLoop_blocked hb]
    · rw [runInitConfig_nonZero hz (hnp 0 σ c ch [] .done (Nat.zero_le _)), execStmtLoop_nonZero hz]
      simp only
      cases hs : stepFn ctx σ c ch with
      | error e => rfl
      | ok r =>
        obtain ⟨c₁, σ₁, ch₁, l⟩ := r
        simp only [Except.bind]
        exact ih (σ := σ₁) (c := c₁) (ch := ch₁) fun n σ' c' ch' ls hpre hn =>
          hnp (n + 1) σ' c' ch' (l :: ls) (.step hs hpre) (Nat.succ_le_succ hn)

theorem runInitConfig_ok_iff : runInitConfig_ok_iff_stmt := by
  intro ctx fuel s sf c ch chf hnp
  rw [runInitConfig_eq_execStmtLoop hnp]
  exact GoLean.GoCore.ExecutionStatement.run_ok_iff ctx fuel s sf c ch chf

theorem runInitConfig_panic_iff : runInitConfig_panic_iff_stmt := by
  intro ctx fuel s c ch t hnp
  rw [runInitConfig_eq_execStmtLoop hnp]
  exact GoLean.GoCore.ExecutionStatement.run_panic_iff ctx fuel s c ch t

theorem runInitConfig_deadlock_iff : runInitConfig_deadlock_iff_stmt := by
  intro ctx fuel s c ch hnp
  rw [runInitConfig_eq_execStmtLoop hnp]
  exact GoLean.GoCore.ExecutionStatement.run_deadlock_iff ctx fuel s c ch

theorem runInitConfig_fuelOut_iff : runInitConfig_fuelOut_iff_stmt := by
  intro ctx fuel s c ch hnp
  rw [runInitConfig_eq_execStmtLoop hnp]
  exact GoLean.GoCore.ExecutionStatement.run_fuelOut_iff ctx fuel s c ch

end InitLoop

/-! ## The `runPkgInitM` wrapper -/

theorem runPkgInitM_some : runPkgInitM_some_stmt := by
  intro ctx fuel s ch initF hf ha hr
  simp only [runPkgInitM, hf, ha, hr, bne_self_eq_false, Bool.or_self, Bool.false_eq_true,
    ↓reduceIte]
  cases runInitConfig ctx fuel s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch <;> rfl

theorem runPkgInitM_ok_iff : runPkgInitM_ok_iff_stmt := by
  intro ctx fuel s s₁ ch ch₁ initF hf ha hr
  rw [runPkgInitM_some hf ha hr]
  cases runInitConfig ctx fuel s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch <;>
    simp [Except.mapError]

/-! ## The `{}`-store forms are the instances at the empty store

The statements of `Equations.lean`'s `runProgramSetup_noInit`, `setup_lookup_arg`,
`setup_lookup_result`, `setup_resultLocs` and `setup_heap_size`, re-derived from the general forms
(controls — the pinned theorems themselves are unchanged). -/

example {fuel : Nat} {program : Program} {name : String} {args : Array GoValue} {choices : Choices}
    {func : Func} {env frameEnv : LocalEnv} {s₂ s₃ : Store} {resultLocs : List Loc}
    (hf : findFunctionIn? program.funcs ⟨name⟩ = some func) (harity : func.args.size = args.size)
    (hres : program.typeDefs.hasReservedPrefix = true) (hglob : program.globals = #[])
    (hinit : findFunctionIn? program.funcs pkgInitFuncId = none)
    (hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (hp : pinResultLocs frameEnv func.results.toList = .ok resultLocs) :
    runProgramSetupM fuel program name args choices
      = .ok (⟨program⟩, .exec func.body frameEnv (.frame [] [] [] [] .stop func.id), s₃, resultLocs, choices) := by
  have hinit' : findFunctionIn? (ProgramCtx.functions ⟨program⟩) pkgInitFuncId = none := hinit
  have hseed : seedGlobals ⟨program⟩ {} program.globals = .ok {} := by rw [hglob]; exact seedGlobals_nil
  exact runProgramSetup_init hf harity hres hseed (runPkgInitM_none hinit') hb ha hp

example {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    (hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (hdistinct : namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true)
    (i : Nat) (hi : i < func.args.size) :
    LocalEnv.lookup frameEnv func.args[i].id = some (.base ⟨i⟩) := by
  simpa [entrySlot] using setup_lookup_arg_from hb ha hdistinct i hi

example {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    (hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (hdistinct : namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true)
    (j : Nat) (hj : j < func.results.size) :
    LocalEnv.lookup frameEnv func.results[j].id = some (.base ⟨func.args.size + j⟩) := by
  simpa [entrySlot] using setup_lookup_result_from hb ha hdistinct j hj

example {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    {resultLocs : List Loc}
    (hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃))
    (hdistinct : namesDistinct ((func.args ++ func.results).toList.map (·.id)) = true)
    (hp : pinResultLocs frameEnv func.results.toList = .ok resultLocs) :
    resultLocs = (List.range func.results.size).map (fun j => Loc.base ⟨func.args.size + j⟩) := by
  simpa [entrySlot] using setup_resultLocs_from hb ha hdistinct hp

example {program : Program} {func : Func} {args : Array GoValue} {env frameEnv : LocalEnv} {s₂ s₃ : Store}
    (hb : bindParams ⟨program⟩ [] {} func.args.toList args.toList = .ok (env, s₂))
    (ha : allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃)) :
    s₃.heap.size = func.args.size + func.results.size := by
  simpa using setup_heap_size_from hb ha

/-! ## The SEEDED entry — S1–S6 (slice A, 2026-10-12) -/

/-- `Store.alloc` read back: the normalized value, the fresh address, the pushed cell. -/
theorem alloc_inv {ctx : ProgramCtx} {s s' : Store} {v : GoValue} {ty : Ty} {l : Loc}
    (h : Store.alloc ctx s v ty = .ok (l, s')) :
    ∃ v', normalizeValueForTy ctx ty v = .ok v' ∧ l = .base ⟨s.heap.size⟩
      ∧ s'.heap = s.heap.push (.value ty v') := by
  unfold Store.alloc at h
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
  obtain ⟨v', hv', h⟩ := h
  simp only [Store.allocCell, Prod.mk.injEq] at h
  obtain ⟨hl, hs⟩ := h
  exact ⟨v', hv', hl.symm, by rw [← hs]⟩

/-- `storeLoc` at a root holding a value cell, read back: the normalized value and the one-cell
overwrite (`storeLoc_root`'s converse). -/
theorem storeLoc_root_inv {ctx : ProgramCtx} {s s' : Store} {a : Addr} {ty : Ty} {old v : GoValue}
    (hl : Heap.lookup s.heap (.base a) = some (.value ty old))
    (h : storeLoc ctx s (.base a) v = .ok s') :
    ∃ w, normalizeValueForTy ctx ty v = .ok w
      ∧ s'.heap = s.heap.set a.id (.value ty w) (Heap.lookup_lt hl) := by
  have hi := Heap.lookup_lt hl
  have hcell : s.heap[a.id] = .value ty old := by
    obtain ⟨i⟩ := a
    simp only [Heap.lookup] at hl
    exact (Array.getElem?_eq_some_iff.mp hl).2
  unfold storeLoc Store.updateCell at h
  simp only [Loc.rootPath, hi, ↓reduceDIte, hcell, writeAt] at h
  cases hn : normalizeValueForTyTy (normalizeValueForTyAt ctx.types ctx.types.size) ty v with
  | error e => simp [hn, Bind.bind, Except.bind, Functor.map, Except.map] at h
  | ok w =>
      refine ⟨w, hn, ?_⟩
      simp only [hn, Bind.bind, Except.bind, Functor.map, Except.map] at h
      cases h
      rfl

/-- Phase 1 from position `k` over a store whose size is `b + k`: the size grows by the list's
length, the cells below are untouched, and cell `i` of the list sits at `b + k + i` as a value
cell of its declared type. -/
theorem seedAllocFrom_shape {ctx : ProgramCtx} :
    ∀ {cs : List SeedCell} {b k : Nat} {s s' : Store},
      seedAllocFrom ctx b s k cs = .ok s' → s.heap.size = b + k →
      s'.heap.size = b + k + cs.length
        ∧ (∀ j, j < s.heap.size → s'.heap[j]? = s.heap[j]?)
        ∧ (∀ i, (hi : i < cs.length) →
            ∃ z, Heap.lookup s'.heap (.base ⟨b + k + i⟩) = some (.value cs[i].typ z))
  | [], b, k, s, s', h, hsz => by
      simp only [seedAllocFrom, Except.ok.injEq] at h
      subst h
      exact ⟨by simp [hsz], fun _ _ => rfl, fun i hi => absurd hi (by simp)⟩
  | c :: rest, b, k, s, s', h, hsz => by
      unfold seedAllocFrom at h
      cases hd : defaultValue ctx c.typ with
      | error e => simp [hd, Bind.bind, Except.bind] at h
      | ok z =>
        cases ha : Store.alloc ctx s z c.typ with
        | error e => simp [hd, ha, Bind.bind, Except.bind] at h
        | ok ls =>
          obtain ⟨l, s₁⟩ := ls
          obtain ⟨z', _, hl, hs₁⟩ := alloc_inv ha
          have hlk : l = Loc.base ⟨b + k⟩ := by rw [hl, hsz]
          subst hlk
          simp only [hd, ha, Bind.bind, Except.bind, bne_self_eq_false, Bool.false_eq_true,
            ↓reduceIte] at h
          have hsz₁ : s₁.heap.size = b + (k + 1) := by rw [hs₁, Array.size_push, hsz, Nat.add_assoc]
          obtain ⟨h1, h2, h3⟩ := seedAllocFrom_shape h hsz₁
          refine ⟨by rw [h1]; simp [List.length_cons]; omega, ?_, ?_⟩
          · intro j hj
            rw [h2 j (by rw [hsz₁]; omega), hs₁, Array.getElem?_push]
            have : j ≠ s.heap.size := Nat.ne_of_lt hj
            simp [this]
          · intro i hi
            cases i with
            | zero =>
                refine ⟨z', ?_⟩
                have hj := h2 (b + k) (by rw [hsz₁]; omega)
                simp only [Nat.add_zero, Heap.lookup, List.getElem_cons_zero]
                rw [hj, hs₁, Array.getElem?_push, hsz]
                simp
            | succ i =>
                obtain ⟨z'', hz''⟩ := h3 i (by simpa using hi)
                refine ⟨z'', ?_⟩
                have : b + k + (i + 1) = b + (k + 1) + i := by omega
                rw [this]
                simpa using hz''

/-- Phase 2 from position `k`, every target cell a value cell of the list's declared type: the
size is unchanged, the cells below `b + k` are untouched, and cell `i` of the list holds its value
resolved and normalized at its declared type. -/
theorem seedStoreFrom_shape {ctx : ProgramCtx} :
    ∀ {cs : List SeedCell} {b k : Nat} {seed : Array SeedCell} {s s' : Store},
      seedStoreFrom ctx b seed s k cs = .ok s' →
      (∀ i, (hi : i < cs.length) →
        ∃ old, Heap.lookup s.heap (.base ⟨b + k + i⟩) = some (.value cs[i].typ old)) →
      s'.heap.size = s.heap.size
        ∧ (∀ j, j < b + k → s'.heap[j]? = s.heap[j]?)
        ∧ (∀ i, (hi : i < cs.length) → ∃ v w,
            resolveSeedValue ctx.types b seed cs[i].typ cs[i].value = .ok v
              ∧ normalizeValueForTy ctx cs[i].typ v = .ok w
              ∧ Heap.lookup s'.heap (.base ⟨b + k + i⟩) = some (.value cs[i].typ w))
  | [], b, k, seed, s, s', h, _ => by
      simp only [seedStoreFrom, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, fun _ _ => rfl, fun i hi => absurd hi (by simp)⟩
  | c :: rest, b, k, seed, s, s', h, hcells => by
      unfold seedStoreFrom at h
      cases hr : resolveSeedValue ctx.types b seed c.typ c.value with
      | error e => simp [hr, Except.mapError, Bind.bind, Except.bind] at h
      | ok v =>
        simp only [hr, Except.mapError, Bind.bind, Except.bind] at h
        obtain ⟨old, hold⟩ := hcells 0 (by simp)
        simp only [Nat.add_zero, List.getElem_cons_zero] at hold
        cases hst : storeLoc ctx s (.base ⟨b + k⟩) v with
        | error e => simp [hst] at h
        | ok s₁ =>
          simp only [hst] at h
          obtain ⟨w, hw, hs₁⟩ := storeLoc_root_inv hold hst
          have hlt := Heap.lookup_lt hold
          have hcells' : ∀ i, (hi : i < rest.length) →
              ∃ old, Heap.lookup s₁.heap (.base ⟨b + (k + 1) + i⟩) = some (.value rest[i].typ old) := by
            intro i hi
            obtain ⟨old', hold'⟩ := hcells (i + 1) (by simp; omega)
            refine ⟨old', ?_⟩
            have hne : (Loc.base ⟨b + k⟩ : Loc) ≠ .base ⟨b + (k + 1) + i⟩ := by
              intro hh
              simp only [Loc.base.injEq, Addr.mk.injEq] at hh
              omega
            rw [show Heap.lookup s₁.heap = Heap.lookup (s.heap.set (b + k) (.value c.typ w) hlt) by rw [hs₁],
              Heap.lookup_set_ne hne]
            have : b + (k + 1) + i = b + k + (i + 1) := by omega
            rw [this]
            simpa using hold'
          obtain ⟨h1, h2, h3⟩ := seedStoreFrom_shape h hcells'
          refine ⟨by rw [h1, hs₁, Array.size_set], ?_, ?_⟩
          · intro j hj
            rw [h2 j (by omega), hs₁, Array.getElem?_set_ne hlt (show b + k ≠ j by omega)]
          · intro i hi
            cases i with
            | zero =>
                refine ⟨v, w, by simpa using hr, by simpa using hw, ?_⟩
                have hj := h2 (b + k) (by omega)
                simp only [Nat.add_zero, List.getElem_cons_zero, Heap.lookup] at hj ⊢
                rw [hj, hs₁]
                simp
            | succ i =>
                obtain ⟨v', w', h1', h2', h3'⟩ := h3 i (by simpa using hi)
                refine ⟨v', w', by simpa using h1', by simpa using h2', ?_⟩
                have : b + k + (i + 1) = b + (k + 1) + i := by omega
                rw [this]
                simpa using h3'

/-- `seedCells` read back as its two phases and the slot list. -/
theorem seedCells_inv {ctx : ProgramCtx} {s₁ sS : Store} {seed : Array SeedCell} {locs : Array Loc}
    (h : seedCells ctx s₁ seed = .ok (sS, locs)) :
    ∃ sA, seedAllocFrom ctx s₁.heap.size s₁ 0 seed.toList = .ok sA
      ∧ seedStoreFrom ctx s₁.heap.size seed sA 0 seed.toList = .ok sS
      ∧ locs = seedLocs s₁.heap.size seed.size := by
  unfold seedCells at h
  cases hA : seedAllocFrom ctx s₁.heap.size s₁ 0 seed.toList with
  | error e => simp [hA, Bind.bind, Except.bind] at h
  | ok sA =>
    cases hS : seedStoreFrom ctx s₁.heap.size seed sA 0 seed.toList with
    | error e => simp [hA, hS, Bind.bind, Except.bind] at h
    | ok sS' =>
      simp only [hA, hS, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨sA, by first | rfl | exact hA, by first | rfl | exact hS, rfl⟩

/-- Phase 1 at position 0 lands cell `i` at `b + i` as a value cell (the premise phase 2 needs). -/
theorem seedAllocFrom_cells {ctx : ProgramCtx} {s₁ sA : Store} {seed : Array SeedCell}
    (hA : seedAllocFrom ctx s₁.heap.size s₁ 0 seed.toList = .ok sA) :
    ∀ i, (hi : i < seed.toList.length) →
      ∃ old, Heap.lookup sA.heap (.base ⟨s₁.heap.size + 0 + i⟩) = some (.value seed.toList[i].typ old) :=
  (seedAllocFrom_shape hA (by simp)).2.2

/-! ### S2, S3 -/

theorem seedCells_locs : seedCells_locs_stmt := by
  intro ctx s₁ seed sS locs h
  obtain ⟨_, _, _, hl⟩ := seedCells_inv h
  exact hl

theorem seedCells_heap_size : seedCells_heap_size_stmt := by
  intro ctx s₁ seed sS locs h
  obtain ⟨sA, hA, hS, _⟩ := seedCells_inv h
  have h1 := (seedAllocFrom_shape hA (by simp)).1
  have h2 := (seedStoreFrom_shape hS (seedAllocFrom_cells hA)).1
  rw [h2, h1]
  simp

theorem seedCells_frame : seedCells_frame_stmt := by
  intro ctx s₁ seed sS locs h j hj
  obtain ⟨sA, hA, hS, _⟩ := seedCells_inv h
  have h1 := (seedAllocFrom_shape hA (by simp)).2.1 j hj
  have h2 := (seedStoreFrom_shape hS (seedAllocFrom_cells hA)).2.1 j (by omega)
  rw [h2, h1]

theorem seedCells_cell : seedCells_cell_stmt := by
  intro ctx s₁ seed sS locs h k hk
  obtain ⟨sA, hA, hS, hl⟩ := seedCells_inv h
  refine ⟨?_, ?_⟩
  · subst hl
    simp [seedLocs, hk]
  · have hk' : k < seed.toList.length := by simpa using hk
    obtain ⟨v, w, h1, h2, h3⟩ := (seedStoreFrom_shape hS (seedAllocFrom_cells hA)).2.2 k hk'
    refine ⟨v, w, ?_, ?_, ?_⟩
    · simpa [Array.getElem_toList] using h1
    · simpa [Array.getElem_toList] using h2
    · simpa [Array.getElem_toList] using h3

/-! ### S5 — well-formedness -/

theorem seedAllocFrom_wf {ctx : ProgramCtx} :
    ∀ {cs : List SeedCell} {b k : Nat} {s s' : Store},
      StateWf ctx s → seedAllocFrom ctx b s k cs = .ok s' → StateWf ctx s'
  | [], _, _, s, s', hw, h => by
      simp only [seedAllocFrom, Except.ok.injEq] at h
      subst h
      exact hw
  | c :: rest, b, k, s, s', hw, h => by
      unfold seedAllocFrom at h
      cases hd : defaultValue ctx c.typ with
      | error e => simp [hd, Bind.bind, Except.bind] at h
      | ok z =>
        cases ha : Store.alloc ctx s z c.typ with
        | error e => simp [hd, ha, Bind.bind, Except.bind] at h
        | ok ls =>
          obtain ⟨l, s₁⟩ := ls
          have hz : GoValue.locSup z ≤ s.nextAddr := by
            rw [defaultValue_locSup hd]
            exact Nat.zero_le _
          have hw₁ := (alloc_wf hw hz ha).1
          simp only [hd, ha, Bind.bind, Except.bind] at h
          split at h
          · exact absurd h (by simp)
          · exact seedAllocFrom_wf hw₁ h

/-- A seed path keeps its root: the location it builds has the root of the location it starts from. -/
theorem seedPathLoc_rootBase :
    ∀ {types : TypeEnv} {l : Loc} {ty : Ty} {p : List SeedPathElem} {l' : Loc} {ty' : Ty},
      seedPathLoc types l ty p = .ok (l', ty') → Loc.rootBase l' = Loc.rootBase l
  | _, _, _, [], _, _, h => by
      simp only [seedPathLoc, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
  | types, l, ty, .field f :: rest, l', ty', h => by
      unfold seedPathLoc at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · rw [seedPathLoc_rootBase h]
          rfl
        · exact absurd h (by simp [stuck])
      · exact absurd h (by simp [stuck])
  | types, l, ty, .index i :: rest, l', ty', h => by
      unfold seedPathLoc at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · rw [seedPathLoc_rootBase h]
          rfl
        · exact absurd h (by simp [stuck])
      · exact absurd h (by simp [stuck])

theorem goValueListSup_le :
    ∀ {l : List GoValue} {bound : Nat}, (∀ v ∈ l, GoValue.locSup v ≤ bound) → goValueListSup l ≤ bound
  | [], _, _ => Nat.zero_le _
  | v :: vs, bound, h => by
      simp only [goValueListSup]
      exact Nat.max_le.mpr ⟨h v (List.mem_cons_self ..),
        goValueListSup_le (fun v' hv' => h v' (List.mem_cons_of_mem _ hv'))⟩

theorem goValueFieldsSup_le :
    ∀ {l : List (String × GoValue)} {bound : Nat},
      (∀ x ∈ l, GoValue.locSup x.2 ≤ bound) → goValueFieldsSup l ≤ bound
  | [], _, _ => Nat.zero_le _
  | (f, v) :: vs, bound, h => by
      simp only [goValueFieldsSup]
      exact Nat.max_le.mpr ⟨h (f, v) (List.mem_cons_self ..),
        goValueFieldsSup_le (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

/-- The declared-order reordering only picks members of the given list. -/
theorem seedStructOrder_mem :
    ∀ {name : TypeId} {decl : List FieldDef} {given ordered : List (String × GoValue)},
      seedStructOrder name decl given = .ok ordered → ∀ x ∈ ordered, x ∈ given
  | _, [], _, ordered, h => by
      simp only [seedStructOrder, Except.ok.injEq] at h
      subst h
      simp
  | name, d :: ds, given, ordered, h => by
      unfold seedStructOrder at h
      split at h
      · rename_i n v heq
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
        obtain ⟨rest, hrest, rfl⟩ := h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · have hm : (n, v) ∈ given.filter (·.1 == d.name) := by
            rw [heq]
            exact List.mem_singleton.mpr rfl
          have hf := List.mem_filter.mp hm
          have hn : n = d.name := by simpa using hf.2
          rw [← hn]
          exact hf.1
        · exact seedStructOrder_mem hrest x hx'
      · exact absurd h (by simp [stuck])
      · exact absurd h (by simp [stuck])

/-- The seed cell named by a successful `seedCellTy` exists. -/
theorem seedCellTy_lt {seed : Array SeedCell} {j : Nat} {ty : Ty}
    (h : seedCellTy seed j = .ok ty) : j < seed.size := by
  unfold seedCellTy at h
  split at h
  · rename_i heq
    exact (Array.getElem?_eq_some_iff.mp heq).1
  · exact absurd h (by simp [stuck])

mutual
/-- Every location in a resolved value lies inside the seed: `locSup ≤ b + n`. -/
theorem resolveSeedValue_locSup {types : TypeEnv} {b : Nat} {seed : Array SeedCell} :
    ∀ {ty : Ty} {sv : SeedValue} {v : GoValue},
      resolveSeedValue types b seed ty sv = .ok v → GoValue.locSup v ≤ b + seed.size
  | ty, .int n, v, h => by
      unfold resolveSeedValue at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · simp only [Except.ok.injEq] at h
          subst h
          exact Nat.zero_le _
        · exact absurd h (by simp [stuck])
      · exact absurd h (by simp [stuck])
  | ty, .bool x, v, h => by
      unfold resolveSeedValue at h
      split at h
      · exact absurd h (by simp)
      · simp only [Except.ok.injEq] at h
        subst h
        exact Nat.zero_le _
      · exact absurd h (by simp [stuck])
  | ty, .struct fields, v, h => by
      unfold resolveSeedValue at h
      split at h
      · exact absurd h (by simp)
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
        obtain ⟨given, hg, ordered, ho, rfl⟩ := h
        simp only [GoValue.locSup]
        exact goValueFieldsSup_le (fun x hx => resolveSeedFields_locSup hg x (seedStructOrder_mem ho x hx))
      · exact absurd h (by simp [stuck])
  | ty, .array elems, v, h => by
      unfold resolveSeedValue at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp [stuck])
        · rename_i x n e heq hne
          cases hvs : resolveSeedList types b seed e elems with
          | error err => simp [hvs, Except.map] at h
          | ok vs =>
              simp only [hvs, Except.map, Except.ok.injEq] at h
              subst h
              simp only [GoValue.locSup]
              exact goValueListSup_le (resolveSeedList_locSup hvs)
      · exact absurd h (by simp [stuck])
  | ty, .ref j path, v, h => by
      unfold resolveSeedValue at h
      split at h
      · exact absurd h (by simp)
      · unfold resolveSeedRef at h
        simp only [bind_eq_ok, pure_eq_ok] at h
        obtain ⟨root, hroot, ⟨loc, leaf⟩, hpath, hv⟩ := h
        have hj := seedCellTy_lt hroot
        split at hv
        · simp only [Except.ok.injEq] at hv
          subst hv
          simp only [GoValue.locSup, Loc.locSup, seedPathLoc_rootBase hpath, Loc.rootBase]
          omega
        · exact absurd hv (by simp [stuck])
      · exact absurd h (by simp [stuck])
  | ty, .nil, v, h => by
      unfold resolveSeedValue at h
      split at h
      · exact absurd h (by simp)
      · simp only [Except.ok.injEq] at h
        subst h
        exact Nat.zero_le _
      · exact absurd h (by simp [stuck])

theorem resolveSeedList_locSup {types : TypeEnv} {b : Nat} {seed : Array SeedCell} :
    ∀ {elem : Ty} {l : List SeedValue} {vs : List GoValue},
      resolveSeedList types b seed elem l = .ok vs → ∀ v ∈ vs, GoValue.locSup v ≤ b + seed.size
  | _, [], vs, h => by
      simp only [resolveSeedList, Except.ok.injEq] at h
      subst h
      simp
  | elem, sv :: rest, vs, h => by
      unfold resolveSeedList at h
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨w, hw, ws, hws, rfl⟩ := h
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact resolveSeedValue_locSup hw
      · exact resolveSeedList_locSup hws v hv'

theorem resolveSeedFields_locSup {types : TypeEnv} {b : Nat} {seed : Array SeedCell} :
    ∀ {name : TypeId} {decl : Array FieldDef} {l : List (String × SeedValue)}
      {ws : List (String × GoValue)},
      resolveSeedFields types b seed name decl l = .ok ws → ∀ x ∈ ws, GoValue.locSup x.2 ≤ b + seed.size
  | _, _, [], ws, h => by
      simp only [resolveSeedFields, Except.ok.injEq] at h
      subst h
      simp
  | name, decl, (f, sv) :: rest, ws, h => by
      unfold resolveSeedFields at h
      split at h
      · exact absurd h (by simp [stuck])
      · simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
        obtain ⟨w, hw, ws', hws, rfl⟩ := h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact resolveSeedValue_locSup hw
        · exact resolveSeedFields_locSup hws x hx'
end

theorem seedStoreFrom_wf {ctx : ProgramCtx} :
    ∀ {cs : List SeedCell} {b k : Nat} {seed : Array SeedCell} {s s' : Store},
      StateWf ctx s → b + seed.size ≤ s.heap.size → b + k + cs.length ≤ s.heap.size →
      seedStoreFrom ctx b seed s k cs = .ok s' → StateWf ctx s'
  | [], _, _, _, s, s', hw, _, _, h => by
      simp only [seedStoreFrom, Except.ok.injEq] at h
      subst h
      exact hw
  | c :: rest, b, k, seed, s, s', hw, hseed, hk, h => by
      unfold seedStoreFrom at h
      cases hr : resolveSeedValue ctx.types b seed c.typ c.value with
      | error e => simp [hr, Except.mapError, Bind.bind, Except.bind] at h
      | ok v =>
        simp only [hr, Except.mapError, Bind.bind, Except.bind] at h
        cases hst : storeLoc ctx s (.base ⟨b + k⟩) v with
        | error e => simp [hst] at h
        | ok s₁ =>
          simp only [hst] at h
          have hl : Loc.locSup (.base ⟨b + k⟩) ≤ s.nextAddr := by
            simp only [Loc.locSup, Loc.rootBase, Store.nextAddr]
            simp only [List.length_cons] at hk
            omega
          have hv : GoValue.locSup v ≤ s.nextAddr :=
            Nat.le_trans (resolveSeedValue_locSup hr) hseed
          obtain ⟨hw₁, hn₁⟩ := storeLoc_wf hw hl hv hst
          have hsz : s₁.heap.size = s.heap.size := hn₁
          exact seedStoreFrom_wf hw₁ (by rw [hsz]; exact hseed)
            (by rw [hsz]; simp only [List.length_cons] at hk; omega) h

theorem seedCells_wf : seedCells_wf_stmt := by
  intro ctx s₁ seed sS locs hw h
  obtain ⟨sA, hA, hS, _⟩ := seedCells_inv h
  have hwA := seedAllocFrom_wf hw hA
  have hsz := (seedAllocFrom_shape hA (by simp)).1
  exact seedStoreFrom_wf hwA (by rw [hsz]; simp) (by rw [hsz]; simp) hS

/-- A resolved argument is bounded by `b + n` when its scalar form is loc-free. -/
theorem resolveSeedArg_locSup {types : TypeEnv} {b : Nat} {seed : Array SeedCell} {ty : Ty}
    {a : SeedArg} {v : GoValue} (h : resolveSeedArg types b seed ty a = .ok v)
    (hs : ∀ w, a = .scalar w → GoValue.locSup w = 0) : GoValue.locSup v ≤ b + seed.size := by
  cases a with
  | scalar w =>
      simp only [resolveSeedArg] at h
      cases h
      rw [hs _ rfl]
      exact Nat.zero_le _
  | ref j path => exact resolveSeedValue_locSup h
  | nil => exact resolveSeedValue_locSup h

theorem resolveSeedArgsList_locSup {types : TypeEnv} {b : Nat} {seed : Array SeedCell} :
    ∀ {i : Nat} {ps : List Param} {as : List SeedArg} {vs : List GoValue},
      resolveSeedArgsList types b seed i ps as = .ok vs →
      (∀ w, SeedArg.scalar w ∈ as → GoValue.locSup w = 0) →
      goValueListSup vs ≤ b + seed.size
  | _, [], [], vs, h, _ => by
      simp only [resolveSeedArgsList, Except.ok.injEq] at h
      subst h
      exact Nat.zero_le _
  | i, p :: ps, a :: as, vs, h, hs => by
      unfold resolveSeedArgsList at h
      cases ha : resolveSeedArg types b seed p.typ a with
      | error e => simp [ha, Except.mapError, Bind.bind, Except.bind] at h
      | ok v =>
        simp only [ha, Except.mapError, Bind.bind, Except.bind] at h
        cases hws : resolveSeedArgsList types b seed (i + 1) ps as with
        | error e => simp [hws] at h
        | ok ws =>
          simp only [hws, pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [goValueListSup]
          exact Nat.max_le.mpr ⟨resolveSeedArg_locSup ha (fun w hw => hs w (hw ▸ List.mem_cons_self ..)),
            resolveSeedArgsList_locSup hws (fun w hw => hs w (List.mem_cons_of_mem _ hw))⟩
  | _, [], _ :: _, _, h, _ => by simp [resolveSeedArgsList, stuck] at h
  | _, _ :: _, [], _, h, _ => by simp [resolveSeedArgsList, stuck] at h

theorem runProgramSetupSeeded_wf : runProgramSetupSeeded_wf_stmt := by
  intro ctx s₁ sS seed slots params args vals env frameEnv s₂ s₃ results hw hs hcells hargs hb ha
  have hwS := seedCells_wf hw hcells
  have hsz := seedCells_heap_size hcells
  have hvals : goValueListSup vals.toList ≤ sS.nextAddr := by
    unfold resolveSeedArgs at hargs
    cases hl : resolveSeedArgsList ctx.types s₁.heap.size seed 0 params.toList args.toList with
    | error e => simp [hl, Except.map] at hargs
    | ok vs =>
      simp only [hl, Except.map, Except.ok.injEq] at hargs
      subst hargs
      simp only [Store.nextAddr, hsz]
      exact resolveSeedArgsList_locSup hl (fun w hw => hs w (by simpa using hw))
  obtain ⟨hw₂, _, henv⟩ := bindParams_wf hb hwS (by simp [LocalEnv.locSup]) hvals
  exact (allocDecls_wf ha hw₂ henv).1

/-! ### S1 -/

theorem runProgramSetupSeeded_init : runProgramSetupSeeded_init_stmt := by
  intro fuel program name seed args choices func s₀ s₁ choices₁ sS slots vals env frameEnv s₂ s₃
    resultLocs hf harity hres hseed hinit hcells hargs hb ha hp
  have hwf : StateWf ⟨program⟩ s₀ := seedGlobals_wf hseed
  simp [runProgramSetupSeededM, hf, harity, hres, hseed, hwf, hinit, hcells, ProgramCtx.types, hargs,
    hb, ha, hp, Bind.bind, Except.bind]

/-! ### S4 — the empty seed erases -/

theorem seedCells_nil (ctx : ProgramCtx) (s : Store) : seedCells ctx s #[] = .ok (s, #[]) := by
  simp [seedCells, seedAllocFrom, seedStoreFrom, seedLocs, Bind.bind, Except.bind, pure, Except.pure]

theorem resolveSeedArgsList_scalar {types : TypeEnv} {b : Nat} {seed : Array SeedCell} :
    ∀ (i : Nat) (ps : List Param) (vs : List GoValue), ps.length = vs.length →
      resolveSeedArgsList types b seed i ps (vs.map SeedArg.scalar) = .ok vs
  | _, [], [], _ => rfl
  | i, p :: ps, v :: vs, h => by
      simp only [List.map_cons, resolveSeedArgsList, resolveSeedArg, Except.mapError, Bind.bind,
        Except.bind]
      rw [resolveSeedArgsList_scalar (i + 1) ps vs (by simpa using h)]
      rfl
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

theorem resolveSeedArgs_scalar {types : TypeEnv} {b : Nat} {seed : Array SeedCell}
    (params : Array Param) (args : Array GoValue) (h : params.size = args.size) :
    resolveSeedArgs types b seed params (args.map SeedArg.scalar) = .ok args := by
  unfold resolveSeedArgs
  rw [Array.toList_map, resolveSeedArgsList_scalar 0 params.toList args.toList (by simpa using h)]
  simp [Except.map]

theorem runProgramSetupSeeded_empty : runProgramSetupSeeded_empty_stmt := by
  intro fuel program name args choices
  unfold runProgramSetupSeededM runProgramSetupM
  simp only [Array.size_map]
  cases hf : findFunctionIn? program.funcs ⟨name⟩ with
  | none => rfl
  | some func =>
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    by_cases harity : (func.args.size != args.size) = true
    · simp only [if_pos harity]
      rfl
    · have heq : func.args.size = args.size := by simpa using harity
      simp only [if_neg harity]
      by_cases hres : program.typeDefs.hasReservedPrefix = true
      · simp only [if_pos hres]
        cases hseed : seedGlobals ⟨program⟩ {} program.globals with
        | error e => rfl
        | ok s₀ =>
          dsimp only
          by_cases hwf : StateWf ⟨program⟩ s₀
          · simp only [if_pos hwf]
            cases hinit : runPkgInitM ⟨program⟩ fuel s₀ choices with
            | error e => rfl
            | ok r =>
              obtain ⟨s₁, choices₁⟩ := r
              dsimp only
              rw [seedCells_nil]
              dsimp only
              rw [resolveSeedArgs_scalar func.args args heq]
              dsimp only
              cases hb : bindParams ⟨program⟩ [] s₁ func.args.toList args.toList with
              | error e => rfl
              | ok r₂ =>
                obtain ⟨env, s₂⟩ := r₂
                dsimp only
                cases ha : allocDecls ⟨program⟩ env s₂ func.results.toList with
                | error e => rfl
                | ok r₃ =>
                  obtain ⟨frameEnv, s₃⟩ := r₃
                  dsimp only
                  cases hp : pinResultLocs frameEnv func.results.toList with
                  | error e => rfl
                  | ok resultLocs => rfl
          · simp only [if_neg hwf]
            rfl
      · simp only [if_neg hres]
        rfl

/-! ### S6 -/

theorem runProgramSeededM_eq : runProgramSeededM_eq_stmt := fun _ _ _ _ _ _ => rfl

theorem runProgramSeededM_empty : runProgramSeededM_empty_stmt := by
  intro fuel program name args choices
  unfold runProgramSeededM runProgramM
  rw [runProgramSetupSeeded_empty]
  cases hs : runProgramSetupM fuel program name args choices with
  | error e => simp [Functor.map, Except.map, Bind.bind, Except.bind]
  | ok r =>
    obtain ⟨pctx, c₀, s₃, resultLocs, choices₁⟩ := r
    simp only [Functor.map, Except.map, Bind.bind, Except.bind]
    cases hr : runConfig pctx fuel s₃ c₀ choices₁ with
    | error e => simp
    | ok r' =>
      obtain ⟨sF, _⟩ := r'
      cases hl : loadMany pctx sF resultLocs with
      | error e => simp [hl]
      | ok values => simp [hl, loadMany, pure, Except.pure]

end GoLean.GoCore.SetupSound
