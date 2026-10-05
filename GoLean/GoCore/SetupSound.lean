import GoLean.GoCore.SetupStatement
import GoLean.GoCore.Equations

/-!
# Proofs for the setup equations G-R1–G-R3 (`SetupStatement.lean`)

[AGENT worker, lane `core/setup-equations-1005`] 2026-10-05; authority and the request as in
`SetupStatement.lean`'s header. Every `<name>_stmt` of G-R1–G-R3 is discharged here as
`theorem <name> : <name>_stmt`, the statement unchanged. G-R4 is NOT proved here (its statement is
out for the logic team's review).

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

end GoLean.GoCore.SetupSound
