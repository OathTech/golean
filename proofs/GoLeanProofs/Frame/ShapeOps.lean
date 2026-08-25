import GoLeanProofs.Frame.ShapeSim
import GoLeanProofs.Frame.StepSim

/-!
# The S-copies of the mutating operation lemmas (C2a, instrument part 2)

Each lemma below mirrors its weak sibling in `HeapOps`/`PanicFrame`/
`Ops2`/`StmtOps`/`ChanSync` VERBATIM, with the strengthened relation
threaded through the strengthened primitives (`FrameSimS.setBase`,
`FrameSimS.alloc_snd`). Non-mutating lemmas (loads, plans, value-level
facts, `dynamicDispatch?`, `applyStrictOp` — zero heap writes) are
consumed as-is via `toFrameSim`. RECORDED SCAFFOLD: these copies
duplicate the weak proofs' spines; the retirement condition is in
`ShapeSim.lean`'s module docstring.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

namespace FrameSimS

/-- Forwarders: weak facts through the parent (dot-notation reach). -/
theorem lookup_some (h : FrameSimS ρ na₀ na fr σ σF) {l : Loc} {c : HeapCell}
    (hl : Heap.lookup σ.heap l = some c) :
    Heap.lookup σF.heap (renameLoc ρ l) = some (renameCell ρ c) :=
  h.toFrameSim.lookup_some hl

theorem lookup_none_base (h : FrameSimS ρ na₀ na fr σ σF) {a : Nat}
    (hl : Heap.lookup σ.heap (.base ⟨a⟩) = none) :
    Heap.lookup σF.heap (.base ⟨ρ a⟩) = none :=
  h.toFrameSim.lookup_none_base hl

theorem alloc_fst (h : FrameSimS ρ na₀ na fr σ σF) (v : GoValue)
    (ty : Option Ty) :
    (ExecState.alloc σF (renameValue ρ v) ty).1 =
      renameLoc ρ (ExecState.alloc σ v ty).1 :=
  h.toFrameSim.alloc_fst v ty

end FrameSimS

/-! ## storeLoc / storeMany (HeapOps 302/434 copies) -/

theorem storeLoc_simS (hS : FrameSimS ρ na₀ na fr σ σF) :
    ∀ (l : Loc) (v : GoValue),
      ExSim (FrameSimS ρ na₀ na fr)
        (storeLoc σ l v) (storeLoc σF (renameLoc ρ l) (renameValue ρ v)) := by
  intro l
  induction l generalizing σ σF hS with
  | base a =>
      intro v
      obtain ⟨i⟩ := a
      simp only [storeLoc, renameLoc]
      cases hl : Heap.lookup σ.heap (.base ⟨i⟩) with
      | some cell =>
          have hf := hS.lookup_some (l := .base ⟨i⟩) hl
          rw [renameLoc] at hf
          rw [hf]
          dsimp only
          rw [show (renameCell ρ cell).declaredTy = cell.declaredTy from rfl]
          cases hd : cell.declaredTy with
          | some ty =>
              dsimp only
              refine ExSim.bind (normalizeValueForTy_sim hS.types_eq ty v) ?_
              intro v' vF' hv'
              subst hv'
              exact ExSim.ok (hS.setBase i { declaredTy := some ty, value := v' })
          | none =>
              dsimp only
              refine ExSim.bind (coerceStoredValue_sim ρ cell.value v) ?_
              intro v' vF' hv'
              subst hv'
              exact ExSim.ok (hS.setBase i { declaredTy := none, value := v' })
      | none =>
          have hfn := hS.lookup_none_base (a := i) hl
          rw [hfn]
          dsimp only
          exact ExSim.ok (hS.setBase i { value := v })
  | field b tid fname ihb =>
      intro v
      simp only [storeLoc, renameLoc]
      refine ExSim.bind (loadLoc_sim hS.toFrameSim b) ?_
      intro bv bvF hbv
      subst hbv
      cases bv
      case struct actual fields =>
        simp only [renameValue]
        rw [structTagCompatible_congr hS.types_eq]
        by_cases hne :
            (actual != tid && !structTagCompatible σ actual tid) = true
        · rw [if_pos hne]
          exact ExSim.stuck'
        · rw [if_neg hne, if_neg hne]
          simp only [pure_bind]
          refine ExSim.bind (structFieldsSet_sim ρ fields fname v) ?_
          intro upd updF hupdF
          subst hupdF
          exact ihb hS (.struct actual upd)
      all_goals exact ExSim.stuck'
  | index b i ihb =>
      intro v
      simp only [storeLoc, renameLoc]
      refine ExSim.bind (loadLoc_sim hS.toFrameSim b) ?_
      intro bv bvF hbv
      subst hbv
      cases bv
      case array vs =>
        simp only [renameValue]
        refine ExSim.bind (arraySet_sim' ρ vs i v) ?_
        intro upd updF hupdF
        subst hupdF
        exact ihb hS (.array upd)
      all_goals exact ExSim.stuck'

theorem storeMany_simS :
    ∀ (locs : List Loc) (vs : List GoValue) {σ σF : ExecState},
      FrameSimS ρ na₀ na fr σ σF →
      ExSim (FrameSimS ρ na₀ na fr)
        (storeMany σ locs vs)
        (storeMany σF (locs.map (renameLoc ρ)) (renameValueList ρ vs)) := by
  intro locs
  induction locs with
  | nil =>
      intro vs σ σF hS
      cases vs with
      | nil => exact ExSim.ok hS
      | cons v vs' => exact ExSim.stuck'
  | cons l ls ih =>
      intro vs σ σF hS
      cases vs with
      | nil => exact ExSim.stuck'
      | cons v vs' =>
          simp only [storeMany, List.map_cons, renameValueList]
          refine ExSim.bind (storeLoc_simS hS l v) ?_
          intro σ' σF' hS'
          exact ih vs' hS'

/-! ## allocDecls / bindParams (HeapOps 482/508 copies) -/

theorem allocDecls_simS :
    ∀ (ps : List Param) (env : LocalEnv) {σ σF : ExecState},
      FrameSimS ρ na₀ na fr σ σF →
      ExSim (fun (r : LocalEnv × ExecState) (rF : LocalEnv × ExecState) =>
          rF.1 = renameEnv ρ r.1 ∧ FrameSimS ρ na₀ na fr r.2 rF.2)
        (allocDecls env σ ps)
        (allocDecls (renameEnv ρ env) σF ps) := by
  intro ps
  induction ps with
  | nil =>
      intro env σ σF hS
      exact ExSim.ok ⟨rfl, hS⟩
  | cons p rest ih =>
      intro env σ σF hS
      simp only [allocDecls]
      refine ExSim.bind (defaultValue_sim (ρ := ρ) hS.types_eq p.typ) ?_
      intro d dF hdF
      subst hdF
      have halloc : ExecState.alloc σF (renameValue ρ d) p.typ
          = (renameLoc ρ (ExecState.alloc σ d p.typ).1,
              (ExecState.alloc σF (renameValue ρ d) p.typ).2) := by
        rw [← hS.alloc_fst d p.typ]
      rw [halloc]
      rw [← localEnv_declare_ren]
      exact ih _ (hS.alloc_snd d p.typ)

theorem bindParams_simS :
    ∀ (ps : List Param) (vs : List GoValue) (env : LocalEnv) {σ σF : ExecState},
      FrameSimS ρ na₀ na fr σ σF →
      ExSim (fun (r : LocalEnv × ExecState) (rF : LocalEnv × ExecState) =>
          rF.1 = renameEnv ρ r.1 ∧ FrameSimS ρ na₀ na fr r.2 rF.2)
        (bindParams env σ ps vs)
        (bindParams (renameEnv ρ env) σF ps (renameValueList ρ vs)) := by
  intro ps
  induction ps with
  | nil =>
      intro vs env σ σF hS
      cases vs with
      | nil => exact ExSim.ok ⟨rfl, hS⟩
      | cons v vs' => exact ExSim.stuck'
  | cons p rest ih =>
      intro vs env σ σF hS
      cases vs with
      | nil => exact ExSim.stuck'
      | cons v vs' =>
          simp only [bindParams, renameValueList]
          refine ExSim.bind (normalizeValueForTy_sim hS.types_eq p.typ v) ?_
          intro v' vF' hv'
          subst hv'
          have halloc : ExecState.alloc σF (renameValue ρ v') p.typ
              = (renameLoc ρ (ExecState.alloc σ v' p.typ).1,
                  (ExecState.alloc σF (renameValue ρ v') p.typ).2) := by
            rw [← hS.alloc_fst v' p.typ]
          rw [halloc]
          rw [← localEnv_declare_ren]
          exact ih vs' _ (hS.alloc_snd v' p.typ)

/-! ## Frame entry (HeapOps 767 / PanicFrame 499/528 copies) -/

theorem enterFrame_simS (hS : FrameSimS ρ na₀ na fr σ σF)
    (fid : FuncId) (args : List GoValue) :
    ExSim (fun (r rF : Func × LocalEnv × List Loc × ExecState) =>
        rF.1 = r.1 ∧ rF.2.1 = renameEnv ρ r.2.1
          ∧ rF.2.2.1 = r.2.2.1.map (renameLoc ρ)
          ∧ FrameSimS ρ na₀ na fr r.2.2.2 rF.2.2.2
          ∧ renameStmt ρ r.1.body = r.1.body)
      (enterFrame σ fid args)
      (enterFrame σF fid (renameValueList ρ args)) := by
  simp only [enterFrame]
  rw [hS.funcs_eq]
  cases hfind : findFunctionIn? σ.functions fid with
  | none => exact ExSim.stuck'
  | some func =>
      simp only [pure_bind]
      rw [renameValueList_length]
      by_cases har : (func.args.size != args.length) = true
      · rw [if_pos har]
        exact ExSim.stuck'
      · simp only [if_neg har]
        have hddargs : (renameValueList ρ args).toArray
            = (renameValueList ρ (args.toArray).toList).toArray := by
          rw [List.toList_toArray]
        rw [hddargs]
        refine ExSim.bind (dynamicDispatch?_sim' hS.toFrameSim func args.toArray) ?_
        intro o oF hoF
        obtain ⟨hoF, hbodies⟩ := hoF
        subst hoF
        cases o with
        | none =>
            have hnil : (renameEnv ρ [] : LocalEnv) = [] := rfl
            rw [← hnil]
            refine ExSim.bind (bindParams_simS func.args.toList args [] hS) ?_
            intro r1 r1F hr1
            obtain ⟨env1, σ1⟩ := r1
            obtain ⟨env1F, σ1F⟩ := r1F
            obtain ⟨henv1, hS1⟩ := hr1
            dsimp only at henv1 hS1 ⊢
            subst henv1
            refine ExSim.bind (allocDecls_simS func.results.toList env1 hS1) ?_
            intro r2 r2F hr2
            obtain ⟨env2, σ2⟩ := r2
            obtain ⟨env2F, σ2F⟩ := r2F
            obtain ⟨henv2, hS2⟩ := hr2
            dsimp only at henv2 hS2 ⊢
            subst henv2
            refine ExSim.bind (pinResultLocs_sim env2 func.results.toList) ?_
            intro ls lsF hls
            subst hls
            exact ExSim.ok ⟨rfl, rfl, rfl, hS2,
              hS.bodies_inv func (findFunctionIn?_mem hfind)⟩
        | some hit =>
            obtain ⟨tf, ta⟩ := hit
            dsimp only [Option.map_some]
            simp only [List.toList_toArray, renameValueList_length]
            by_cases har2 : (tf.args.size != ta.toList.length) = true
            · rw [if_pos har2]
              exact ExSim.stuck'
            · simp only [if_neg har2]
              have hnil : (renameEnv ρ [] : LocalEnv) = [] := rfl
              rw [← hnil]
              refine ExSim.bind (bindParams_simS tf.args.toList ta.toList [] hS) ?_
              intro r1 r1F hr1
              obtain ⟨env1, σ1⟩ := r1
              obtain ⟨env1F, σ1F⟩ := r1F
              obtain ⟨henv1, hS1⟩ := hr1
              dsimp only at henv1 hS1 ⊢
              subst henv1
              refine ExSim.bind (allocDecls_simS tf.results.toList env1 hS1) ?_
              intro r2 r2F hr2
              obtain ⟨env2, σ2⟩ := r2
              obtain ⟨env2F, σ2F⟩ := r2F
              obtain ⟨henv2, hS2⟩ := hr2
              dsimp only at henv2 hS2 ⊢
              subst henv2
              refine ExSim.bind (pinResultLocs_sim env2 tf.results.toList) ?_
              intro ls lsF hls
              subst hls
              exact ExSim.ok ⟨rfl, rfl, rfl, hS2, hbodies tf ta rfl⟩

/-- The strengthened triple relation (`TripSim` at S). -/
abbrev TripSimS (ρ : Nat → Nat) (na₀ na : Nat) (fr : Heap) :
    Config × ExecState × Choices → Config × ExecState × Choices → Prop :=
  fun r rF => rF.1 = renameConfig ρ r.1
    ∧ FrameSimS ρ na₀ na fr r.2.1 rF.2.1 ∧ rF.2.2 = r.2.2

theorem enterFrameStep_simS (hS : FrameSimS ρ na₀ na fr σ σF)
    (fid : FuncId) (args : List GoValue)
    (mk mkF : Func → LocalEnv → List Loc → Config) (k : Cont) (ch : Choices)
    (hmk : ∀ f e ls, renameStmt ρ f.body = f.body →
        mkF f (renameEnv ρ e) (ls.map (renameLoc ρ))
          = renameConfig ρ (mk f e ls)) :
    ExSim (TripSimS ρ na₀ na fr)
      (enterFrameStep σ fid args mk k ch)
      (enterFrameStep σF fid (renameValueList ρ args) mkF
        (renameCont ρ k) ch) := by
  simp only [enterFrameStep]
  cases henter : enterFrame σ fid args with
  | ok r =>
      obtain ⟨f, e, ls, σ'⟩ := r
      obtain ⟨rF, hrF, hrel⟩ := (enterFrame_simS hS fid args).ok_inv henter
      obtain ⟨fF, eF, lsF, σF'⟩ := rF
      obtain ⟨hf, he, hls, hS', hbody⟩ := hrel
      dsimp only at hf he hls hS' hbody
      subst hf he hls
      rw [hrF]
      exact ExSim.ok ⟨hmk _ _ _ hbody, hS', rfl⟩
  | error err =>
      cases err
      case panic m =>
          rw [(enterFrame_simS hS fid args).panic_inv henter]
          refine ExSim.ok ⟨?_, hS, rfl⟩
          simp [renameConfig, renameChain, renameEntry, runtimeErrorValue_ren]
      all_goals exact ExSim.skip fun m h => GoError.noConfusion h

theorem enterFrameDeferPanicking_simS (hS : FrameSimS ρ na₀ na fr σ σF)
    (fid : FuncId) (args : List GoValue)
    (mk mkF : Func → LocalEnv → Config) (chain : List PanicEntry)
    (krest : Cont) (ch : Choices)
    (hmk : ∀ f e, renameStmt ρ f.body = f.body →
        mkF f (renameEnv ρ e) = renameConfig ρ (mk f e)) :
    ExSim (TripSimS ρ na₀ na fr)
      (enterFrameDeferPanicking σ fid args mk chain krest ch)
      (enterFrameDeferPanicking σF fid (renameValueList ρ args) mkF
        (renameChain ρ chain) (renameCont ρ krest) ch) := by
  simp only [enterFrameDeferPanicking]
  cases henter : enterFrame σ fid args with
  | ok r =>
      obtain ⟨f, e, ls, σ'⟩ := r
      obtain ⟨rF, hrF, hrel⟩ := (enterFrame_simS hS fid args).ok_inv henter
      obtain ⟨fF, eF, lsF, σF'⟩ := rF
      obtain ⟨hf, he, hls, hS', hbody⟩ := hrel
      dsimp only at hf he hls hS' hbody
      subst hf he hls
      rw [hrF]
      exact ExSim.ok ⟨by rw [hmk _ _ hbody], hS', rfl⟩
  | error err =>
      cases err
      case panic m =>
          rw [(enterFrame_simS hS fid args).panic_inv henter]
          refine ExSim.ok ⟨?_, hS, rfl⟩
          simp [renameConfig, renameChain, renameEntry, runtimeErrorValue_ren,
            List.map_append]
      all_goals exact ExSim.skip fun m h => GoError.noConfusion h

/-! ## Iteration-variable binding (PanicFrame 434 copy) -/

theorem bindIterVars_simS (hS : FrameSimS ρ na₀ na fr σ σF)
    (env : LocalEnv) (keyVar valVar : Option String) (kt vt : Ty)
    (key value : GoValue) :
    ExSim (fun (r rF : LocalEnv × ExecState) =>
        rF.1 = renameEnv ρ r.1 ∧ FrameSimS ρ na₀ na fr r.2 rF.2)
      (bindIterVars env σ keyVar valVar kt vt key value)
      (bindIterVars (renameEnv ρ env) σF keyVar valVar kt vt
        (renameValue ρ key) (renameValue ρ value)) := by
  have hval : ∀ (env1 : LocalEnv) {σ1 σ1F : ExecState},
      FrameSimS ρ na₀ na fr σ1 σ1F →
      ExSim (fun (r rF : LocalEnv × ExecState) =>
          rF.1 = renameEnv ρ r.1 ∧ FrameSimS ρ na₀ na fr r.2 rF.2)
        (match valVar with
          | some name => do
            let vv ← normalizeValueForTy σ1 vt value
            pure (env1.declare name (σ1.alloc vv (some vt)).fst,
              (σ1.alloc vv (some vt)).snd)
          | none => pure (env1, σ1))
        (match valVar with
          | some name => do
            let vv ← normalizeValueForTy σ1F vt (renameValue ρ value)
            pure ((renameEnv ρ env1).declare name
                (σ1F.alloc vv (some vt)).fst,
              (σ1F.alloc vv (some vt)).snd)
          | none => pure (renameEnv ρ env1, σ1F)) := by
    intro env1 σ1 σ1F hS1
    cases valVar with
    | none => exact ExSim.ok ⟨rfl, hS1⟩
    | some vn =>
        refine ExSim.bind (normalizeValueForTy_sim hS1.types_eq vt value) ?_
        intro vv vvF hvvF
        subst hvvF
        have halloc : ExecState.alloc σ1F (renameValue ρ vv) (some vt)
            = (renameLoc ρ (ExecState.alloc σ1 vv (some vt)).1,
                (ExecState.alloc σ1F (renameValue ρ vv) (some vt)).2) := by
          rw [← hS1.alloc_fst vv (some vt)]
        rw [halloc]
        rw [← localEnv_declare_ren]
        exact ExSim.ok ⟨rfl, hS1.alloc_snd vv (some vt)⟩
  simp only [bindIterVars]
  cases keyVar with
  | none =>
      simp only [pure_bind]
      exact hval env hS
  | some kn =>
      refine ExSim.bind (normalizeValueForTy_sim hS.types_eq kt key) ?_
      intro kv kvF hkvF
      subst hkvF
      have halloc : ExecState.alloc σF (renameValue ρ kv) (some kt)
          = (renameLoc ρ (ExecState.alloc σ kv (some kt)).1,
              (ExecState.alloc σF (renameValue ρ kv) (some kt)).2) := by
        rw [← hS.alloc_fst kv (some kt)]
      rw [halloc]
      simp only [pure_bind]
      rw [← localEnv_declare_ren]
      exact hval _ (hS.alloc_snd kv (some kt))

end GoLean.Frame
