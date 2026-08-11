import GoLeanProofs.LangDM

/-!
# The wpDM law ports (channel-logic slice 3 — design note
`docs/2026-08-11_channel-resource-tier.md` §3)

The sequential `Laws/*` family restated on the MEDIATED DM carrier —
the law surface the dsp flagship walk needs (S2 note §6 obstacle 2):
block/init, `makeChan` (P-CL1-6 closes), `new`, call-frame
entry/exit, the strict spine (`toInterface`/`typeAssert`/`add`/
`deref`), and the assign/`assignMany` tgtOp spine, plus the pure
control/eval/go-statement glue. Port pattern: same machine-equation
content as `Laws/Control`/`Laws/Eval`/`Laws/Init`/`Laws/StmtOps`/
`Laws/Call`, over the DM cores; the mediated rules are refuted by
`stepDM_shape_cases` (all shapes here are sequential — the four side
conditions are `rfl`). Cores added here: `wpDM_pure_step` (generic
`step_det`-based pure lift), `wpDM_alloc_step` and
`wpDM_alloc_store_step` (the allocating shapes — both HAND OUT the
allocation's `metaToken`, which the sequential family discards: the
flagship's reply-leg meta tie needs the signal channel's token,
design note §2(a)).

Laws are registered `@[go_walk_law]` where their side conditions are
mechanical, so `go_walk` drives DM walks exactly as it drives
sequential ones (the table discriminates on the `PoolCfgDM.mk`
wrapper; no interference with the sequential entries).

Same-commit witness: `Specs/SeqWalkDM.lean` — the kitchen-sink
single-thread DM walk (call → block → init → makeChan → new →
toInterface → typeAssert → assignMany → return) discharging every
named port on a concrete program, D1-BOTH.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open Iris.ProgramLogic.Language.Notation
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open Iris.BI

namespace GoLean.Iris

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-! ## The cores -/

/-- **Generic pure deterministic step on the DM carrier** (the
`wp_pure_det` port): a state-independent step from a choice-free
sequential-shape configuration. Determinism comes from the generic
`step_det`; each instance supplies only its `Step` constructor and the
four shape side conditions (all `rfl` at sequential shapes). -/
theorem wpDM_pure_step {c₀ c₁ : Config}
    (hcf : c₀.choiceFree)
    (hsp : spawnPlan c₀ = none) (hsc : spawnedCont c₀ = none)
    (hblk : isBlockedConfig c₀ = false) (hpos : chanSelApplyPos c₀ = false)
    (hstep : ∀ σ : ExecState, Step c₀ σ c₁ σ) :
    (|={E}[E]▷=> £ 1 -∗ WP (PoolCfgDM.mk c₁) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk c₀) @ s ; E {{ Φ }} :=
  wpDM_pure_det hsp hsc hblk hpos hstep
    (fun σ c₂ σ₂ h => by
      obtain ⟨h1, h2⟩ := step_det hcf (hstep σ) h
      exact ⟨h1.symm, h2.symm⟩)

/-- **One-cell allocating step on the DM carrier**: `c₀` allocates ONE
fresh cell and continues Addr-parametrically. The continuation receives
the points-to AND the allocation's `metaToken` (design note §2(a) — the
sequential family discards it; the meta tie must not). -/
theorem wpDM_alloc_step {cell : HeapCell} {c₀ : Config} (c₁ : Addr → Config)
    (hnv : ToVal.toVal (PoolCfgDM.mk c₀) = (none : Option Unit))
    (hsp : spawnPlan c₀ = none) (hsc : spawnedCont c₀ = none)
    (hblk : isBlockedConfig c₀ = false) (hpos : chanSelApplyPos c₀ = false)
    (hred : ∀ σ₁ : ExecState, σ₁.functions = GoCoreGS.prog GF →
      σ₁.methods = GoCoreGS.methods GF → σ₁.types = GoCoreGS.types GF →
      Step c₀ σ₁ (c₁ ⟨σ₁.nextAddr⟩)
        { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) cell,
                  nextAddr := σ₁.nextAddr + 1 } ∧
      (∀ c' s', Step c₀ σ₁ c' s' →
        c' = c₁ ⟨σ₁.nextAddr⟩ ∧
        s' = { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) cell,
                       nextAddr := σ₁.nextAddr + 1 })) :
    iprop(∀ pa : Addr, pa.id ↦ cell ∗ metaToken pa.id ⊤ -∗
        WP (PoolCfgDM.mk (c₁ pa)) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk c₀) @ s ; E {{ Φ }} := by
  iintro Hcont
  iapply wp_lift_step (h := hnv)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], _, _, [],
        GoPrimStepDM.step (.lift (.lift (hred σ₁ hfns hmeths htypes).1))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    rcases stepDM_shape_cases hblk hpos st with hse | ⟨kk, hkk, -⟩
    · cases hse with
      | lift sq =>
        obtain ⟨rfl, rfl⟩ := (hred σ₁ hfns hmeths htypes).2 _ _ sq
        imod (genHeap_alloc (v := cell) hwf.fresh_get?) $$ Hσ
          with ⟨Hσ, Hpt, Htok⟩
        imod Hclose
        imodintro
        simp only [List.map_nil, Algebra.BigOpL.bigOpL_nil]
        isplitl [Hσ]
        · isplitl [Hσ]
          · iapply (genHeapInterp_eqv
              (fun kk => (heapToMap_set_base σ₁.heap ⟨σ₁.nextAddr⟩ cell
                kk).symm)) $$ Hσ
          · ipureintro
            exact ⟨hfns, hmeths, htypes, hwf.alloc⟩
        · isplitl [Hpt Htok Hcont]
          · iapply Hcont $$ %(⟨σ₁.nextAddr⟩ : Addr) [$Hpt $Htok]
          · itrivial
      | spawn hsp' _ =>
        rw [hsp] at hsp'
        cases hsp'
    · rw [hkk] at hsc
      simp [spawnedCont] at hsc

/-- **Allocate-and-store step on the DM carrier** (`wp_alloc_store_step`'s
port + the `metaToken` handover): ONE step allocates `fcell` fresh and
rewrites the owned target cell to `newcell fa` (which may name the fresh
address). The `makeChan`/`newValue`/make-family engine. -/
theorem wpDM_alloc_store_step {a : Addr} {fcell oldcell : HeapCell}
    (newcell : Addr → HeapCell) {c₀ : Config} (c₁ : Config)
    (hnv : ToVal.toVal (PoolCfgDM.mk c₀) = (none : Option Unit))
    (hsp : spawnPlan c₀ = none) (hsc : spawnedCont c₀ = none)
    (hblk : isBlockedConfig c₀ = false) (hpos : chanSelApplyPos c₀ = false)
    (hred : ∀ σ₁ : ExecState, σ₁.functions = GoCoreGS.prog GF →
      σ₁.methods = GoCoreGS.methods GF → σ₁.types = GoCoreGS.types GF →
      Heap.lookup σ₁.heap (.base a) = some oldcell →
      a.id ≠ σ₁.nextAddr →
      Step c₀ σ₁ c₁
        { σ₁ with
          heap := Heap.set (Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) fcell)
                    (.base a) (newcell ⟨σ₁.nextAddr⟩),
          nextAddr := σ₁.nextAddr + 1 } ∧
      (∀ c' s', Step c₀ σ₁ c' s' →
        c' = c₁ ∧
        s' = { σ₁ with
               heap := Heap.set (Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) fcell)
                         (.base a) (newcell ⟨σ₁.nextAddr⟩),
               nextAddr := σ₁.nextAddr + 1 })) :
    a.id ↦ oldcell
      ∗ iprop(∀ fa : Addr, fa.id ↦ fcell ∗ a.id ↦ newcell fa
          ∗ metaToken fa.id ⊤ -∗
          WP (PoolCfgDM.mk c₁) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk c₀) @ s ; E {{ Φ }} := by
  iintro ⟨Hpt, Hcont⟩
  iapply wp_lift_step (h := hnv)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some oldcell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some oldcell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hne : a.id ≠ σ₁.nextAddr := by
    have := hwf.lt_of_lookup hlook; omega
  have hfresh : get? (heapToMap σ₁.heap) σ₁.nextAddr = none := hwf.fresh_get?
  have hlook' : Heap.lookup (Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) fcell)
      (.base a) = some oldcell := by
    have := heap_lookup_set_base_ne (h := σ₁.heap) (n := a.id)
      (b := (⟨σ₁.nextAddr⟩ : Addr)) (c := fcell) (fun he => hne he.symm)
    simpa using this.trans (by simpa using hlook)
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], _, _, [],
        GoPrimStepDM.step (.lift (.lift
          (hred σ₁ hfns hmeths htypes hlook hne).1))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    rcases stepDM_shape_cases hblk hpos st with hse | ⟨kk, hkk, -⟩
    · cases hse with
      | lift sq =>
        obtain ⟨rfl, rfl⟩ := (hred σ₁ hfns hmeths htypes hlook hne).2 _ _ sq
        imod (genHeap_alloc (v := fcell) hfresh) $$ Hσ with ⟨Hσ, Hf, Htok⟩
        imod (genHeap_update (v₂ := newcell ⟨σ₁.nextAddr⟩)) $$ [$Hσ $Hpt]
          with ⟨Hσ, Hpt⟩
        imod Hclose
        imodintro
        simp only [List.map_nil, Algebra.BigOpL.bigOpL_nil]
        isplitl [Hσ]
        · isplitl [Hσ]
          · iapply (genHeapInterp_eqv
              (fun kk => (heapToMap_set_base₂ σ₁.heap ⟨σ₁.nextAddr⟩ a fcell
                (newcell ⟨σ₁.nextAddr⟩) kk).symm)) $$ Hσ
          · ipureintro
            exact ⟨hfns, hmeths, htypes,
              (HeapWf.alloc (c := fcell) hwf).set_existing hlook'⟩
        · isplitl [Hf Hpt Htok Hcont]
          · iapply Hcont $$ %(⟨σ₁.nextAddr⟩ : Addr) [$Hf $Hpt $Htok]
          · itrivial
      | spawn hsp' _ =>
        rw [hsp] at hsp'
        cases hsp'
    · rw [hkk] at hsc
      simp [spawnedCont] at hsc

/-! ## Control glue (`Laws/Control` ports) -/

@[go_walk_law]
theorem wpDM_seqn {ss : Array Stmt} {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.next (seqCont ss.toList env k))) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.exec (.seqn ss) env k)) @ s ; E {{ Φ }} :=
  wpDM_pure_step (by simp [Config.choiceFree, stmtPlan]) rfl rfl rfl rfl
    (fun _ => Step.seqn)

@[go_walk_law]
theorem wpDM_seq_next {t : Stmt} {rest : List Stmt} {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.exec t env (.seq rest env k))) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.next (.seq (t :: rest) env k))) @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.seqNext)

@[go_walk_law]
theorem wpDM_seq_done {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗ WP (PoolCfgDM.mk (.next k)) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.next (.seq [] env k))) @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.seqDone)

@[go_walk_law]
theorem wpDM_block_nil {ss : Array Stmt} {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.next (.seq ss.toList env.pushScope k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.exec (.block #[] ss) env k)) @ s ; E {{ Φ }} :=
  wpDM_pure_step (by simp [Config.choiceFree, stmtPlan]) rfl rfl rfl rfl
    (fun _ => Step.block rfl)

@[go_walk_law]
theorem wpDM_frame_fall {tenv : LocalEnv} {k : Cont} {w : Bool} :
    (|={E}[E]▷=> £ 1 -∗ WP (PoolCfgDM.mk (.next k)) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.next (.frame [] tenv [] [] k w))) @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.frameFall)

@[go_walk_law]
theorem wpDM_return {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗ WP (PoolCfgDM.mk (.returning k)) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.exec .returnStmt env k)) @ s ; E {{ Φ }} :=
  wpDM_pure_step (by simp [Config.choiceFree, stmtPlan]) rfl rfl rfl rfl
    (fun _ => Step.returnStmt)

@[go_walk_law]
theorem wpDM_seq_return {rest : List Stmt} {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗ WP (PoolCfgDM.mk (.returning k)) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.returning (.seq rest env k))) @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.seqReturn)

/-- The empty-splice absorber on the DM carrier (`wp_seqCont_nil`'s
port). -/
theorem wpDM_seqCont_nil {env : LocalEnv} {k : Cont} :
    (WP (PoolCfgDM.mk (.next k)) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.next (seqCont [] env k))) @ s ; E {{ Φ }} := by
  iintro H
  have hcases : seqCont [] env k = k ∨ seqCont [] env k = .seq [] env k := by
    cases k
    case seq rest env' k' =>
      by_cases henv : env' = env
      · subst henv
        exact Or.inl (by simp [seqCont])
      · exact Or.inr (by simp [seqCont, henv])
    all_goals exact Or.inr rfl
  rcases hcases with heq | heq <;> rw [heq]
  · iexact H
  · iapply wpDM_seq_done
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro -
    iexact H

/-! ## Pure expression steps (`Laws/Eval` ports) -/

@[go_walk_law]
theorem wpDM_eval_intLit {n : Int} {kind : IntKind} {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.retV (.int (kind.normalize n) kind) k))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.evalE (.intLit n kind) env k)) @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.evalIntLit)

@[go_walk_law]
theorem wpDM_eval_boolLit {b : Bool} {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.retV (.bool b) k)) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.evalE (.boolLit b) env k)) @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.evalBoolLit)

@[go_walk_law]
theorem wpDM_eval_ref {id : String} {loc : Loc} {env : LocalEnv} {k : Cont}
    (hres : LocalEnv.lookup env id = some loc) :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.retV (.addr loc) k)) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.evalE (.ref id) env k)) @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.evalRef hres)

@[go_walk_law]
theorem wpDM_eval_strict {e : Expr} {op : StrictOp} {e₁ : Expr}
    {rest : List Expr} {env : LocalEnv} {k : Cont}
    (hplan : strictPlan e = some (op, e₁ :: rest)) :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE e₁ env (.strictK op [] rest env k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.evalE e env k)) @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.evalStrict hplan)

@[go_walk_law]
theorem wpDM_strict_shift {op : StrictOp} {done : List GoValue} {v : GoValue}
    {e : Expr} {rest : List Expr} {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE e env (.strictK op (v :: done) rest env k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.retV v (.strictK op done (e :: rest) env k)))
        @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.strictShift)

@[go_walk_law]
theorem wpDM_strict_apply_pure {op : StrictOp} {done : List GoValue}
    {v out : GoValue} {env : LocalEnv} {k : Cont}
    (happly : ∀ σ : ExecState,
      applyStrictOp σ op (v :: done).reverse = .ok (out, σ)) :
    (|={E}[E]▷=> £ 1 -∗ WP (PoolCfgDM.mk (.retV out k)) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.retV v (.strictK op done [] env k))) @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun σ => Step.strictApply (happly σ))

/-- Types-pinned strict apply (`wp_strict_apply_pin`'s port — the
`toInterface` boxing / `typeAssert` unboxing / named-type conversion
class). Resource-free on both sides. -/
@[go_walk_law]
theorem wpDM_strict_apply_pin {op : StrictOp} {done : List GoValue}
    {v out : GoValue} {env : LocalEnv} {k : Cont}
    (happly : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      applyStrictOp σ op (v :: done).reverse = .ok (out, σ)) :
    (WP (PoolCfgDM.mk (.retV out k)) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.retV v (.strictK op done [] env k)))
          @ s ; E {{ Φ }} := by
  iintro H
  iapply (wpDM_det_step_keep (P := iprop(emp))
    (c₁ := Config.retV out k) (hnv := rfl) (hsp := rfl) (hsc := rfl)
    (hblk := rfl) (hpos := rfl)
    (hred := by
      intro σ₁ _hfns _hmeths htypes
      iintro ⟨Hσ, -⟩
      imodintro
      ipureintro
      refine ⟨Step.strictApply (happly σ₁ htypes), ?_⟩
      intro c' s' hst
      obtain ⟨h1, h2⟩ :=
        step_det (by trivial) (Step.strictApply (happly σ₁ htypes)) hst
      exact ⟨h1.symm, h2.symm⟩))
  isplitl []
  · itrivial
  · iintro -
    iexact H

/-- Nullary types-pinned strict form (`struct{}{}` and friends). -/
@[go_walk_law]
theorem wpDM_eval_strict_nullary_pin {e : Expr} {op : StrictOp}
    {v : GoValue} {env : LocalEnv} {k : Cont}
    (hplan : strictPlan e = some (op, []))
    (happly : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      applyStrictOp σ op [] = .ok (v, σ)) :
    (WP (PoolCfgDM.mk (.retV v k)) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.evalE e env k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wpDM_det_step_keep (P := iprop(emp))
    (c₁ := Config.retV v k) (hnv := rfl) (hsp := rfl) (hsc := rfl)
    (hblk := rfl) (hpos := rfl)
    (hred := by
      intro σ₁ _hfns _hmeths htypes
      iintro ⟨Hσ, -⟩
      imodintro
      ipureintro
      refine ⟨Step.evalStrictNullary hplan (happly σ₁ htypes), ?_⟩
      intro c' s' hst
      obtain ⟨h1, h2⟩ := step_det (by simp [Config.choiceFree])
        (Step.evalStrictNullary hplan (happly σ₁ htypes)) hst
      exact ⟨h1.symm, h2.symm⟩))
  isplitl []
  · itrivial
  · iintro -
    iexact H

/-- State-READING strict apply at an arbitrary fraction
(`wp_strict_apply_read`'s port, generalized to `↦{dq}` — a persisted
`↦□` handle cell serves the dsp child's `*c$cap` derefs).

Deliberately NOT `@[go_walk_law]`-registered (slice-3 finding, design
note §6 commit-4 log): its `happly` can be discharged by `rfl` at any
PURE strict apply while its owned cell stays meta-undetermined, so the
walk's `iframe` would grab an arbitrary context points-to as the
"read" cell — a spurious resource capture (observed renaming a live
hypothesis in the dsp child walk). Genuine reads supply it explicitly. -/
theorem wpDM_strict_apply_read {op : StrictOp} {done : List GoValue}
    {v out : GoValue} {a : Addr} {dq : DFrac} {cell : HeapCell}
    {env : LocalEnv} {k : Cont}
    (happly : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base a) = some cell →
      applyStrictOp σ op (v :: done).reverse = .ok (out, σ)) :
    a.id ↦{dq} cell
      ∗ (a.id ↦{dq} cell -∗ WP (PoolCfgDM.mk (.retV out k)) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.retV v (.strictK op done [] env k)))
          @ s ; E {{ Φ }} := by
  iapply wpDM_det_step_keep (P := iprop(a.id ↦{dq} cell))
    (c₁ := Config.retV out k) (hnv := rfl) (hsp := rfl) (hsc := rfl)
    (hblk := rfl) (hpos := rfl)
  intro σ₁ _hfns _hmeths htypes
  iintro ⟨Hσ, Hpt⟩
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id = some cell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a) = some cell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  imodintro
  ipureintro
  refine ⟨Step.strictApply (happly σ₁ htypes hlook), ?_⟩
  intro c' s' hst
  obtain ⟨h1, h2⟩ :=
    step_det (by trivial) (Step.strictApply (happly σ₁ htypes hlook)) hst
  exact ⟨h1.symm, h2.symm⟩

/-! ## The assign / tgtOp / rhs / store spine (`Laws/Eval` ports) -/

@[go_walk_law]
theorem wpDM_assign_start {lhs : Assignee} {rhs e : Expr} {sh : TargetShape}
    {ops : List Expr} {env : LocalEnv} {k : Cont}
    (hplan : targetPlan lhs = some (sh, e :: ops)) :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE e env (.tgtOpK sh [] ops [] [] .vals [rhs] []
        (.seqn #[]) env k))) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.exec (.assign lhs rhs) env k)) @ s ; E {{ Φ }} :=
  wpDM_pure_step (by simp [Config.choiceFree, stmtPlan]) rfl rfl rfl rfl
    (fun _ => Step.assignFirst hplan)

@[go_walk_law]
theorem wpDM_assign_many_start {left : Array Assignee} {right : Array Expr}
    {sh : TargetShape} {e : Expr} {ops : List Expr}
    {targets : List (TargetShape × List Expr)} {env : LocalEnv} {k : Cont}
    (hsz : left.size = right.size)
    (hplan : targetsPlan left.toList = some ((sh, e :: ops) :: targets)) :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE e env (.tgtOpK sh [] ops [] targets .vals
        right.toList [] (.seqn #[]) env k))) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.exec (.assignMany left right) env k))
        @ s ; E {{ Φ }} :=
  wpDM_pure_step (by simp [Config.choiceFree, stmtPlan]) rfl rfl rfl rfl
    (fun _ => Step.assignManyFirst hsz hplan)

@[go_walk_law]
theorem wpDM_tgtop_shift {sh : TargetShape} {ops : List GoValue} {v : GoValue}
    {e : Expr} {pending : List Expr} {refs : List TargetRef}
    {targets : List (TargetShape × List Expr)} {rop : RhsOp} {rhs : List Expr}
    {vals : List GoValue} {body : Stmt} {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE e env (.tgtOpK sh (v :: ops) pending refs targets
        rop rhs vals body env k))) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.retV v (.tgtOpK sh ops (e :: pending) refs targets
        rop rhs vals body env k))) @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.tgtOpShift)

@[go_walk_law]
theorem wpDM_tgtop_next {sh : TargetShape} {ops : List GoValue} {v : GoValue}
    {r : TargetRef} {sh' : TargetShape} {e : Expr} {ops' : List Expr}
    {targets : List (TargetShape × List Expr)} {refs : List TargetRef}
    {rop : RhsOp} {rhs : List Expr} {vals : List GoValue} {body : Stmt}
    {env : LocalEnv} {k : Cont}
    (hcomp : completeTargetRef sh (v :: ops).reverse = some r) :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE e env (.tgtOpK sh' [] ops' (refs ++ [r]) targets
        rop rhs vals body env k))) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.retV v (.tgtOpK sh ops [] refs ((sh', e :: ops') :: targets)
        rop rhs vals body env k))) @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.tgtOpNext hcomp)

@[go_walk_law]
theorem wpDM_tgtop_rhs {sh : TargetShape} {ops : List GoValue} {v : GoValue}
    {r : TargetRef} {refs : List TargetRef} {rop : RhsOp} {e : Expr}
    {rest : List Expr} {vals : List GoValue} {body : Stmt}
    {env : LocalEnv} {k : Cont}
    (hcomp : completeTargetRef sh (v :: ops).reverse = some r) :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE e env (.rhsK rop (refs ++ [r]) [] rest body env k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.retV v (.tgtOpK sh ops [] refs [] rop (e :: rest) vals
        body env k))) @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.tgtOpRhs hcomp)

@[go_walk_law]
theorem wpDM_tgtop_stores {sh : TargetShape} {ops : List GoValue} {v : GoValue}
    {r : TargetRef} {refs : List TargetRef} {rop : RhsOp}
    {vals : List GoValue} {body : Stmt} {env : LocalEnv} {k : Cont}
    (hcomp : completeTargetRef sh (v :: ops).reverse = some r) :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.next (.storeK (refs ++ [r]) vals body env k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.retV v (.tgtOpK sh ops [] refs [] rop [] vals
        body env k))) @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.tgtOpStores hcomp)

@[go_walk_law]
theorem wpDM_rhs_shift {rop : RhsOp} {refs : List TargetRef}
    {done : List GoValue} {v : GoValue} {e : Expr} {rest : List Expr}
    {body : Stmt} {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE e env (.rhsK rop refs (v :: done) rest body env k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.retV v (.rhsK rop refs done (e :: rest) body env k)))
        @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.rhsShift)

@[go_walk_law]
theorem wpDM_rhs_stores_vals {refs : List TargetRef} {done : List GoValue}
    {v : GoValue} {body : Stmt} {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.next (.storeK refs (v :: done).reverse body env k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.retV v (.rhsK .vals refs done [] body env k)))
        @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.rhsStores rfl)

@[go_walk_law]
theorem wpDM_stores_done {body : Stmt} {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.exec body env k)) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.next (.storeK [] [] body env k))) @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.storeDone)

/-- The statement-form phase-2 drain at an arbitrary continuation
(`wp_stores_done_nil`'s port). -/
theorem wpDM_stores_done_nil {env : LocalEnv} {k : Cont} :
    (WP (PoolCfgDM.mk (.next k)) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.next (.storeK [] [] (.seqn #[]) env k)))
        @ s ; E {{ Φ }} := by
  iintro H
  iapply wpDM_stores_done
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  iapply wpDM_seqn
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  simp only [Array.toList_empty]
  iapply wpDM_seqCont_nil
  iexact H

/-- The spine store step (`wp_store_target`'s port): one `storeK`
phase-2 store through a completed reference, the target's cell owned. -/
theorem wpDM_store_target {a : Addr} {r : TargetRef} {v : GoValue}
    {oldcell newcell : HeapCell} {rs : List TargetRef} {vals : List GoValue}
    {body : Stmt} {env : LocalEnv} {k : Cont}
    (hstore : ∀ σ₁ : ExecState, σ₁.types = GoCoreGS.types GF →
      Heap.lookup σ₁.heap (.base a) = some oldcell →
      storeTarget σ₁ r v
        = .ok { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) :
    a.id ↦ oldcell
      ∗ (a.id ↦ newcell -∗
          WP (PoolCfgDM.mk (.next (.storeK rs vals body env k)))
            @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.next (.storeK (r :: rs) (v :: vals) body env k)))
          @ s ; E {{ Φ }} := by
  iapply wpDM_store_step (hnv := rfl) (hsp := rfl) (hsc := rfl)
    (hblk := rfl) (hpos := rfl)
  intro σ₁ hfns hmeths htypes hlook
  refine ⟨Step.storeStep (hstore σ₁ htypes hlook), ?_⟩
  intro c' s' hst'
  cases hst' with
  | storeStep h' =>
    rw [hstore σ₁ htypes hlook] at h'
    injection h' with h'
    exact ⟨rfl, h'.symm⟩
  | storeStepPanic h' =>
    rw [hstore σ₁ htypes hlook] at h'
    cases h'

/-- The bare-chain instance (`wp_assign_store_loc`'s port). -/
theorem wpDM_assign_store_loc {a : Addr} {tgt : Loc} {v : GoValue}
    {oldcell newcell : HeapCell} {rs : List TargetRef} {vals : List GoValue}
    {body : Stmt} {env : LocalEnv} {k : Cont}
    (hstore : ∀ σ₁ : ExecState, σ₁.types = GoCoreGS.types GF →
      Heap.lookup σ₁.heap (.base a) = some oldcell →
      storeLoc σ₁ tgt v
        = .ok { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) :
    a.id ↦ oldcell
      ∗ (a.id ↦ newcell -∗
          WP (PoolCfgDM.mk (.next (.storeK rs vals body env k)))
            @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.next (.storeK (.chain (.addr tgt) [] [] :: rs)
            (v :: vals) body env k))) @ s ; E {{ Φ }} :=
  wpDM_store_target (fun σ₁ htypes hlook => by
    simp [storeTarget, resolveChain, valueAsLoc, Bind.bind, Except.bind,
      hstore σ₁ htypes hlook])

/-! ## Wide statement ops (`Laws/StmtOps` ports) -/

@[go_walk_law]
theorem wpDM_stmt_op_first {stmt : Stmt} {op : StmtOp} {nt : Nat} {e : Expr}
    {rest : List Expr} {env : LocalEnv} {k : Cont}
    (hplan : stmtPlan stmt = some (op, nt, e :: rest)) :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE e env (.stmtOpK op nt [] rest env k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.exec stmt env k)) @ s ; E {{ Φ }} :=
  wpDM_pure_step (by simp [Config.choiceFree, hplan]) rfl rfl rfl rfl
    (fun _ => Step.stmtOpFirst hplan)

@[go_walk_law]
theorem wpDM_stmt_op_shift_target {op : StmtOp} {nt : Nat}
    {done : List GoValue} {v : GoValue} {loc : Loc} {e : Expr}
    {rest : List Expr} {env : LocalEnv} {k : Cont}
    (hnt : done.length < nt) (hloc : valueAsLoc v = .ok loc) :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE e env (.stmtOpK op nt (v :: done) rest env k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.retV v (.stmtOpK op nt done (e :: rest) env k)))
        @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl
    (fun _ => Step.stmtOpShiftTarget hnt hloc)

@[go_walk_law]
theorem wpDM_stmt_op_shift_plain {op : StmtOp} {nt : Nat}
    {done : List GoValue} {v : GoValue} {e : Expr} {rest : List Expr}
    {env : LocalEnv} {k : Cont}
    (hnt : nt ≤ done.length) :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE e env (.stmtOpK op nt (v :: done) rest env k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.retV v (.stmtOpK op nt done (e :: rest) env k)))
        @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.stmtOpShiftPlain hnt)

/-- The allocate-and-store apply step (`wp_stmt_op_apply_alloc_store`'s
port; the apply position is not choice-free, so determinism is by
inversion — `happly`'s `∀ ch` closes the stream quantifier). -/
theorem wpDM_stmt_op_apply_alloc_store {op : StmtOp} {nt : Nat}
    {done : List GoValue} {v : GoValue} {a : Addr} {fcell oldcell : HeapCell}
    (newcell : Addr → HeapCell) {env : LocalEnv} {k : Cont}
    (happly : ∀ (σ : ExecState) (ch : Choices), σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base a) = some oldcell →
      a.id ≠ σ.nextAddr →
      applyStmtOp σ ch op nt (v :: done).reverse
        = .ok ({ σ with
                 heap := Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) fcell)
                           (.base a) (newcell ⟨σ.nextAddr⟩),
                 nextAddr := σ.nextAddr + 1 }, ch)) :
    a.id ↦ oldcell
      ∗ iprop(∀ fa : Addr, fa.id ↦ fcell ∗ a.id ↦ newcell fa
          ∗ metaToken fa.id ⊤ -∗
          WP (PoolCfgDM.mk (.next k)) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.retV v (.stmtOpK op nt done [] env k)))
          @ s ; E {{ Φ }} := by
  iapply (wpDM_alloc_store_step newcell (c₁ := Config.next k) (hnv := rfl)
    (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl))
  intro σ₁ _hfns _hmeths htypes hlook hne
  refine ⟨Step.stmtOpApply (ch := []) (happly σ₁ [] htypes hlook hne), ?_⟩
  intro c' s' hst
  cases hst with
  | @stmtOpApply _ _ _ _ _ _ _ _ ch _ hap =>
    rw [happly σ₁ ch htypes hlook hne] at hap
    injection hap with hap
    exact ⟨rfl, (Prod.mk.inj hap).1.symm⟩
  | @stmtOpApplyPanic _ _ _ _ _ _ _ _ ch hap =>
    rw [happly σ₁ ch htypes hlook hne] at hap
    exact absurd hap (by simp)

/-- **`ch = make(chan T)` as ONE step** — P-CL1-6 CLOSES (no sequential
counterpart ever existed; built from `applyStmtOpCore`'s `.makeChan`
arm): allocate the empty untyped OPEN channel data cell (`⟨none,
.chanData #[] 0 false⟩` — exactly the shape `chanInv`/`chanInvP` pin)
and store a channel handle naming it into the target. The
continuation's `metaToken fa.id ⊤` is the reply-leg tie's raw material
(design note §2(a)). The capacityless form (`cap = 0`, the dsp shape);
the capacity-carrying form lands with a buffered-channel consumer. -/
theorem wpDM_make_chan {a : Addr} {oldcell : HeapCell}
    (newcell : Addr → HeapCell) {env : LocalEnv} {k : Cont}
    (hstore : ∀ (σ : ExecState) (fa : Addr), σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base a) = some oldcell →
      storeLoc σ (.base a) (.chan ⟨some (.base fa)⟩)
        = .ok { σ with heap := Heap.set σ.heap (.base a) (newcell fa) }) :
    a.id ↦ oldcell
      ∗ iprop(∀ fa : Addr, fa.id ↦ (⟨none, .chanData #[] 0 false⟩ : HeapCell)
          ∗ a.id ↦ newcell fa ∗ metaToken fa.id ⊤ -∗
          WP (PoolCfgDM.mk (.next k)) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.retV (.addr (.base a))
            (.stmtOpK (.makeChan false) 1 [] [] env k))) @ s ; E {{ Φ }} := by
  iapply (wpDM_stmt_op_apply_alloc_store (done := [])
    (fcell := (⟨none, .chanData #[] 0 false⟩ : HeapCell)) newcell)
  intro σ ch htypes hlook hne
  have hlook' : Heap.lookup
      (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨none, .chanData #[] 0 false⟩)
      (.base a) = some oldcell := by
    have := heap_lookup_set_base_ne (h := σ.heap) (n := a.id)
      (b := (⟨σ.nextAddr⟩ : Addr))
      (c := (⟨none, .chanData #[] 0 false⟩ : HeapCell)) (fun he => hne he.symm)
    simpa using this.trans (by simpa using hlook)
  have hst := hstore { σ with
      heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨none, .chanData #[] 0 false⟩,
      nextAddr := σ.nextAddr + 1 } ⟨σ.nextAddr⟩ htypes hlook'
  simp [applyStmtOp, valueAsLoc, ExecState.alloc, ExecState.freshLoc, hst,
    Bind.bind, Except.bind, applyStmtOpCore]

/-- **`p = new(v)` as ONE step** (`wp_new_value`'s port). -/
theorem wpDM_new_value {typ : Option Ty} {a : Addr} {oldcell : HeapCell}
    (newcell : Addr → HeapCell) {v : GoValue} {env : LocalEnv} {k : Cont}
    (hstore : ∀ (σ : ExecState) (fa : Addr), σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base a) = some oldcell →
      storeLoc σ (.base a) (.addr (.base fa))
        = .ok { σ with heap := Heap.set σ.heap (.base a) (newcell fa) }) :
    a.id ↦ oldcell
      ∗ iprop(∀ fa : Addr, fa.id ↦ (⟨typ, v⟩ : HeapCell)
          ∗ a.id ↦ newcell fa ∗ metaToken fa.id ⊤ -∗
          WP (PoolCfgDM.mk (.next k)) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.retV v
            (.stmtOpK (.newValue typ) 1 [.addr (.base a)] [] env k)))
          @ s ; E {{ Φ }} := by
  iapply (wpDM_stmt_op_apply_alloc_store (done := [.addr (.base a)])
    (fcell := (⟨typ, v⟩ : HeapCell)) newcell)
  intro σ ch htypes hlook hne
  have hlook' : Heap.lookup
      (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨typ, v⟩) (.base a)
      = some oldcell := by
    have := heap_lookup_set_base_ne (h := σ.heap) (n := a.id)
      (b := (⟨σ.nextAddr⟩ : Addr)) (c := (⟨typ, v⟩ : HeapCell))
      (fun he => hne he.symm)
    simpa using this.trans (by simpa using hlook)
  have hst := hstore { σ with
      heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨typ, v⟩,
      nextAddr := σ.nextAddr + 1 } ⟨σ.nextAddr⟩ htypes hlook'
  simp [applyStmtOp, valueAsLoc, ExecState.alloc, ExecState.freshLoc, hst,
    Bind.bind, Except.bind, applyStmtOpCore]

/-! ## Declarations (`Laws/Init` port) -/

/-- `var x T` inside a sequence (`wp_init`'s port; the continuation
additionally receives the allocation's `metaToken`). -/
theorem wpDM_init {pid : String} {pty : Ty} {v : GoValue} {rest : List Stmt}
    {env : LocalEnv} {k : Cont}
    (hdef : ∀ σ₁ : ExecState, σ₁.types = GoCoreGS.types GF →
      defaultValue σ₁ pty = .ok v) :
    iprop(∀ pa : Addr, pa.id ↦ (⟨some pty, v⟩ : HeapCell) ∗ metaToken pa.id ⊤ -∗
        WP (PoolCfgDM.mk (.next (.seq rest (env.declare pid (.base pa)) k)))
          @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.exec (.initialization ⟨pid, pty⟩) env
            (.seq rest env k))) @ s ; E {{ Φ }} := by
  iapply (wpDM_alloc_step
    (cell := (⟨some pty, v⟩ : HeapCell))
    (c₁ := fun pa => Config.next (.seq rest (env.declare pid (.base pa)) k))
    (hnv := rfl) (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl))
  intro σ₁ _hfns _hmeths htypes
  have hstep : Step (.exec (.initialization ⟨pid, pty⟩) env (.seq rest env k)) σ₁
      (.next (.seq rest (env.declare pid (.base ⟨σ₁.nextAddr⟩)) k))
      { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some pty, v⟩,
                nextAddr := σ₁.nextAddr + 1 } :=
    Step.initialization (hdef σ₁ htypes) (ExecState.alloc_eq σ₁ v (some pty))
  refine ⟨hstep, ?_⟩
  intro c' s' hst
  cases hst with
  | stmtOpFirst hplan => simp [stmtPlan] at hplan
  | stmtOpNullary hplan _ => simp [stmtPlan] at hplan
  | chanStFirst hplan => simp [chanPlan] at hplan
  | syncStFirst hplan => simp [syncPlan] at hplan
  | initialization hd ha =>
    rw [hdef σ₁ htypes] at hd
    injection hd with hv
    rw [← hv, ExecState.alloc_eq] at ha
    injection ha with hloc hst'
    rw [← hloc, ← hst']
    exact ⟨rfl, rfl⟩

/-! ## Calls (`Laws/Call` ports — the nullary/1-result shape the dsp
frames take) -/

/-- Frame entry, nullary argument / single result (`wp_call_enter_ret1`'s
port; the result cell's `metaToken` handed along). -/
theorem wpDM_call_enter_ret1 {targets : Array Assignee} {fid : FuncId}
    {func : Func} {rid : String} {rty : Ty} {dv : GoValue}
    {plans : List (TargetShape × List Expr)} {env : LocalEnv} {k : Cont}
    (hplan : targetsPlan targets.toList = some plans)
    (hfind : findFunctionIn? (GoCoreGS.prog GF) fid = some func)
    (hargs : func.args = #[])
    (hres : func.results = #[⟨rid, rty⟩])
    (hnodisp : ∀ σ : ExecState, σ.methods = GoCoreGS.methods GF →
      dynamicDispatch? σ func #[] = .ok none)
    (hdef : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      defaultValue σ rty = .ok dv) :
    iprop(∀ ra : Addr, ra.id ↦ (⟨some rty, dv⟩ : HeapCell) ∗ metaToken ra.id ⊤ -∗
        WP (PoolCfgDM.mk (.exec func.body [[(rid, Loc.base ra)]]
              (.frame plans env [Loc.base ra] [] k func.wrapper)))
          @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.exec (.call targets fid #[]) env k))
          @ s ; E {{ Φ }} := by
  have henter : ∀ σ₁ : ExecState, σ₁.functions = GoCoreGS.prog GF →
      σ₁.methods = GoCoreGS.methods GF → σ₁.types = GoCoreGS.types GF →
      enterFrame σ₁ fid []
        = .ok (func, [[(rid, Loc.base ⟨σ₁.nextAddr⟩)]], [Loc.base ⟨σ₁.nextAddr⟩],
            { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩) ⟨some rty, dv⟩,
                      nextAddr := σ₁.nextAddr + 1 }) := by
    intro σ₁ hfns hmeths htypes
    unfold enterFrame
    rw [hfns, hfind]
    simp [hargs, hres, Bind.bind, Except.bind, hnodisp σ₁ hmeths, bindParams,
      hdef σ₁ htypes, ExecState.alloc, ExecState.freshLoc, allocDecls,
      pinResultLocs, LocalEnv.declare, LocalEnv.lookup, Scope.lookup]
    exact hfns
  iapply (wpDM_alloc_step
    (cell := (⟨some rty, dv⟩ : HeapCell))
    (c₁ := fun ra => Config.exec func.body [[(rid, Loc.base ra)]]
      (.frame plans env [Loc.base ra] [] k func.wrapper))
    (hnv := rfl) (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl))
  intro σ₁ hfns hmeths htypes
  have hstep := Step.callImmediate (env := env) (k := k)
    hplan rfl (henter σ₁ hfns hmeths htypes)
  refine ⟨hstep, ?_⟩
  intro c' s' hst
  obtain ⟨h1, h2⟩ := step_det (by simp [Config.choiceFree, stmtPlan]) hstep hst
  exact ⟨h1.symm, h2.symm⟩

/-- Value frame exit at an int result (`wp_frame_return_int`'s port —
the four-step spine walk: read the pinned result, evaluate the caller
target post-call, complete, store normalizing). -/
theorem wpDM_frame_return_int {x : String} {tenv : LocalEnv} {ta ra : Addr}
    {kind tkind : IntKind} {m : Int} {w : GoValue} {k : Cont} {wf : Bool}
    (hres : LocalEnv.lookup tenv x = some (.base ta)) :
    ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.int tkind), w⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
          ∗ ta.id ↦ (⟨some (.int tkind), .int (tkind.normalize m) tkind⟩ : HeapCell)
          -∗ WP (PoolCfgDM.mk (.next k)) @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.returning
            (.frame [(.chain [], [.ref x])] tenv [.base ra] [] k wf)))
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Ht, Hcont⟩
  -- step 1: the frame exit READS the pinned result cell
  iapply (wpDM_det_step_keep
    (P := iprop(ra.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)))
    (c₁ := Config.evalE (.ref x) tenv (.tgtOpK (.chain []) [] [] [] []
      .vals [] [.int m kind] (.seqn #[]) tenv k))
    (hnv := rfl) (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hred := fun σ₁ _hfns _hmeths _htypes => by
      iintro ⟨Hσ, Hpt⟩
      ihave %Hmap : ⌜get? (heapToMap σ₁.heap) ra.id
          = some (⟨some (.int kind), .int m kind⟩ : HeapCell)⌝ $$ [Hσ Hpt]
      · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
        itrivial
      have hlook : Heap.lookup σ₁.heap (.base ra)
          = some ⟨some (.int kind), .int m kind⟩ := by
        rw [get?_heapToMap] at Hmap; simpa using Hmap
      have hload : loadMany σ₁ [Loc.base ra] = .ok [GoValue.int m kind] := by
        simp [loadMany, loadLoc, hlook, Bind.bind, Except.bind]
      imodintro
      ipureintro
      refine ⟨Step.frameReturnTargets hload, ?_⟩
      intro c' s' hst
      obtain ⟨h1, h2⟩ := step_det (by trivial)
        (Step.frameReturnTargets hload) hst
      exact ⟨h1.symm, h2.symm⟩))
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  -- step 2: the caller-target operand, post-call
  iapply (wpDM_eval_ref hres)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  -- step 3: the target completes
  iapply (wpDM_tgtop_stores (r := .chain (.addr (.base ta)) [] []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro -
  simp only [List.nil_append]
  -- step 4: the store (normalizing at the target's kind)
  iapply (wpDM_assign_store_loc
    (oldcell := ⟨some (.int tkind), w⟩)
    (newcell := ⟨some (.int tkind), .int (tkind.normalize m) tkind⟩)
    (hstore := fun σ₁ _ht hlook => storeLoc_int_any hlook m))
  isplitl [Ht]
  · iexact Ht
  iintro Ht
  iapply wpDM_stores_done_nil
  iapply Hcont
  isplitl [Hr]
  · iexact Hr
  · iexact Ht

/-! ## Go-statement and channel-statement glue -/

@[go_walk_law]
theorem wpDM_gostmt_entry {callee : Expr} {args : Array Expr}
    {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE callee env (.goCalleeK args.toList env k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.exec (.goStmt callee args) env k)) @ s ; E {{ Φ }} :=
  wpDM_pure_step (by simp [Config.choiceFree, stmtPlan]) rfl rfl rfl rfl
    (fun _ => Step.goStmtEntry)

@[go_walk_law]
theorem wpDM_gocallee_arg {cv : GoValue} {a : Expr} {rest : List Expr}
    {env : LocalEnv} {k : Cont}
    (hdef : deferrableCallee cv = true) :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE a env (.goArgsK cv [] rest env k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.retV cv (.goCalleeK (a :: rest) env k)))
        @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.goCalleeArg hdef)

@[go_walk_law]
theorem wpDM_goarg_next {v cv : GoValue} {vals : List GoValue} {a : Expr}
    {rest : List Expr} {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE a env (.goArgsK cv (vals ++ [v]) rest env k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.retV v (.goArgsK cv vals (a :: rest) env k)))
        @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.goArgNext)

@[go_walk_law]
theorem wpDM_chanst_first {stmt : Stmt} {op : ChanStOp} {e : Expr}
    {rest : List Expr} {env : LocalEnv} {k : Cont}
    (hplan : chanPlan stmt = some (op, e :: rest)) :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE e env (.chanStK op [] rest env k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.exec stmt env k)) @ s ; E {{ Φ }} :=
  wpDM_pure_step (by
      have := stmtPlan_of_chanPlan hplan
      simp [Config.choiceFree, this]) rfl rfl rfl rfl
    (fun _ => Step.chanStFirst hplan)

@[go_walk_law]
theorem wpDM_chanst_shift {op : ChanStOp} {done : List GoValue} {v : GoValue}
    {e : Expr} {rest : List Expr} {env : LocalEnv} {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗
      WP (PoolCfgDM.mk (.evalE e env (.chanStK op (v :: done) rest env k)))
        @ s ; E {{ Φ }}) ⊢
      WP (PoolCfgDM.mk (.retV v (.chanStK op done (e :: rest) env k)))
        @ s ; E {{ Φ }} :=
  wpDM_pure_step trivial rfl rfl rfl rfl (fun _ => Step.chanStShift)

end

end GoLean.Iris
