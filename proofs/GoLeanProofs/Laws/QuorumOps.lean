import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.MachineSound
import GoLeanProofs.HeapBridge
import GoLeanProofs.Laws.Eval
import GoLeanProofs.Laws.Range
import GoLeanProofs.Specs.GoldenQuorum

/-!
# Quorum-op laws — the per-construct laws the `CommittedIndex` walk needs
(quorum pilot phase 4 item 2, 2026-07-31)

The constructs the pinned `CommittedIndex` lowering
(`Specs/GoldenQuorum.quorumLowered`) hits that had no WP law:

1. **`mapRangeSnapshot`** — the state-READING step that turns the ranged
   map value into the iteration snapshot (`Laws/Range` starts one step
   later, at `mapIterK`). Two forms: through a `.mapData` cell
   (`wp_map_range_snapshot`) and the nil map (`wp_map_range_snapshot_nil`,
   pure — the machine reads nothing).
2. **The wide-statement (`stmtOpK`) walk** — `wp_stmt_op_first`,
   `wp_stmt_op_shift_target`, `wp_stmt_op_shift_plain`, and the apply
   step. NOTHING existed for the `stmtOpK` family before this file; every
   wide statement (`sortSlice`, `mapLookup`, `makeSlice`, `appendSlice`,
   `mapAssign`, …) enters through these.
3. **`sortSlice`** (`wp_sort_slice`) — the `slices.Sort` extern. A slice's
   backing store is ONE heap cell holding an `.array`, so despite the
   multi-element read+write this is a single-cell step: the
   `wp_stmt_op_apply_store` core applies verbatim.
4. **`mapLookup`** (`wp_map_lookup`) — the comma-ok read, a THREE-cell
   step (read the map's data cell, write the value target and the ok
   target); `wp_read_store_step₂` is the new core.

What the apply-step cores here do NOT cover: wide ops that ALLOCATE
inside `applyStmtOp` (`makeMap`, `makeSlice`, `newValue`, `appendSlice`'s
spill path) — those need an allocating apply core in the
`wp_call_enter_*` style (`genHeap_alloc` + `∀`-quantified fresh address),
not a store core. The operand walk (`wp_stmt_op_first`/the shifts) is
shared by all of them.

## The blocker this file DOCUMENTS rather than papers over

`wp_call_dynamic_enter` (frame entry through the interface anchor) is NOT
here, and neither is any frame-entry law for the quorum program.
`GoCoreGS` pins `σ.functions` and `σ.methods`, but **not `σ.types`** —
while `enterFrame`/`dynamicDispatch?` on this program depend on it:

* `bindParams` normalizes each argument at its declared type, and every
  quorum entry point has a `.defined`-typed parameter (`main.MajorityConfig`,
  `main.mapAckIndexer`, `main.Index`);
* `allocDecls` defaults the results at their declared type (`$res0 :
  main.Index`);
* `concreteMethodForDynamic?` compares the receiver box's dynamic tag
  against `canonicalTy σ method.recv`, and a method receiver is always a
  defined type.

Each of those resolves through `TypeEnv.lookup σ.types` and FAILS CLOSED
on an unknown name, so a premise of the house `∀ σ, σ.functions = … →
σ.methods = … → …` shape is *false* at defined types — a law taking one
would be vacuous exactly the way the non-vacuity gate exists to catch.
`typeEnv_pin_is_load_bearing` below is the kernel-checked demonstration.
The fix is an arc-level change to the ghost state (a `types` field on
`GoCoreGS` + a conjunct in the state interpretation, and the matching
`obtain ⟨hfns, hmeths, hwf⟩` updates in every existing law file); it is
deliberately NOT smuggled in here.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris

set_option linter.unusedSimpArgs false

/-! ## Heap algebra the multi-write steps need

`Laws/*` so far only ever wrote ONE cell per step; `applyStmtOp`'s wide
ops write repeatedly (`sortSlice`: once per element; `mapLookup`: the
value target then the ok target). These two lemmas are what let a
repeated-`Heap.set` computation be read back as the single-`Heap.set`
shape the store cores expect. Both avoid any `LawfulBEq Loc` assumption
by casing on the SAME `loc == needle` boolean the definitions case on. -/

/-- Overwriting a mapped location twice keeps only the second write. -/
theorem heap_set_set_of_lookup {h : Heap} {l : Loc} {c₀ c₁ c₂ : HeapCell}
    (hl : Heap.lookup h l = some c₀) :
    Heap.set (Heap.set h l c₁) l c₂ = Heap.set h l c₂ := by
  induction h with
  | nil => simp [Heap.lookup] at hl
  | cons p rest ih =>
    obtain ⟨loc, old⟩ := p
    simp only [Heap.lookup] at hl
    cases hb : (loc == l) with
    | true => simp [Heap.set, hb]
    | false =>
      simp only [hb, Bool.false_eq_true, if_false] at hl
      simp only [Heap.set, hb, Bool.false_eq_true, if_false]
      exact congrArg _ (ih hl)

/-- Reading back the location just written (base locations, via the
`heapToMap` bridge — no `LawfulBEq Loc` assumption). -/
theorem heap_lookup_set_base_self (h : Heap) (a : Addr) (c : HeapCell) :
    Heap.lookup (Heap.set h (.base a) c) (.base a) = some c := by
  rw [← get?_heapToMap, (heapToMap_set_base h a c) a.id,
    LawfulPartialMap.get?_insert]
  simp

/-- Bridge B for TWO successive base writes (what a two-target wide op
does): the projection is the two inserts. -/
theorem heapToMap_set_base₂ (h : Heap) (ta oa : Addr) (tc oc : HeapCell) :
    heapToMap (Heap.set (Heap.set h (.base ta) tc) (.base oa) oc)
      ≡ₘ insert (insert (heapToMap h) ta.id tc) oa.id oc := by
  intro kk
  rw [(heapToMap_set_base (Heap.set h (.base ta) tc) oa oc) kk,
    LawfulPartialMap.get?_insert, LawfulPartialMap.get?_insert]
  by_cases hk : oa.id = kk
  · simp [hk]
  · simp [hk, (heapToMap_set_base h ta tc) kk, LawfulPartialMap.get?_insert]

/-- A mapped location stays mapped across a write anywhere. -/
theorem heap_lookup_set_isSome {h : Heap} {l l' : Loc} {c : HeapCell} {x : HeapCell}
    (hl : Heap.lookup h l' = some x) :
    ∃ y, Heap.lookup (Heap.set h l c) l' = some y := by
  induction h with
  | nil => simp [Heap.lookup] at hl
  | cons p rest ih =>
    obtain ⟨loc, old⟩ := p
    simp only [Heap.lookup] at hl
    cases hb : (loc == l) with
    | true =>
      simp only [Heap.set, hb, if_true]
      cases hb' : (loc == l') with
      | true => exact ⟨c, by simp [Heap.lookup, hb']⟩
      | false =>
        simp only [hb', Bool.false_eq_true, if_false] at hl
        exact ⟨x, by simp [Heap.lookup, hb', hl]⟩
    | false =>
      simp only [Heap.set, hb, Bool.false_eq_true, if_false]
      cases hb' : (loc == l') with
      | true => exact ⟨old, by simp [Heap.lookup, hb']⟩
      | false =>
        simp only [hb', Bool.false_eq_true, if_false] at hl
        simpa [Heap.lookup, hb'] using ih hl

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-! ## 1. The map-range snapshot step -/

/-- **The snapshot step (state-reading)**: `for … range m` with `m` a
non-nil map value loads the map's data cell and installs its entries as
the iteration snapshot. The data cell rides through unchanged (`mapRange`
snapshots — later writes to the map do not affect the iteration), so this
is a `wp_det_step_keep` read, exactly like `wp_eval_var`. `Laws/Range`
picks up from the `mapIterK` this produces. -/
theorem wp_map_range_snapshot {ba : Addr} {mty : Option Ty}
    {entries : Array (GoValue × GoValue)} {keyVar valVar : Option String}
    {keyTy valTy : Ty} {body : Stmt} {env k} :
    ba.id ↦ (⟨mty, .mapData entries⟩ : HeapCell)
      ∗ (ba.id ↦ (⟨mty, .mapData entries⟩ : HeapCell) -∗
          WP (Config.next (.mapIterK keyVar valVar keyTy valTy body entries env k))
            @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.map ⟨some (.base ba)⟩)
            (.mapRangeK keyVar valVar keyTy valTy body env k)) @ s ; E {{ Φ }} := by
  iapply wp_det_step_keep (P := iprop(ba.id ↦ (⟨mty, .mapData entries⟩ : HeapCell)))
    (c₁ := Config.next (.mapIterK keyVar valVar keyTy valTy body entries env k))
    (hnv := rfl)
  intro σ₁
  iintro ⟨Hσ, Hpt⟩
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) ba.id
      = some (⟨mty, .mapData entries⟩ : HeapCell)⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base ba) = some ⟨mty, .mapData entries⟩ := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hentries : mapRangeEntries σ₁ (.map ⟨some (.base ba)⟩) = .ok entries := by
    simp [mapRangeEntries, valueAsMap, loadLoc, hlook, Bind.bind, Except.bind]
  imodintro
  ipureintro
  refine ⟨Step.mapRangeSnapshot hentries, ?_⟩
  intro c' s' hst
  obtain ⟨h1, h2⟩ := step_det (by trivial) (Step.mapRangeSnapshot hentries) hst
  exact ⟨h1.symm, h2.symm⟩

/-- **The nil-map snapshot step (pure)**: a nil map has no data cell, so
the machine reads nothing and the snapshot is empty — no resources
needed. (`Laws/Range.wp_map_iter_done` then exits the loop in one more
step.) -/
theorem wp_map_range_snapshot_nil {keyVar valVar : Option String}
    {keyTy valTy : Ty} {body : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.next (.mapIterK keyVar valVar keyTy valTy body #[] env k))
        @ s ; E {{ Φ }}) ⊢
      WP (Config.retV (.map ⟨none⟩)
            (.mapRangeK keyVar valVar keyTy valTy body env k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial
    (fun _ => Step.mapRangeSnapshot
      (by simp [mapRangeEntries, valueAsMap, Bind.bind, Except.bind]))

/-! ## 2. The wide-statement (`stmtOpK`) walk -/

/-- **Enter a wide statement**: `stmtPlan` gives the op, the number of
leading TARGET operands, and the operand expressions in evaluation order;
the machine evaluates the first one under a `stmtOpK` frame. Generic over
the whole `StmtOp` table. -/
theorem wp_stmt_op_first {stmt : Stmt} {op : StmtOp} {nt : Nat} {e : Expr}
    {rest : List Expr} {env k}
    (hplan : stmtPlan stmt = some (op, nt, e :: rest)) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE e env (.stmtOpK op nt [] rest env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec stmt env k) @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree, hplan]) (fun _ => Step.stmtOpFirst hplan)

/-- Shift to the next operand while still in the TARGET prefix: the
delivered value must be an address (`hloc`), which is recorded and the
next operand evaluated. -/
theorem wp_stmt_op_shift_target {op : StmtOp} {nt : Nat} {done : List GoValue}
    {v : GoValue} {loc : Loc} {e : Expr} {rest : List Expr} {env k}
    (hnt : done.length < nt) (hloc : valueAsLoc v = .ok loc) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE e env (.stmtOpK op nt (v :: done) rest env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.retV v (.stmtOpK op nt done (e :: rest) env k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.stmtOpShiftTarget hnt hloc)

/-- Shift to the next operand past the target prefix (a plain value
operand — no address check). -/
theorem wp_stmt_op_shift_plain {op : StmtOp} {nt : Nat} {done : List GoValue}
    {v : GoValue} {e : Expr} {rest : List Expr} {env k}
    (hnt : nt ≤ done.length) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE e env (.stmtOpK op nt (v :: done) rest env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.retV v (.stmtOpK op nt done (e :: rest) env k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.stmtOpShiftPlain hnt)

/-- **The apply step, single-cell form**: the last operand arrives and ONE
step performs the whole state update. `happly` is the wide op's
cell-conditioned state-transition fact, in the `wp_assign_store`/`hstore`
style: given the owned cell's content, `applyStmtOp` rewrites exactly that
cell (any `Choices` stream — the ops this covers consume none).

The apply position is NOT `choiceFree` (`appendSlice`'s spill consumes a
capacity choice), so determinism is proved here by inversion instead of
`step_det`: `happly`'s `∀ ch` closes the choice-stream quantifier, and the
panic arm contradicts `.ok`. -/
theorem wp_stmt_op_apply_store {op : StmtOp} {nt : Nat} {done : List GoValue}
    {v : GoValue} {a : Addr} {oldcell newcell : HeapCell} {env k}
    (happly : ∀ (σ : ExecState) (ch : Choices),
      Heap.lookup σ.heap (.base a) = some oldcell →
      applyStmtOp σ ch op nt (v :: done).reverse
        = .ok ({ σ with heap := Heap.set σ.heap (.base a) newcell }, ch)) :
    a.id ↦ oldcell ∗ (a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV v (.stmtOpK op nt done [] env k)) @ s ; E {{ Φ }} := by
  iapply wp_store_step (hnv := rfl)
  intro σ₁ hlook
  refine ⟨Step.stmtOpApply (ch := []) (happly σ₁ [] hlook), ?_⟩
  intro c' s' hst
  cases hst with
  | @stmtOpApply _ _ _ _ _ _ _ _ ch _ hap =>
    rw [happly σ₁ ch hlook] at hap
    injection hap with hap
    exact ⟨rfl, (Prod.mk.inj hap).1.symm⟩
  | @stmtOpApplyPanic _ _ _ _ _ _ _ _ ch hap =>
    rw [happly σ₁ ch hlook] at hap
    exact absurd hap (by simp)

/-! ## 3. `sortSlice` — the `slices.Sort` extern -/

/-- **`slices.Sort` on an integer slice**, as ONE apply step. A slice's
elements live in a single backing cell (`Loc.index base i` stores go
through `storeLoc`'s array path), so the whole multi-element read+sort+
write-back touches exactly one owned cell — the general single-cell apply
core applies verbatim, no big-sep over element cells needed (the
granularity ledger's `sortSlice` entry, `applyStmtOp`). `happly` is the
computed transition, discharged per instantiation. -/
theorem wp_sort_slice {elem : Ty} {slice : SliceValue} {a : Addr}
    {oldcell newcell : HeapCell} {env k}
    (happly : ∀ (σ : ExecState) (ch : Choices),
      Heap.lookup σ.heap (.base a) = some oldcell →
      applyStmtOp σ ch (.sortSlice elem) 0 [.slice slice]
        = .ok ({ σ with heap := Heap.set σ.heap (.base a) newcell }, ch)) :
    a.id ↦ oldcell ∗ (a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.slice slice)
            (.stmtOpK (.sortSlice elem) 0 [] [] env k)) @ s ; E {{ Φ }} :=
  wp_stmt_op_apply_store (done := []) happly

/-! ## 4. `mapLookup` — the comma-ok read

Three cells move in ONE step (the map's data cell is read; the value
target and the ok target are written), so a new lifting core is needed:
`Lifting.lean` tops out at one read + one write (`wp_store_step₂`). The
core supplies the two targets' DISEQUALITY to its reduction premise —
derived from owning both points-tos, so no caller-side aliasing
side-condition is needed (the second `storeLoc` must see the first
write's heap). -/

/-- Two owned full-fraction cells are at distinct addresses. -/
theorem pointsTo_ne' {a b : Addr} {c₁ c₂ : HeapCell} :
    (iprop(a.id ↦ c₁ ∗ b.id ↦ c₂) : IProp GF) ⊢ ⌜a.id ≠ b.id⌝ := by
  iintro ⟨H1, H2⟩
  iapply pointsTo_ne $$ H1 H2

/-- **One-read/two-write step core.** The step reads the cell at `ra`
(riding through unchanged) and writes `ta` then `oa`, in that order —
the composed `Heap.set` shape `applyStmtOp`'s two-target ops produce. -/
theorem wp_read_store_step₂ {ra ta oa : Addr}
    {rcell tcell tcell' ocell ocell' : HeapCell} {c₀ : Config} {k}
    (hnv : ToVal.toVal c₀ = (none : Option Unit))
    (hred : ∀ σ₁ : ExecState, ta.id ≠ oa.id →
      Heap.lookup σ₁.heap (.base ra) = some rcell →
      Heap.lookup σ₁.heap (.base ta) = some tcell →
      Heap.lookup σ₁.heap (.base oa) = some ocell →
      Step c₀ σ₁ (.next k)
          { σ₁ with heap := Heap.set (Heap.set σ₁.heap (.base ta) tcell')
                              (.base oa) ocell' } ∧
      (∀ c' s', Step c₀ σ₁ c' s' →
          c' = Config.next k ∧
          s' = { σ₁ with heap := Heap.set (Heap.set σ₁.heap (.base ta) tcell')
                                   (.base oa) ocell' })) :
    ra.id ↦ rcell ∗ ta.id ↦ tcell ∗ oa.id ↦ ocell
      ∗ (ra.id ↦ rcell ∗ ta.id ↦ tcell' ∗ oa.id ↦ ocell'
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP c₀ @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Ht, Ho, Hcont⟩
  iapply wp_lift_step (h := hnv)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, hwf⟩ := Hinv
  ihave %Hmr : ⌜get? (heapToMap σ₁.heap) ra.id = some rcell⌝ $$ [Hσ Hr]
  · icases genHeap_valid $$ [$Hσ $Hr] with >%h
    itrivial
  ihave %Hmt : ⌜get? (heapToMap σ₁.heap) ta.id = some tcell⌝ $$ [Hσ Ht]
  · icases genHeap_valid $$ [$Hσ $Ht] with >%h
    itrivial
  ihave %Hmo : ⌜get? (heapToMap σ₁.heap) oa.id = some ocell⌝ $$ [Hσ Ho]
  · icases genHeap_valid $$ [$Hσ $Ho] with >%h
    itrivial
  ihave %Hne : ⌜ta.id ≠ oa.id⌝ $$ [Ht Ho]
  · icases pointsTo_ne' $$ [$Ht $Ho] with %h
    itrivial
  have hlookr : Heap.lookup σ₁.heap (.base ra) = some rcell := by
    rw [get?_heapToMap] at Hmr; simpa using Hmr
  have hlookt : Heap.lookup σ₁.heap (.base ta) = some tcell := by
    rw [get?_heapToMap] at Hmt; simpa using Hmt
  have hlooko : Heap.lookup σ₁.heap (.base oa) = some ocell := by
    rw [get?_heapToMap] at Hmo; simpa using Hmo
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], Config.next k, _, [],
        GoPrimStep.step (hred σ₁ Hne hlookr hlookt hlooko).1⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    obtain ⟨rfl, rfl⟩ := (hred σ₁ Hne hlookr hlookt hlooko).2 _ _ st
    imod (genHeap_update (v₂ := tcell')) $$ [$Hσ $Ht] with ⟨Hσ, Ht⟩
    imod (genHeap_update (v₂ := ocell')) $$ [$Hσ $Ho] with ⟨Hσ, Ho⟩
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    obtain ⟨y, hy⟩ := heap_lookup_set_isSome (l := .base ta) (c := tcell') hlooko
    isplitl [Hσ]
    · isplitl [Hσ]
      · iapply (genHeapInterp_eqv
          (fun kk => (heapToMap_set_base₂ σ₁.heap ta oa tcell' ocell' kk).symm)) $$ Hσ
      · ipureintro
        exact ⟨hfns, hmeths, (hwf.set_existing hlookt).set_existing hy⟩
    · isplitl [Hr Ht Ho Hcont]
      · iapply Hcont $$ [$Hr $Ht $Ho]
      · itrivial

/-- **The apply step, one-read/two-write form** — the wide-op face of
`wp_read_store_step₂` (the `mapLookup`/`typeAssertStmt` shape: two target
cells written, one state cell read). -/
theorem wp_stmt_op_apply_read_store₂ {op : StmtOp} {nt : Nat} {done : List GoValue}
    {v : GoValue} {ra ta oa : Addr}
    {rcell tcell tcell' ocell ocell' : HeapCell} {env k}
    (happly : ∀ (σ : ExecState) (ch : Choices), ta.id ≠ oa.id →
      Heap.lookup σ.heap (.base ra) = some rcell →
      Heap.lookup σ.heap (.base ta) = some tcell →
      Heap.lookup σ.heap (.base oa) = some ocell →
      applyStmtOp σ ch op nt (v :: done).reverse
        = .ok ({ σ with heap := Heap.set (Heap.set σ.heap (.base ta) tcell')
                                  (.base oa) ocell' }, ch)) :
    ra.id ↦ rcell ∗ ta.id ↦ tcell ∗ oa.id ↦ ocell
      ∗ (ra.id ↦ rcell ∗ ta.id ↦ tcell' ∗ oa.id ↦ ocell'
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV v (.stmtOpK op nt done [] env k)) @ s ; E {{ Φ }} := by
  iapply wp_read_store_step₂ (hnv := rfl)
  intro σ₁ hne hlookr hlookt hlooko
  refine ⟨Step.stmtOpApply (ch := []) (happly σ₁ [] hne hlookr hlookt hlooko), ?_⟩
  intro c' s' hst
  cases hst with
  | @stmtOpApply _ _ _ _ _ _ _ _ ch _ hap =>
    rw [happly σ₁ ch hne hlookr hlookt hlooko] at hap
    injection hap with hap
    exact ⟨rfl, (Prod.mk.inj hap).1.symm⟩
  | @stmtOpApplyPanic _ _ _ _ _ _ _ _ ch hap =>
    rw [happly σ₁ ch hne hlookr hlookt hlooko] at hap
    exact absurd hap (by simp)

/-- **The comma-ok map read** `t, ok = m[key]` as ONE apply step: the
map's data cell is read, the value target and the ok target are written
(in that order — the machine's `storeLoc`/`storeLoc` sequence).

The premises are the machine's own computations, in the
`wp_assign_store`/`hstore` style: `hkey` normalizes the key operand at the
range key type, `hpair` is the lookup's `(value, found)` answer given the
owned data cell, and the two `hstore*` are the cell-conditioned writes.
They are all state-quantified, so they are dischargeable exactly when the
types involved are `σ.types`-independent (see this module's header —
`.defined`-typed target cells are the blocked case). -/
theorem wp_map_lookup {keyTy valTy : Ty} {mba ta oa : Addr} {mty : Option Ty}
    {entries : Array (GoValue × GoValue)} {keyV key val : GoValue} {b : Bool}
    {tcell tcell' ocell ocell' : HeapCell} {env k}
    (hkey : ∀ σ : ExecState, normalizeValueForTy σ keyTy keyV = .ok key)
    (hpair : ∀ σ : ExecState,
      Heap.lookup σ.heap (.base mba) = some ⟨mty, .mapData entries⟩ →
      mapLookupValue σ ⟨some (.base mba)⟩ key keyTy valTy = .ok (val, b))
    (hstoret : ∀ σ : ExecState, Heap.lookup σ.heap (.base ta) = some tcell →
      storeLoc σ (.base ta) val
        = .ok { σ with heap := Heap.set σ.heap (.base ta) tcell' })
    (hstoreo : ∀ σ : ExecState, Heap.lookup σ.heap (.base oa) = some ocell →
      storeLoc σ (.base oa) (.bool b)
        = .ok { σ with heap := Heap.set σ.heap (.base oa) ocell' }) :
    mba.id ↦ (⟨mty, .mapData entries⟩ : HeapCell) ∗ ta.id ↦ tcell ∗ oa.id ↦ ocell
      ∗ (mba.id ↦ (⟨mty, .mapData entries⟩ : HeapCell) ∗ ta.id ↦ tcell'
            ∗ oa.id ↦ ocell' -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV keyV
            (.stmtOpK (.mapLookup keyTy valTy) 2
              [.map ⟨some (.base mba)⟩, .addr (.base oa), .addr (.base ta)] [] env k))
        @ s ; E {{ Φ }} := by
  iapply wp_stmt_op_apply_read_store₂
  intro σ ch hne hlookm hlookt hlooko
  have hlooko' : Heap.lookup (Heap.set σ.heap (.base ta) tcell') (.base oa)
      = some ocell := by
    rw [heap_lookup_set_base_ne (b := ta) (n := oa.id) hne]
    exact hlooko
  have hstore2 := hstoreo { σ with heap := Heap.set σ.heap (.base ta) tcell' } hlooko'
  simp [applyStmtOp, valueAsMap, valueAsLoc, hkey σ, hpair σ hlookm,
    hstoret σ hlookt, hstore2, Bind.bind, Except.bind]

end

/-! ## The witness subjects, EXTRACTED FROM THE PIN

Each witness below runs on a statement *projected out of*
`GoldenQuorum.quorumLowered` — the frontend's actual lowering — so the
`rfl`-checked `*_eq` lemmas are what tie the laws to the real code (edit
the pin and these stop being `rfl`). -/

namespace QuorumPin

open GoLean.Iris.GoldenQuorum

/-- The pinned `main.MajorityConfig.CommittedIndex`'s statement list. -/
def committedIndexStmts : Array Stmt :=
  match findFunctionIn? quorumLowered.funcs ⟨"main.MajorityConfig.CommittedIndex"⟩ with
  | some f => match f.body with
    | .block _ ss => ss
    | _ => #[]
  | none => #[]

/-- The pinned `main.mapAckIndexer.AckedIndex`'s statement list. -/
def ackedIndexStmts : Array Stmt :=
  match findFunctionIn? quorumLowered.funcs ⟨"main.mapAckIndexer.AckedIndex"⟩ with
  | some f => match f.body with
    | .block _ ss => ss
    | _ => #[]
  | none => #[]

/-- `slices.Sort(srt)` — the sort of the acked-index scratch slice. -/
def sortStmt : Stmt := (committedIndexStmts[6]?).getD (.seqn #[])

/-- `for id := range c` — the voter loop. -/
def rangeStmt : Stmt :=
  match (committedIndexStmts[5]?).getD (.seqn #[]) with
  | .block _ inner => (inner[1]?).getD (.seqn #[])
  | _ => .seqn #[]

/-- The voter loop's body (whatever the pin says it is). -/
def rangeBody : Stmt :=
  match rangeStmt with
  | .mapRange _ _ _ _ _ b => b
  | _ => .seqn #[]

/-- `idx, ok := m[id]` — the comma-ok read inside `AckedIndex`. -/
def mapLookupStmt : Stmt :=
  match (ackedIndexStmts[0]?).getD (.seqn #[]) with
  | .seqn arr => (arr[2]?).getD (.seqn #[])
  | _ => .seqn #[]

theorem sortStmt_eq : sortStmt = .sortSlice (.var "srt") (.int .uint64) := rfl

theorem rangeStmt_eq :
    rangeStmt = .mapRange (some "id") none (.var "c") (.int .uint64)
      (.defined ⟨"struct{}"⟩) rangeBody := rfl

theorem mapLookupStmt_eq :
    mapLookupStmt = .mapLookup (.var "idx") (.var "ok") (.var "m") (.var "id")
      (.int .uint64) (.defined ⟨"main.Index"⟩) := rfl

/-! The concrete cells the `sortSlice` witness sorts: a 3-element `uint64`
backing array, unsorted, and its sorted image. -/

def sortOldCell : HeapCell :=
  ⟨some (.array 3 (.int .uint64)),
   .array #[.int 3 .uint64, .int 1 .uint64, .int 2 .uint64]⟩

def sortNewCell : HeapCell :=
  ⟨some (.array 3 (.int .uint64)),
   .array #[.int 1 .uint64, .int 2 .uint64, .int 3 .uint64]⟩

end QuorumPin

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-! ## Non-vacuity witnesses, on the pinned lowering -/

/-- **Witness for `wp_map_range_snapshot`** on the REAL voter loop
(`QuorumPin.rangeStmt`, `rfl`-projected out of the pin): dispatch the
range, load `c`, snapshot its data cell — landing exactly on the
`mapIterK` that `Laws/Range`'s nondeterministic law consumes. Premise-free
beyond the environment resolution and the two owned cells. -/
theorem wp_map_range_snapshot_committed {ca mba : Addr}
    {entries : Array (GoValue × GoValue)} {env k}
    (hres : LocalEnv.lookup env "c" = some (.base ca)) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base mba)⟩⟩ : HeapCell)
      ∗ mba.id ↦ (⟨some (.map (.int .uint64) (.defined ⟨"struct{}"⟩)),
                   .mapData entries⟩ : HeapCell)
      ∗ (ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
                   .map ⟨some (.base mba)⟩⟩ : HeapCell)
          ∗ mba.id ↦ (⟨some (.map (.int .uint64) (.defined ⟨"struct{}"⟩)),
                       .mapData entries⟩ : HeapCell)
          -∗ WP (Config.next (.mapIterK (some "id") none (.int .uint64)
                (.defined ⟨"struct{}"⟩) QuorumPin.rangeBody entries env k))
              @ s ; E {{ Φ }})
      ⊢ WP (Config.exec QuorumPin.rangeStmt env k) @ s ; E {{ Φ }} := by
  iintro ⟨Hc, Hm, Hcont⟩
  rw [QuorumPin.rangeStmt_eq]
  iapply wp_map_range_start
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcr1
  iapply (wp_eval_var (cell := ⟨some (.defined ⟨"main.MajorityConfig"⟩),
    .map ⟨some (.base mba)⟩⟩) hres)
  isplitl [Hc]
  · iexact Hc
  iintro Hc
  iapply wp_map_range_snapshot
  isplitl [Hm]
  · iexact Hm
  iintro Hm
  iapply Hcont $$ [$Hc $Hm]

/-- **Witness for `wp_sort_slice`** (and for `wp_stmt_op_first`) on the
REAL `slices.Sort(srt)` statement of the pinned `CommittedIndex`: the
whole statement walk — plan dispatch, the `srt` load, the sort step — on a
concrete 3-element `uint64` backing array, `[3,1,2] ↦ [1,2,3]`. Every
premise is discharged by computation; the sort's `happly` is the machine's
own `applyStmtOp` run. -/
theorem wp_sort_slice_srt {sa ba : Addr} {env k}
    (hres : LocalEnv.lookup env "srt" = some (.base sa)) :
    sa.id ↦ (⟨some (.slice (.int .uint64)),
              .slice ⟨some (.base ba), 0, 3, 3⟩⟩ : HeapCell)
      ∗ ba.id ↦ QuorumPin.sortOldCell
      ∗ (sa.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base ba), 0, 3, 3⟩⟩ : HeapCell)
          ∗ ba.id ↦ QuorumPin.sortNewCell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec QuorumPin.sortStmt env k) @ s ; E {{ Φ }} := by
  iintro ⟨Hs, Hb, Hcont⟩
  rw [QuorumPin.sortStmt_eq]
  iapply (wp_stmt_op_first (op := .sortSlice (.int .uint64)) (nt := 0)
    (e := .var "srt") (rest := []) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcs1
  iapply (wp_eval_var (cell := ⟨some (.slice (.int .uint64)),
    .slice ⟨some (.base ba), 0, 3, 3⟩⟩) hres)
  isplitl [Hs]
  · iexact Hs
  iintro Hs
  iapply (wp_sort_slice (a := ba) (oldcell := QuorumPin.sortOldCell)
    (newcell := QuorumPin.sortNewCell)
    (happly := by
      intro σ ch hlook
      have n1 : IntKind.uint64.normalize 1 = 1 := by rfl
      have n2 : IntKind.uint64.normalize 2 = 2 := by rfl
      have n3 : IntKind.uint64.normalize 3 = 3 := by rfl
      simp [applyStmtOp, valueAsSlice, validateSlice, sliceIndexLoc, loadLoc,
        hlook, QuorumPin.sortOldCell, QuorumPin.sortNewCell,
        heap_lookup_set_base_self, Bind.bind, Except.bind, List.range',
        List.forIn_cons, List.forIn_nil, arrayGet, arrayIndexNat, storeLoc,
        arraySet, coerceStoredValue, normalizeValueForTy,
        normalizeValueForTyFuel, normalizeArrayForTy, List.mergeSort,
        heap_set_set_of_lookup hlook, Functor.map, Except.map, n1, n2, n3]))
  isplitl [Hb]
  · iexact Hb
  iintro Hb
  iapply Hcont $$ [$Hs $Hb]

/-- **Witness for `wp_map_lookup`** (and for the target/plain operand
shifts) on the REAL `idx, ok := m[id]` of the pinned
`main.mapAckIndexer.AckedIndex`: the whole statement walk on a one-entry
`uint64 → Index` map, key present, `12` delivered with `ok = true`.

RECORDED DIVERGENCE from the pin: the `idx` cell is declared
`.int .uint64` here, where the lowering declares it
`.defined main.Index`. The store into a `.defined`-typed cell resolves
through `σ.types`, which the ghost state does not pin — see this module's
header. The map's VALUE type is the faithful `.defined main.Index` (the
found branch never touches `defaultValue`), as are the key type and the
statement itself. -/
theorem wp_map_lookup_ackedIndex {ma ida mba ta oa : Addr} {env k}
    (hm : LocalEnv.lookup env "m" = some (.base ma))
    (hid : LocalEnv.lookup env "id" = some (.base ida))
    (hidx : LocalEnv.lookup env "idx" = some (.base ta))
    (hok : LocalEnv.lookup env "ok" = some (.base oa)) :
    ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
              .map ⟨some (.base mba)⟩⟩ : HeapCell)
      ∗ ida.id ↦ (⟨some (.int .uint64), .int 3 .uint64⟩ : HeapCell)
      ∗ mba.id ↦ (⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
                   .mapData #[(.int 3 .uint64, .int 12 .uint64)]⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.int .uint64), .int 0 .uint64⟩ : HeapCell)
      ∗ oa.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                   .map ⟨some (.base mba)⟩⟩ : HeapCell)
          ∗ ida.id ↦ (⟨some (.int .uint64), .int 3 .uint64⟩ : HeapCell)
          ∗ mba.id ↦ (⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
                       .mapData #[(.int 3 .uint64, .int 12 .uint64)]⟩ : HeapCell)
          ∗ ta.id ↦ (⟨some (.int .uint64), .int 12 .uint64⟩ : HeapCell)
          ∗ oa.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec QuorumPin.mapLookupStmt env k) @ s ; E {{ Φ }} := by
  iintro ⟨Hm, Hid, Hmb, Ht, Ho, Hcont⟩
  rw [QuorumPin.mapLookupStmt_eq]
  iapply (wp_stmt_op_first (op := .mapLookup (.int .uint64) (.defined ⟨"main.Index"⟩))
    (nt := 2) (e := .ref "idx") (rest := [.ref "ok", .var "m", .var "id"]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcm1
  iapply (wp_eval_ref hidx)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcm2
  iapply (wp_stmt_op_shift_target (loc := .base ta) (by simp) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcm3
  iapply (wp_eval_ref hok)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcm4
  iapply (wp_stmt_op_shift_target (loc := .base oa) (by simp) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcm5
  iapply (wp_eval_var (cell := ⟨some (.defined ⟨"main.mapAckIndexer"⟩),
    .map ⟨some (.base mba)⟩⟩) hm)
  isplitl [Hm]
  · iexact Hm
  iintro Hm
  iapply (wp_stmt_op_shift_plain (by simp))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcm6
  iapply (wp_eval_var (cell := ⟨some (.int .uint64), .int 3 .uint64⟩) hid)
  isplitl [Hid]
  · iexact Hid
  iintro Hid
  iapply (wp_map_lookup (mba := mba) (ta := ta) (oa := oa)
    (mty := some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)))
    (entries := #[(.int 3 .uint64, .int 12 .uint64)])
    (key := .int 3 .uint64) (val := .int 12 .uint64) (b := true)
    (tcell := ⟨some (.int .uint64), .int 0 .uint64⟩)
    (tcell' := ⟨some (.int .uint64), .int 12 .uint64⟩)
    (ocell := ⟨some .bool, .bool false⟩)
    (ocell' := ⟨some .bool, .bool true⟩)
    (hkey := fun σ => by
      have n3 : IntKind.uint64.normalize 3 = 3 := by rfl
      simp [normalizeValueForTy, normalizeValueForTyFuel, n3])
    (hpair := fun σ hl => by
      simp [mapLookupValue, mapEntries, loadLoc, hl, mapEntryIndex?, valueEq,
        valueEqFuel, checkKeyHashable, valueHashability, Bind.bind, Except.bind])
    (hstoret := fun σ hl => storeLoc_int_any hl 12)
    (hstoreo := fun σ hl => by
      simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind]))
  isplitl [Hmb]
  · iexact Hmb
  isplitl [Ht]
  · iexact Ht
  isplitl [Ho]
  · iexact Ho
  iintro ⟨Hmb, Ht, Ho⟩
  iapply Hcont $$ [$Hm $Hid $Hmb $Ht $Ho]

end

/-! ## Why there is no `wp_call_dynamic_enter` here (the recorded blocker)

Kernel-checked demonstration that frame entry into this program depends on
`σ.types`, which the state interpretation does not pin: the SAME value at
the SAME declared type normalizes differently in two states that agree on
`functions` and `methods`. `bindParams` (every quorum entry point has a
`.defined`-typed parameter), `allocDecls` (`$res0 : main.Index`), and
`concreteMethodForDynamic?` (receiver canonicalization) all route through
this. A `∀ σ, σ.functions = … → σ.methods = … → …` premise about any of
them is therefore FALSE, and a law carrying one would be vacuous. -/
theorem typeEnv_pin_is_load_bearing :
    TypeEnv.lookup GoldenQuorum.quorumLowered.typeDefs.toList ⟨"main.Index"⟩
        = some (.defined (.int .uint64))
      ∧ (normalizeValueForTy ({ types := [] } : ExecState)
          (.defined ⟨"main.Index"⟩) (.int 5 .uint64)).toOption = none
      ∧ (normalizeValueForTy
          ({ types := [(⟨"main.Index"⟩, .defined (.int .uint64))] } : ExecState)
          (.defined ⟨"main.Index"⟩) (.int 5 .uint64)).toOption
        = some (.int 5 .uint64) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp +decide [normalizeValueForTy, normalizeValueForTyFuel, TypeEnv.lookup,
      typeResolutionFuel, Except.toOption]
  · have n5 : IntKind.uint64.normalize 5 = 5 := by rfl
    simp +decide [normalizeValueForTy, normalizeValueForTyFuel, TypeEnv.lookup,
      typeResolutionFuel, Except.toOption, n5]

end GoLean.Iris
