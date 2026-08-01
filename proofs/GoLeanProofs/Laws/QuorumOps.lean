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
import GoLeanProofs.Laws.Call
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

The operand walk (`wp_stmt_op_first`/the shifts) is shared by every wide
op, allocating or not.

## Dynamic-dispatch frame entry (the blocker this file used to record)

5. **`wp_call_dynamic_enter₂`** — frame entry through an interface
   ANCHOR (`Laws/Call.lean` holds the general law; the witness on the
   REAL `main.AckedIndexer.AckedIndex` anchor is here). This was
   BLOCKED when the file was written: `GoCoreGS` pinned `σ.functions`
   and `σ.methods` but not `σ.types`, while `bindParams` (normalizes at
   the DECLARED parameter type), `allocDecls` (defaults results at
   theirs) and `concreteMethodForDynamic?` (canonicalizes the receiver,
   always a defined type) all resolve `.defined` names through
   `TypeEnv.lookup σ.types` and FAIL CLOSED on an unknown name — so a
   house-style `∀ σ, σ.functions = … → σ.methods = … → …` premise about
   any of them was FALSE and the law would have been vacuous.
   `typeEnv_pin_is_load_bearing` below is the kernel-checked
   demonstration; it now stands as the REGRESSION GUARD on the fix
   (`GoCoreGS.types` + the state-interpretation conjunct, 2026-07-31).

A second blocker surfaced and was fixed in the same slice: `Ty` derived
its `BEq` and, being a NESTED inductive, got an OPAQUE equality function
— unreasonable-about in the kernel, so no dispatch fact was provable at
all. `Ty.eqb` (`GoLean/GoCore/Value.lean`) is the total transparent
replacement; the differential is unchanged by it.

6. **The ALLOCATING apply core** (§2b, added by the summit slice
   2026-07-31): wide ops that allocate a fresh cell INSIDE `applyStmtOp`
   and publish a handle to it in their target — `wp_stmt_op_apply_alloc_store`
   on the general `wp_alloc_store_step` core (`Lifting.lean`), with
   `wp_make_map` and `wp_make_slice` as its two instances. `newValue` and
   `appendSlice`'s spill path are the same shape and stay owed (no walk
   forces them yet).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris

set_option linter.unusedSimpArgs false

/-! ## Environment algebra the multi-declaration walks need

`Laws/*` so far only ever resolved names in a CONCRETE environment
literal, where `rfl` suffices. A walk through a body that DECLARES
variables carries `env.declare id ℓ` layers over a quantified `env`, so
resolution needs the three general equations below. Nothing about a
program appears; this is `LocalEnv`'s own algebra. -/

/-- A freshly declared name resolves to its new location. -/
@[go_walk_simp]
theorem lookup_declare_self {env : LocalEnv} {id : String} {l : Loc} :
    LocalEnv.lookup (env.declare id l) id = some l := by
  cases env <;> simp [LocalEnv.declare, LocalEnv.lookup, Scope.lookup]

/-- Declaring a DIFFERENT name leaves a resolution unchanged. -/
@[go_walk_simp]
theorem lookup_declare_ne {env : LocalEnv} {id id' : String} {l : Loc}
    (hne : (id' == id) = false) :
    LocalEnv.lookup (env.declare id' l) id = LocalEnv.lookup env id := by
  cases env <;> simp [LocalEnv.declare, LocalEnv.lookup, Scope.lookup, hne]

/-- Entering a block (an empty pushed scope) leaves resolutions unchanged. -/
@[go_walk_simp]
theorem lookup_pushScope {env : LocalEnv} {id : String} :
    LocalEnv.lookup env.pushScope id = LocalEnv.lookup env id := by
  simp [LocalEnv.pushScope, LocalEnv.lookup, Scope.lookup]

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
  intro σ₁ _hfns _hmeths _htypes
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
@[go_walk_law]
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
@[go_walk_law]
theorem wp_stmt_op_shift_target {op : StmtOp} {nt : Nat} {done : List GoValue}
    {v : GoValue} {loc : Loc} {e : Expr} {rest : List Expr} {env k}
    (hnt : done.length < nt) (hloc : valueAsLoc v = .ok loc) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE e env (.stmtOpK op nt (v :: done) rest env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.retV v (.stmtOpK op nt done (e :: rest) env k)) @ s ; E {{ Φ }} :=
  wp_pure_det rfl trivial (fun _ => Step.stmtOpShiftTarget hnt hloc)

/-- Shift to the next operand past the target prefix (a plain value
operand — no address check). -/
@[go_walk_law]
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
    (happly : ∀ (σ : ExecState) (ch : Choices), σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base a) = some oldcell →
      applyStmtOp σ ch op nt (v :: done).reverse
        = .ok ({ σ with heap := Heap.set σ.heap (.base a) newcell }, ch)) :
    a.id ↦ oldcell ∗ (a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV v (.stmtOpK op nt done [] env k)) @ s ; E {{ Φ }} := by
  iapply wp_store_step (hnv := rfl)
  intro σ₁ hfns hmeths htypes hlook
  refine ⟨Step.stmtOpApply (ch := []) (happly σ₁ [] htypes hlook), ?_⟩
  intro c' s' hst
  cases hst with
  | @stmtOpApply _ _ _ _ _ _ _ _ ch _ hap =>
    rw [happly σ₁ ch htypes hlook] at hap
    injection hap with hap
    exact ⟨rfl, (Prod.mk.inj hap).1.symm⟩
  | @stmtOpApplyPanic _ _ _ _ _ _ _ _ ch hap =>
    rw [happly σ₁ ch htypes hlook] at hap
    exact absurd hap (by simp)

/-! ## 2b. The ALLOCATING apply step (`makeMap`, `makeSlice`, `newValue`)

The wide ops that allocate a fresh cell *inside* `applyStmtOp` and then
publish a handle to it in their target — the class the earlier slices
recorded as owed. One core (`wp_alloc_store_step`, `Lifting.lean`) and
two instances; the continuation quantifies over the machine's chosen
address, as everywhere fresh cells appear. -/

/-- **The apply step, allocate-and-store form**: the last operand arrives
and ONE step allocates `fcell` at a fresh address and writes the target
cell (whose new content may name that address — hence `newcell : Addr →
HeapCell`). `happly` is the wide op's cell-conditioned transition, in the
`wp_stmt_op_apply_store` style, additionally given that the target is not
the fresh address (true because it is already mapped). -/
theorem wp_stmt_op_apply_alloc_store {op : StmtOp} {nt : Nat}
    {done : List GoValue} {v : GoValue} {a : Addr} {fcell oldcell : HeapCell}
    (newcell : Addr → HeapCell) {env k}
    (happly : ∀ (σ : ExecState) (ch : Choices), σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base a) = some oldcell →
      a.id ≠ σ.nextAddr →
      applyStmtOp σ ch op nt (v :: done).reverse
        = .ok ({ σ with
                 heap := Heap.set (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) fcell)
                           (.base a) (newcell ⟨σ.nextAddr⟩),
                 nextAddr := σ.nextAddr + 1 }, ch)) :
    a.id ↦ oldcell
      ∗ iprop(∀ fa : Addr, fa.id ↦ fcell ∗ a.id ↦ newcell fa -∗
          WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV v (.stmtOpK op nt done [] env k)) @ s ; E {{ Φ }} := by
  iapply (wp_alloc_store_step newcell (hnv := rfl))
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

/-- **`m = make(map[K]V)`** as ONE step: allocate the map's data cell
(empty, and UNTYPED — `applyStmtOp` allocates it with no declared type)
and store a map handle naming it into the target. `hstore` is the
cell-conditioned store fact, quantified over the fresh address because
the stored value names it; the target's declared type is whatever the
lowering gave it, so the coercion is the caller's to discharge (at a
`.defined` map type it resolves through `σ.types` — hence the pin). -/
theorem wp_make_map {a : Addr} {oldcell : HeapCell} (newcell : Addr → HeapCell)
    {env k}
    (hstore : ∀ (σ : ExecState) (fa : Addr), σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base a) = some oldcell →
      storeLoc σ (.base a) (.map ⟨some (.base fa)⟩)
        = .ok { σ with heap := Heap.set σ.heap (.base a) (newcell fa) }) :
    a.id ↦ oldcell
      ∗ iprop(∀ fa : Addr, fa.id ↦ (⟨none, .mapData #[]⟩ : HeapCell)
          ∗ a.id ↦ newcell fa -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.addr (.base a))
            (.stmtOpK (.makeMap false) 1 [] [] env k)) @ s ; E {{ Φ }} := by
  iapply (wp_stmt_op_apply_alloc_store (done := [])
    (fcell := (⟨none, .mapData #[]⟩ : HeapCell)) newcell)
  intro σ ch htypes hlook hne
  have hlook' : Heap.lookup
      (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨none, .mapData #[]⟩) (.base a)
      = some oldcell := by
    have := heap_lookup_set_base_ne (h := σ.heap) (n := a.id)
      (b := (⟨σ.nextAddr⟩ : Addr)) (c := (⟨none, .mapData #[]⟩ : HeapCell))
      (fun he => hne he.symm)
    simpa using this.trans (by simpa using hlook)
  have hst := hstore { σ with
      heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨none, .mapData #[]⟩,
      nextAddr := σ.nextAddr + 1 } ⟨σ.nextAddr⟩ htypes hlook'
  simp [applyStmtOp, valueAsLoc, ExecState.alloc, ExecState.freshLoc, hst,
    Bind.bind, Except.bind]

/-- **`s = make([]T, n)`** as ONE step: allocate the backing array (the
default value at `[n]T`) and store a slice handle over it. Same core as
`wp_make_map`; `hbacking` is the machine's own default-array computation
(state-quantified under the type pin — `buildDefaultArrayValue` resolves
named element types) and `hstore` the cell-conditioned store. The length
operand is delivered as an `Int`; `hlen` fixes its non-negative reading,
which is what makes the `makeslice` bounds checks pass. -/
theorem wp_make_slice {elem : Ty} {a : Addr} {n : Nat} {oldcell : HeapCell}
    {backing : GoValue} (newcell : Addr → HeapCell) {env k}
    (hbacking : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      buildDefaultArrayValue σ n elem = .ok backing)
    (hstore : ∀ (σ : ExecState) (fa : Addr), σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base a) = some oldcell →
      storeLoc σ (.base a)
          (.slice { base := some (.base fa), offset := 0, len := n, cap := n })
        = .ok { σ with heap := Heap.set σ.heap (.base a) (newcell fa) }) :
    a.id ↦ oldcell
      ∗ iprop(∀ fa : Addr, fa.id ↦ (⟨some (.array n elem), backing⟩ : HeapCell)
          ∗ a.id ↦ newcell fa -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.int (Int.ofNat n) .int)
            (.stmtOpK (.makeSlice elem false) 1 [.addr (.base a)] [] env k))
          @ s ; E {{ Φ }} := by
  iapply (wp_stmt_op_apply_alloc_store (done := [.addr (.base a)])
    (fcell := (⟨some (.array n elem), backing⟩ : HeapCell)) newcell)
  intro σ ch htypes hlook hne
  have hlook' : Heap.lookup
      (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨some (.array n elem), backing⟩)
      (.base a) = some oldcell := by
    have := heap_lookup_set_base_ne (h := σ.heap) (n := a.id)
      (b := (⟨σ.nextAddr⟩ : Addr))
      (c := (⟨some (.array n elem), backing⟩ : HeapCell))
      (fun he => hne he.symm)
    simpa using this.trans (by simpa using hlook)
  have hst := hstore { σ with
      heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨some (.array n elem), backing⟩,
      nextAddr := σ.nextAddr + 1 } ⟨σ.nextAddr⟩ htypes hlook'
  have hn : ¬ ((n : Int) < 0) := by omega
  simp [applyStmtOp, valueAsLoc, valueAsInt, natFromNonnegativeInt, hn,
    hbacking σ htypes, ExecState.alloc, ExecState.freshLoc, hst,
    Bind.bind, Except.bind]

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
    (happly : ∀ (σ : ExecState) (ch : Choices), σ.types = GoCoreGS.types GF →
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
    (hred : ∀ σ₁ : ExecState, σ₁.functions = GoCoreGS.prog GF →
      σ₁.methods = GoCoreGS.methods GF → σ₁.types = GoCoreGS.types GF →
      ta.id ≠ oa.id →
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
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
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
        GoPrimStep.step (hred σ₁ hfns hmeths htypes Hne hlookr hlookt hlooko).1⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    obtain ⟨rfl, rfl⟩ :=
      (hred σ₁ hfns hmeths htypes Hne hlookr hlookt hlooko).2 _ _ st
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
        exact ⟨hfns, hmeths, htypes, (hwf.set_existing hlookt).set_existing hy⟩
    · isplitl [Hr Ht Ho Hcont]
      · iapply Hcont $$ [$Hr $Ht $Ho]
      · itrivial

/-- **The apply step, one-read/two-write form** — the wide-op face of
`wp_read_store_step₂` (the `mapLookup`/`typeAssertStmt` shape: two target
cells written, one state cell read). -/
theorem wp_stmt_op_apply_read_store₂ {op : StmtOp} {nt : Nat} {done : List GoValue}
    {v : GoValue} {ra ta oa : Addr}
    {rcell tcell tcell' ocell ocell' : HeapCell} {env k}
    (happly : ∀ (σ : ExecState) (ch : Choices), σ.functions = GoCoreGS.prog GF →
      σ.methods = GoCoreGS.methods GF → σ.types = GoCoreGS.types GF →
      ta.id ≠ oa.id →
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
  intro σ₁ hfns hmeths htypes hne hlookr hlookt hlooko
  refine ⟨Step.stmtOpApply (ch := [])
    (happly σ₁ [] hfns hmeths htypes hne hlookr hlookt hlooko), ?_⟩
  intro c' s' hst
  cases hst with
  | @stmtOpApply _ _ _ _ _ _ _ _ ch _ hap =>
    rw [happly σ₁ ch hfns hmeths htypes hne hlookr hlookt hlooko] at hap
    injection hap with hap
    exact ⟨rfl, (Prod.mk.inj hap).1.symm⟩
  | @stmtOpApplyPanic _ _ _ _ _ _ _ _ ch hap =>
    rw [happly σ₁ ch hfns hmeths htypes hne hlookr hlookt hlooko] at hap
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
    (hkey : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ keyTy keyV = .ok key)
    (hpair : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base mba) = some ⟨mty, .mapData entries⟩ →
      mapLookupValue σ ⟨some (.base mba)⟩ key keyTy valTy = .ok (val, b))
    (hstoret : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base ta) = some tcell →
      storeLoc σ (.base ta) val
        = .ok { σ with heap := Heap.set σ.heap (.base ta) tcell' })
    (hstoreo : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base oa) = some ocell →
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
  intro σ ch hfns hmeths htypes hne hlookm hlookt hlooko
  have hlooko' : Heap.lookup (Heap.set σ.heap (.base ta) tcell') (.base oa)
      = some ocell := by
    rw [heap_lookup_set_base_ne (b := ta) (n := oa.id) hne]
    exact hlooko
  have hstore2 := hstoreo { σ with heap := Heap.set σ.heap (.base ta) tcell' }
    htypes hlooko'
  simp [applyStmtOp, valueAsMap, valueAsLoc, hkey σ htypes, hpair σ htypes hlookm,
    hstoret σ htypes hlookt, hstore2, Bind.bind, Except.bind]

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

/-- Fallback for the projections below — never selected on the pin (each
`*_find` lemma below is `rfl`-checked against `quorumLowered`). -/
def missingFunc : Func :=
  { id := ⟨"$absent"⟩, args := #[], results := #[], body := .seqn #[] }

/-- The interface ANCHOR `Func` — `main.AckedIndexer.AckedIndex`, the
bodiless dispatch target the callsite names. -/
def ackedIndexAnchor : Func :=
  (findFunctionIn? quorumLowered.funcs ⟨"main.AckedIndexer.AckedIndex"⟩).getD
    missingFunc

/-- The CONCRETE implementation `main.mapAckIndexer.AckedIndex`. -/
def ackedIndexImpl : Func :=
  (findFunctionIn? quorumLowered.funcs ⟨"main.mapAckIndexer.AckedIndex"⟩).getD
    missingFunc

theorem ackedIndexAnchor_find :
    findFunctionIn? quorumLowered.funcs ⟨"main.AckedIndexer.AckedIndex"⟩
      = some ackedIndexAnchor := rfl

theorem ackedIndexImpl_find :
    findFunctionIn? quorumLowered.funcs ⟨"main.mapAckIndexer.AckedIndex"⟩
      = some ackedIndexImpl := rfl

theorem ackedIndexAnchor_args : ackedIndexAnchor.args.size = 2 := rfl

theorem ackedIndexImpl_args :
    ackedIndexImpl.args = #[⟨"m", .defined ⟨"main.mapAckIndexer"⟩⟩,
                            ⟨"id", .int .uint64⟩] := rfl

/-! The pinned program's TYPE ENVIRONMENT entries, `rfl`-projected. These
keep `simp` off the 1400-line program literal: every resolution of a named
type in a witness goes through one of these. -/

theorem typeEnv_Index :
    TypeEnv.lookup quorumLowered.typeDefs.toList ⟨"main.Index"⟩
      = some (.defined (.int .uint64)) := rfl

theorem typeEnv_mapAckIndexer :
    TypeEnv.lookup quorumLowered.typeDefs.toList ⟨"main.mapAckIndexer"⟩
      = some (.defined (.map (.int .uint64) (.defined ⟨"main.Index"⟩))) := rfl

theorem typeEnv_structEmpty :
    TypeEnv.lookup quorumLowered.typeDefs.toList ⟨"struct{}"⟩
      = some (.struct #[]) := rfl

theorem typeEnv_MajorityConfig :
    TypeEnv.lookup quorumLowered.typeDefs.toList ⟨"main.MajorityConfig"⟩
      = some (.defined (.map (.int .uint64) (.defined ⟨"struct{}"⟩))) := rfl

/-- The pinned METHOD TABLE, as a literal (so `simp` can run the
`methodInfoByFuncId?`/`concreteMethodForDynamic?` folds). -/
theorem quorumMethods_eq :
    quorumLowered.methods =
      #[{ name := "AckedIndex", funcId := ⟨"main.AckedIndexer.AckedIndex"⟩,
          recv := .interface ⟨"main.AckedIndexer"⟩ },
        { name := "AckedIndex", funcId := ⟨"main.mapAckIndexer.AckedIndex"⟩,
          recv := .defined ⟨"main.mapAckIndexer"⟩ },
        { name := "Slice", funcId := ⟨"main.MajorityConfig.Slice"⟩,
          recv := .defined ⟨"main.MajorityConfig"⟩ },
        { name := "CommittedIndex", funcId := ⟨"main.MajorityConfig.CommittedIndex"⟩,
          recv := .defined ⟨"main.MajorityConfig"⟩ }] := rfl

/-- Reflexivity of `BEq Ty` at the receiver type the dispatch compares.

Docstring corrected 2026-07-31 (pre-merge audit, finding 11 — it was
stale at birth, written in the very commit that changed the fact): `Ty`
no longer `deriving BEq`. Its instance is the hand-written, TOTAL,
transparent `Ty.eqb` (`GoLean/GoCore/Value.lean`, see this file's module
header), so `rfl` closes this goal too — `decide` is no longer the only
route. `simp` still makes no progress on it, and generic reflexivity
`∀ t, t == t` is still not a theorem — but for a NEW reason: `Ty.eqb` is
FUEL-BOUNDED (`tyEqFuel`) and answers `false` on exhaustion, so
reflexivity holds only below the fuel depth, which is why the dispatch
facts stay per-instance. -/
theorem beq_mapAckIndexer_self :
    ((Ty.defined ⟨"main.mapAckIndexer"⟩) == (Ty.defined ⟨"main.mapAckIndexer"⟩))
      = true := by decide

theorem ackedIndexAnchor_id :
    ackedIndexAnchor.id = ⟨"main.AckedIndexer.AckedIndex"⟩ := rfl

theorem ackedIndexImpl_results :
    ackedIndexImpl.results = #[⟨"$res0", .defined ⟨"main.Index"⟩⟩,
                               ⟨"$res1", .bool⟩] := rfl

theorem sortStmt_eq : sortStmt = .sortSlice (.var "srt") (.int .uint64) := rfl

theorem rangeStmt_eq :
    rangeStmt = .mapRange (some "id") none (.var "c") (.int .uint64)
      (.defined ⟨"struct{}"⟩) rangeBody := rfl

theorem mapLookupStmt_eq :
    mapLookupStmt = .mapLookup (.var "idx") (.var "ok") (.var "m") (.var "id")
      (.int .uint64) (.defined ⟨"main.Index"⟩) := rfl

/-- The CONCRETE method's whole body, `rfl`-projected out of the pin: a
declaration-free block of two sequences — declare `idx : main.Index` and
`ok : bool`, the comma-ok read, then the two result writes and `return`.
Edit the pin and this stops being `rfl`. -/
theorem ackedIndexImpl_body_eq :
    ackedIndexImpl.body = .block #[]
      #[.seqn #[.initialization ⟨"idx", .defined ⟨"main.Index"⟩⟩,
                .initialization ⟨"ok", .bool⟩,
                mapLookupStmt],
        .seqn #[.assign (.var "$res0") (.var "idx"),
                .assign (.var "$res1") (.var "ok"),
                .returnStmt]] := rfl

/-! ### The whole driver chain, `rfl`-projected out of the pin

`committedOneKnown → run → main.MajorityConfig.CommittedIndex` — the three
function bodies the summit walk traverses, each split into the statements
the walk steps through. Every lemma below is `rfl` against
`GoldenQuorum.quorumLowered`: edit the pin and they stop compiling, which
is the whole point of naming them rather than inlining literals. -/

def committedIndexImpl : Func :=
  (findFunctionIn? quorumLowered.funcs ⟨"main.MajorityConfig.CommittedIndex"⟩).getD
    missingFunc

def runImpl : Func :=
  (findFunctionIn? quorumLowered.funcs ⟨"run"⟩).getD missingFunc

def oneKnownImpl : Func :=
  (findFunctionIn? quorumLowered.funcs ⟨"committedOneKnown"⟩).getD missingFunc

theorem committedIndexImpl_find :
    findFunctionIn? quorumLowered.funcs ⟨"main.MajorityConfig.CommittedIndex"⟩
      = some committedIndexImpl := rfl

theorem runImpl_find :
    findFunctionIn? quorumLowered.funcs ⟨"run"⟩ = some runImpl := rfl

theorem oneKnownImpl_find :
    findFunctionIn? quorumLowered.funcs ⟨"committedOneKnown"⟩
      = some oneKnownImpl := rfl

theorem committedIndexImpl_args :
    committedIndexImpl.args = #[⟨"c", .defined ⟨"main.MajorityConfig"⟩⟩,
                                ⟨"l", .interface ⟨"main.AckedIndexer"⟩⟩] := rfl

theorem committedIndexImpl_results :
    committedIndexImpl.results = #[⟨"$res0", .defined ⟨"main.Index"⟩⟩] := rfl

theorem runImpl_args :
    runImpl.args = #[⟨"c", .defined ⟨"main.MajorityConfig"⟩⟩,
                     ⟨"l", .defined ⟨"main.mapAckIndexer"⟩⟩] := rfl

theorem runImpl_results :
    runImpl.results = #[⟨"$res0", .int .uint64⟩] := rfl

theorem oneKnownImpl_args : oneKnownImpl.args = #[] := rfl

theorem oneKnownImpl_results :
    oneKnownImpl.results = #[⟨"$res0", .int .uint64⟩] := rfl

theorem committedIndexImpl_body_eq :
    committedIndexImpl.body = .block #[] committedIndexStmts := rfl

/-! The nine statements of `CommittedIndex`, in order. -/

def ciLenStmt : Stmt := (committedIndexStmts[0]?).getD (.seqn #[])
def ciEmptyIf : Stmt := (committedIndexStmts[1]?).getD (.seqn #[])
def ciStkDecl : Stmt := (committedIndexStmts[2]?).getD (.seqn #[])
def ciSrtDecl : Stmt := (committedIndexStmts[3]?).getD (.seqn #[])
def ciFitIf : Stmt := (committedIndexStmts[4]?).getD (.seqn #[])
def ciLoopBlock : Stmt := (committedIndexStmts[5]?).getD (.seqn #[])
def ciPosStmt : Stmt := (committedIndexStmts[7]?).getD (.seqn #[])
def ciResStmt : Stmt := (committedIndexStmts[8]?).getD (.seqn #[])

theorem committedIndexStmts_toList :
    committedIndexStmts.toList =
      [ciLenStmt, ciEmptyIf, ciStkDecl, ciSrtDecl, ciFitIf, ciLoopBlock,
       sortStmt, ciPosStmt, ciResStmt] := rfl

theorem ciLenStmt_eq :
    ciLenStmt = .seqn #[.initialization ⟨"n", .int .int⟩,
      .assign (.var "n")
        (.length (.var "c") (some (.defined ⟨"main.MajorityConfig"⟩)))] := rfl

theorem ciEmptyIf_eq :
    ciEmptyIf = .ifThenElse (.eqCmp (.int .int) (.var "n") (.intLit 0 .int))
      (.block #[] #[.seqn #[.assign (.var "$res0")
        (.intLit 18446744073709551615 .uint64), .returnStmt]])
      (.seqn #[]) := rfl

theorem ciStkDecl_eq :
    ciStkDecl = .seqn #[.initialization ⟨"stk", .array 7 (.int .uint64)⟩] := rfl

theorem ciSrtDecl_eq :
    ciSrtDecl = .seqn #[.initialization ⟨"srt", .slice (.int .uint64)⟩] := rfl

/-- The `len(stk) >= n` fit test. The TAKEN branch reslices the on-stack
array (`srt = stk[:n]`); the other allocates (`make([]uint64, n)`). -/
theorem ciFitIf_eq :
    ciFitIf = .ifThenElse (.atLeastCmp (.intLit 7 .int) (.var "n"))
      (.block #[] #[.seqn #[.assign (.var "srt")
        (.slice (.ref "stk") (.intLit 0 .int) (.var "n") none)]])
      (.block #[]
        #[.seqn #[.initialization ⟨"$c2", .slice (.int .uint64)⟩,
                  .makeSlice (.var "$c2") (.int .uint64) (.var "n") none],
          .seqn #[.assign (.var "srt") (.var "$c2")]]) := rfl

/-- `$c2 = make([]uint64, n)` — the heap-allocating branch of the fit
test (`len(stk) >= n` false). Not on the `n = 1` path, which is exactly
why it is the right subject for the `makeSlice` witness: the law must be
discharged on a real statement even where the summit walk does not go. -/
def ciMakeSliceStmt : Stmt :=
  match ciFitIf with
  | .ifThenElse _ _ (.block _ inner) =>
      match (inner[0]?).getD (.seqn #[]) with
      | .seqn arr => (arr[1]?).getD (.seqn #[])
      | _ => .seqn #[]
  | _ => .seqn #[]

theorem ciMakeSliceStmt_eq :
    ciMakeSliceStmt = .makeSlice (.var "$c2") (.int .uint64) (.var "n") none :=
  rfl

def ciIDecl : Stmt :=
  .seqn #[.initialization ⟨"i", .int .int⟩,
          .assign (.var "i") (.sub (.var "n") (.intLit 1 .int))]

theorem ciLoopBlock_eq : ciLoopBlock = .block #[] #[ciIDecl, rangeStmt] := rfl

def ciCallSeq : Stmt :=
  .seqn #[.initialization ⟨"idx", .defined ⟨"main.Index"⟩⟩,
          .initialization ⟨"ok", .bool⟩,
          .call #[.var "idx", .var "ok"] ⟨"main.AckedIndexer.AckedIndex"⟩
            #[.var "l", .var "id"]]

def ciOkThen : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "srt") (.var "i")))
                (.convert (.int .uint64) (.var "idx"))],
      .assign (.var "i") (.sub (.var "i") (.intLit 1 .int))]

def ciOkIf : Stmt := .ifThenElse (.var "ok") ciOkThen (.seqn #[])

theorem rangeBody_eq :
    rangeBody = .block #[] #[.block #[] #[ciCallSeq, ciOkIf]] := rfl

theorem ciPosStmt_eq :
    ciPosStmt = .seqn #[.initialization ⟨"pos", .int .int⟩,
      .assign (.var "pos")
        (.sub (.var "n") (.add (.div (.var "n") (.intLit 2 .int))
          (.intLit 1 .int)))] := rfl

theorem ciResStmt_eq :
    ciResStmt = .seqn #[.assign (.var "$res0")
        (.convert (.defined ⟨"main.Index"⟩) (.indexGet (.var "srt") (.var "pos"))),
      .returnStmt] := rfl

/-! `run`, the two-statement wrapper the driver calls. -/

def runCallSeq : Stmt :=
  .seqn #[.initialization ⟨"$c3", .defined ⟨"main.Index"⟩⟩,
          .call #[.var "$c3"] ⟨"main.MajorityConfig.CommittedIndex"⟩
            #[.var "c",
              .toInterface (.interface ⟨"main.AckedIndexer"⟩)
                (.defined ⟨"main.mapAckIndexer"⟩) (.var "l")]]

def runResSeq : Stmt :=
  .seqn #[.assign (.var "$res0") (.convert (.int .uint64) (.var "$c3")),
          .returnStmt]

theorem runImpl_body_eq : runImpl.body = .block #[] #[runCallSeq, runResSeq] := rfl

/-! `committedOneKnown`, the driver: build `MajorityConfig{1:{}}` and
`mapAckIndexer{1:12}`, call `run`, return. -/

def okCfgSeq : Stmt :=
  .seqn #[.initialization ⟨"$c10", .map (.int .uint64) (.defined ⟨"struct{}"⟩)⟩,
          .makeMap (.var "$c10") (.int .uint64) (.defined ⟨"struct{}"⟩) none,
          .mapAssign (.var "$c10") (.intLit 1 .uint64)
            (.structLit (.defined ⟨"struct{}"⟩) #[])
            (.int .uint64) (.defined ⟨"struct{}"⟩)]

def okAckSeq : Stmt :=
  .seqn #[.initialization ⟨"$c11", .map (.int .uint64) (.defined ⟨"main.Index"⟩)⟩,
          .makeMap (.var "$c11") (.int .uint64) (.defined ⟨"main.Index"⟩) none,
          .mapAssign (.var "$c11") (.intLit 1 .uint64) (.intLit 12 .uint64)
            (.int .uint64) (.defined ⟨"main.Index"⟩)]

def okCallSeq : Stmt :=
  .seqn #[.initialization ⟨"$c12", .int .uint64⟩,
          .call #[.var "$c12"] ⟨"run"⟩ #[.var "$c10", .var "$c11"]]

def okResSeq : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "$c12"), .returnStmt]

theorem oneKnownImpl_body_eq :
    oneKnownImpl.body = .block #[] #[okCfgSeq, okAckSeq, okCallSeq, okResSeq] :=
  rfl

/-- `var stk [7]uint64` — the on-stack scratch array's zero value, the
declaration's default (`majority.go`'s "use an on-stack slice to keep us
off the heap" trick, verbatim in the pin). -/
def stkZero : GoValue :=
  .array #[.int 0 .uint64, .int 0 .uint64, .int 0 .uint64, .int 0 .uint64,
           .int 0 .uint64, .int 0 .uint64, .int 0 .uint64]

/-- The same array after the single voter's index has been written at
slot 0 — the state `slices.Sort` then sorts (over a length-1 window, so
it is the sorted image too). -/
def stkOne (v : Int) : GoValue :=
  .array #[.int v .uint64, .int 0 .uint64, .int 0 .uint64, .int 0 .uint64,
           .int 0 .uint64, .int 0 .uint64, .int 0 .uint64]

/-- The declaration default at `[7]uint64`, computed. -/
theorem defaultValue_stk (σ : ExecState) :
    defaultValue σ (.array 7 (.int .uint64)) = .ok stkZero := by
  simp only [defaultValue, defaultValueFuel, typeResolutionFuel, stkZero,
    Bind.bind, Except.bind]
  rfl

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
      intro σ ch _ht hlook
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
`main.mapAckIndexer.AckedIndex`: the whole statement walk on a ONE-ENTRY
`uint64 → Index` map, key present, the stored index delivered with
`ok = true`.

Generic in the entry (`q ↦ v`, any representable `uint64`s) and in the
data cell's declared type — deliberately, per the standing
over-specialization check: the earlier form hard-coded `3 ↦ 12` and a
`some (.map …)`-typed data cell, neither of which is a property of Go.
`makeMap` allocates the data cell with NO declared type, so a walk over
the real driver could not have used the pinned-type version at all.

FAITHFUL TO THE PIN as of the `σ.types` pin (quorum pilot phase 4): the
`idx` target cell is declared `.defined main.Index`, exactly as the
lowering declares it — the store's coercion at that named type resolves
through `σ.types`, dischargeable now that the ghost state pins it. -/
@[go_walk_law]
theorem wp_map_lookup_ackedIndex {ma ida mba ta oa : Addr} {mty : Option Ty}
    {q v : Int} {env k}
    (htypes : GoCoreGS.types GF = GoldenQuorum.quorumLowered.typeDefs.toList)
    (hq : IntKind.uint64.normalize q = q)
    (hv : IntKind.uint64.normalize v = v)
    (hm : LocalEnv.lookup env "m" = some (.base ma))
    (hid : LocalEnv.lookup env "id" = some (.base ida))
    (hidx : LocalEnv.lookup env "idx" = some (.base ta))
    (hok : LocalEnv.lookup env "ok" = some (.base oa)) :
    ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
              .map ⟨some (.base mba)⟩⟩ : HeapCell)
      ∗ ida.id ↦ (⟨some (.int .uint64), .int q .uint64⟩ : HeapCell)
      ∗ mba.id ↦ (⟨mty, .mapData #[(.int q .uint64, .int v .uint64)]⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ oa.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                   .map ⟨some (.base mba)⟩⟩ : HeapCell)
          ∗ ida.id ↦ (⟨some (.int .uint64), .int q .uint64⟩ : HeapCell)
          ∗ mba.id ↦ (⟨mty, .mapData #[(.int q .uint64, .int v .uint64)]⟩ : HeapCell)
          ∗ ta.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int v .uint64⟩ : HeapCell)
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
  iapply (wp_eval_var (cell := ⟨some (.int .uint64), .int q .uint64⟩) hid)
  isplitl [Hid]
  · iexact Hid
  iintro Hid
  iapply (wp_map_lookup (mba := mba) (ta := ta) (oa := oa) (mty := mty)
    (entries := #[(.int q .uint64, .int v .uint64)])
    (key := .int q .uint64) (val := .int v .uint64) (b := true)
    (tcell := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (tcell' := ⟨some (.defined ⟨"main.Index"⟩), .int v .uint64⟩)
    (ocell := ⟨some .bool, .bool false⟩)
    (ocell' := ⟨some .bool, .bool true⟩)
    (hkey := fun σ _ht => by
      simp [normalizeValueForTy, normalizeValueForTyFuel, hq])
    (hpair := fun σ _ht hl => by
      simp [mapLookupValue, mapEntries, loadLoc, hl, mapEntryIndex?, valueEq,
        valueEqFuel, checkKeyHashable, valueHashability, Bind.bind, Except.bind])
    (hstoret := fun σ ht hl => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hl ⊢
      simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, hv, Bind.bind, Except.bind])
    (hstoreo := fun σ _ht hl => by
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

/-- **Witness for `wp_make_slice`** (and for the allocating apply core) on
the REAL `$c2 = make([]uint64, n)` of the pinned `CommittedIndex` — the
branch the on-stack scratch array normally avoids. At `n = 1`: the backing
array `[1]uint64` is allocated at a machine-chosen address and a slice
over it is stored in `$c2`. Every premise is discharged by computation. -/
theorem wp_make_slice_c2 {c2a na : Addr} {env k}
    (hres : LocalEnv.lookup env "$c2" = some (.base c2a))
    (hn : LocalEnv.lookup env "n" = some (.base na)) :
    c2a.id ↦ (⟨some (.slice (.int .uint64)),
               .slice ⟨none, 0, 0, 0⟩⟩ : HeapCell)
      ∗ na.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell)
      ∗ iprop(∀ fa : Addr,
          fa.id ↦ (⟨some (.array 1 (.int .uint64)),
                    .array #[.int 0 .uint64]⟩ : HeapCell)
            ∗ c2a.id ↦ (⟨some (.slice (.int .uint64)),
                         .slice ⟨some (.base fa), 0, 1, 1⟩⟩ : HeapCell)
            ∗ na.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell) -∗
          WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec QuorumPin.ciMakeSliceStmt env k) @ s ; E {{ Φ }} := by
  iintro ⟨Hc2, Hn, Hcont⟩
  rw [QuorumPin.ciMakeSliceStmt_eq]
  iapply (wp_stmt_op_first (op := .makeSlice (.int .uint64) false) (nt := 1)
    (e := .ref "$c2") (rest := [.var "n"]) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hm1
  iapply (wp_eval_ref hres)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hm2
  iapply (wp_stmt_op_shift_target (loc := .base c2a) (by simp) rfl)
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hm3
  iapply (wp_eval_var (a := na) (cell := ⟨some (.int .int), .int 1 .int⟩) hn)
  isplitl [Hn]
  · iexact Hn
  iintro Hn
  iapply (wp_make_slice (elem := .int .uint64) (a := c2a) (n := 1)
    (backing := .array #[.int 0 .uint64])
    (newcell := fun fa => ⟨some (.slice (.int .uint64)),
                           .slice ⟨some (.base fa), 0, 1, 1⟩⟩)
    (hbacking := fun σ _ht => by
      simp [buildDefaultArrayValue, buildArrayValue, defaultValue,
        defaultValueFuel, typeResolutionFuel, Bind.bind, Except.bind])
    (oldcell := ⟨some (.slice (.int .uint64)), .slice ⟨none, 0, 0, 0⟩⟩)
    (hstore := fun σ fa _ht hlk => by
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind]))
  isplitl [Hc2]
  · iexact Hc2
  iintro %fa ⟨Hfa, Hc2⟩
  iapply Hcont $$ %fa [$Hfa $Hc2 $Hn]

/-- **Witness for `wp_call_dynamic_enter₂`** on the REAL interface call
`l.AckedIndex(id)` of the pinned `CommittedIndex`: the callsite names the
ANCHOR `main.AckedIndexer.AckedIndex` (a bodiless `Func`), the receiver
arrives as an interface box with dynamic type
`.defined main.mapAckIndexer`, and ONE step redirects to
`main.mapAckIndexer.AckedIndex` with the receiver UNBOXED
(`needsDeref = false`), allocates the two parameter cells (normalized at
`.defined main.mapAckIndexer` and `uint64`) and the two result cells
(`$res0 : main.Index` defaulted to `0`, `$res1 : bool` to `false`), and
enters the implementation body.

EVERY premise is discharged by computation against `quorumLowered`; the
only external hypotheses are the three ghost-state pins. This is the law
the pre-`types`-pin ghost state made unstateable: `bindParams` normalizes
at `.defined main.mapAckIndexer` and `allocDecls` defaults at
`.defined main.Index`, both `TypeEnv.lookup σ.types` resolutions. -/
@[go_walk_law]
theorem wp_call_dynamic_enter_ackedIndex {mba : Addr} {n : Int}
    {locs : List Loc} {env k}
    (hprog : GoCoreGS.prog GF = GoldenQuorum.quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = GoldenQuorum.quorumLowered.methods)
    (htypes : GoCoreGS.types GF = GoldenQuorum.quorumLowered.typeDefs.toList) :
    iprop(∀ a₀ : Addr, ∀ a₁ : Addr, ∀ a₂ : Addr, ∀ a₃ : Addr,
        a₀.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                  .map ⟨some (.base mba)⟩⟩ : HeapCell)
          ∗ a₁.id ↦ (⟨some (.int .uint64),
                      .int (IntKind.uint64.normalize n) .uint64⟩ : HeapCell)
          ∗ a₂.id ↦ (⟨some (.defined ⟨"main.Index"⟩),
                      .int 0 .uint64⟩ : HeapCell)
          ∗ a₃.id ↦ (⟨some .bool, .bool false⟩ : HeapCell) -∗
        WP (Config.exec QuorumPin.ackedIndexImpl.body
              [[("$res1", Loc.base a₃), ("$res0", Loc.base a₂),
                ("id", Loc.base a₁), ("m", Loc.base a₀)]]
              (.frame locs [Loc.base a₂, Loc.base a₃] [] k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.int n .uint64)
            (.callArgsK ⟨"main.AckedIndexer.AckedIndex"⟩ locs
              [.interface (.defined ⟨"main.mapAckIndexer"⟩)
                (.map ⟨some (.base mba)⟩)] [] env k)) @ s ; E {{ Φ }} :=
  wp_call_dynamic_enter₂
    (anchor := QuorumPin.ackedIndexAnchor) (concrete := QuorumPin.ackedIndexImpl)
    (recv := .map ⟨some (.base mba)⟩)
    (hfind := by rw [hprog]; exact QuorumPin.ackedIndexAnchor_find)
    (hanchor := QuorumPin.ackedIndexAnchor_args)
    (hargs := QuorumPin.ackedIndexImpl_args)
    (hres := QuorumPin.ackedIndexImpl_results)
    (hrid := by decide)
    (hdisp := fun σ hf hm ht => by
      rw [execState_pin_eq (ht.trans htypes) (hf.trans hprog) (hm.trans hmeths)]
      simp +decide [dynamicDispatch?, methodInfoByFuncId?, methodRecvInterfaceName?,
        resolveDefinedAliases, resolveDefinedAliasesFuel,
        concreteMethodForDynamic?, methodRecvDynamicTy?, canonicalTy,
        canonicalTyFuel, typeResolutionFuel, QuorumPin.quorumMethods_eq,
        QuorumPin.typeEnv_mapAckIndexer,
        QuorumPin.ackedIndexAnchor_id, QuorumPin.ackedIndexImpl_find,
        QuorumPin.beq_mapAckIndexer_self,
        Bind.bind, Except.bind])
    (hnorm₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_mapAckIndexer])
    (hnorm₁ := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel])
    (hdef₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [defaultValue, defaultValueFuel, typeResolutionFuel,
        QuorumPin.typeEnv_Index])
    (hdef₁ := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel])

/-- **Witness for `wp_call_enter₂`** (the STATIC two-argument/two-result
frame entry) on the REAL `main.mapAckIndexer.AckedIndex` of the pinned
lowering, called on a CONCRETE receiver (no interface box, so
`dynamicDispatch?` must answer `none` — which it does because the
method's recorded receiver `.defined main.mapAckIndexer` resolves to a
map type, not an interface: the `methodRecvInterfaceName?` gate).

This is the entry the `GoFuncSpec2` discharge walks, and it is the exact
complement of `wp_call_dynamic_enter_ackedIndex`: same method, same
parameter/result cells, the other dispatch answer. Every premise is
discharged by computation against `quorumLowered`; the only external
hypotheses are the three ghost-state pins. -/
@[go_walk_law]
theorem wp_call_enter_ackedIndexImpl {mba : Addr} {n : Int}
    {locs : List Loc} {env k}
    (hprog : GoCoreGS.prog GF = GoldenQuorum.quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = GoldenQuorum.quorumLowered.methods)
    (htypes : GoCoreGS.types GF = GoldenQuorum.quorumLowered.typeDefs.toList) :
    iprop(∀ a₀ : Addr, ∀ a₁ : Addr, ∀ a₂ : Addr, ∀ a₃ : Addr,
        a₀.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                  .map ⟨some (.base mba)⟩⟩ : HeapCell)
          ∗ a₁.id ↦ (⟨some (.int .uint64),
                      .int (IntKind.uint64.normalize n) .uint64⟩ : HeapCell)
          ∗ a₂.id ↦ (⟨some (.defined ⟨"main.Index"⟩),
                      .int 0 .uint64⟩ : HeapCell)
          ∗ a₃.id ↦ (⟨some .bool, .bool false⟩ : HeapCell) -∗
        WP (Config.exec QuorumPin.ackedIndexImpl.body
              [[("$res1", Loc.base a₃), ("$res0", Loc.base a₂),
                ("id", Loc.base a₁), ("m", Loc.base a₀)]]
              (.frame locs [Loc.base a₂, Loc.base a₃] [] k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.int n .uint64)
            (.callArgsK ⟨"main.mapAckIndexer.AckedIndex"⟩ locs
              [.map ⟨some (.base mba)⟩] [] env k)) @ s ; E {{ Φ }} :=
  wp_call_enter₂
    (func := QuorumPin.ackedIndexImpl)
    (hfind := by rw [hprog]; exact QuorumPin.ackedIndexImpl_find)
    (hargs := QuorumPin.ackedIndexImpl_args)
    (hres := QuorumPin.ackedIndexImpl_results)
    (hrid := by decide)
    (hnodisp := fun σ hf hm ht => by
      rw [execState_pin_eq (ht.trans htypes) (hf.trans hprog) (hm.trans hmeths)]
      simp +decide [dynamicDispatch?, methodInfoByFuncId?, methodRecvInterfaceName?,
        resolveDefinedAliases, resolveDefinedAliasesFuel,
        QuorumPin.quorumMethods_eq, QuorumPin.typeEnv_mapAckIndexer,
        Bind.bind, Except.bind]
      -- the receiver resolves to a MAP type, never `.interface`, so both
      -- arms of the remaining match answer "no dynamic dispatch".
      split <;> rfl)
    (hnorm₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_mapAckIndexer])
    (hnorm₁ := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel])
    (hdef₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [defaultValue, defaultValueFuel, typeResolutionFuel,
        QuorumPin.typeEnv_Index])
    (hdef₁ := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel])

end

/-! ## The regression guard on the `σ.types` pin

Kernel-checked demonstration that frame entry into this program depends on
`σ.types`: the SAME value at the SAME declared type normalizes to `.ok`
under the program's type environment and to `unsupported` under an empty
one — two states that can agree on `functions` and `methods`.
`bindParams` (every quorum entry point has a `.defined`-typed parameter),
`allocDecls` (`$res0 : main.Index`), and `concreteMethodForDynamic?`
(receiver canonicalization) all route through it. This is why
`GoCoreGS.types` exists; delete the pin and the laws above become
vacuous, which is exactly what this theorem makes visible. -/
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
