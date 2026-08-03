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
import GoLeanProofs.Laws.Values

/-!
# Wide-statement (`stmtOpK`) laws — the `StmtOp` walk, and the ops it carries

GENERAL laws only (the layering doctrine,
`docs/2026-08-01_tcb-and-layering-doctrine.md` §2): every statement in
this module quantifies over programs, environments, cells and values —
no target name, pinned lowering, or program fragment appears. The
quorum witnesses that instantiate these laws on the pinned etcd-io/raft
lowering live in `Specs/GoldenQuorumPin.lean`. (History: this content
began as `Laws/QuorumOps.lean`, written for the `CommittedIndex` walk —
quorum pilot phase 4, 2026-07-31 — and was renamed/split at the
proof-automation arc's close-out because its laws were never
quorum-specific, only its witnesses.)

What lives here:

1. **`mapRangeSnapshot`** — the state-READING step that turns the ranged
   map value into the iteration snapshot (`Laws/Range` starts one step
   later, at `mapIterK`). Two forms: through a `.mapData` cell
   (`wp_map_range_snapshot`) and the nil map (`wp_map_range_snapshot_nil`,
   pure — the machine reads nothing).
2. **The wide-statement (`stmtOpK`) walk** — `wp_stmt_op_first`,
   `wp_stmt_op_shift_target`, `wp_stmt_op_shift_plain`, and the apply
   steps. Every wide statement (`sortSlice`, `mapLookup`, `makeSlice`,
   `appendSlice`, `mapAssign`, …) enters through these.
   2b. **The ALLOCATING apply core** — wide ops that allocate a fresh
   cell INSIDE `applyStmtOp` and publish a handle to it in their target:
   `wp_stmt_op_apply_alloc_store` on the general `wp_alloc_store_step`
   core (`Lifting.lean`), with `wp_make_map` and `wp_make_slice` as its
   two instances. `newValue` and `appendSlice`'s spill path are the same
   shape and stay owed (no walk forces them yet).
3. **`sortSlice`** (`wp_sort_slice`) — the `slices.Sort` extern. A slice's
   backing store is ONE heap cell holding an `.array`, so despite the
   multi-element read+write this is a single-cell step: the
   `wp_stmt_op_apply_store` core applies verbatim. The machine's
   transition at a SYMBOLIC length is `applyStmtOp_sortSlice_ints`
   (the two `for i in [:len]` loops by induction via
   `Laws/Values.forIn_range'_inv`).
4. **`mapLookup`** (`wp_map_lookup`) — the comma-ok read, a THREE-cell
   step (read the map's data cell, write the value target and the ok
   target); `wp_read_store_step₂` is the new core. The map-entry SEARCH
   at a symbolic entry array is characterized by
   `mapLookupValue_miss`/`mapLookupValue_hit` (via
   `forIn_find_none`/`forIn_find_some`).

The operand walk (`wp_stmt_op_first`/the shifts) is shared by every wide
op, allocating or not.
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

/-- **The machine's `slices.Sort` transition at a SYMBOLIC length.** A
slice over the first `vals.length` slots of a backing array whose
elements are normalized ints of one kind: the apply step replaces those
slots by the sorted image and leaves the tail alone. `hsorted` hands over
the sort's ANSWER — the machine sorts (`sortLe`) `(Int × IntKind)` pairs by
their `Int`, and any characterization of that list (e.g. via
sorted-permutation uniqueness) may be supplied. -/
theorem applyStmtOp_sortSlice_ints {σ : ExecState} {ch : Choices} {sta : Addr}
    {kind : IntKind} {cap : Nat} {vals sorted : List Int} {tail : List GoValue}
    (hcap : vals.length + tail.length = cap)
    (hnormv : ∀ v ∈ vals, kind.normalize v = v)
    (htail : ∀ x ∈ tail, ∃ w : Int, x = .int w kind ∧ kind.normalize w = w)
    (hsorted : sortLe (fun a b => decide (a.1 ≤ b.1)) (vals.map (fun v => (v, kind)))
      = sorted.map (fun v => (v, kind)))
    (hlook : Heap.lookup σ.heap (.base sta)
      = some (intArrayCell cap kind (intVals kind vals ++ tail))) :
    applyStmtOp σ ch (.sortSlice (.int kind)) 0
        [.slice ⟨some (.base sta), 0, vals.length, cap⟩]
      = .ok ({ σ with heap := Heap.set σ.heap (.base sta)
                        (intArrayCell cap kind (intVals kind sorted ++ tail)) },
             ch) := by
  -- the sorted list is a permutation of the input, hence same length and
  -- same (normalized) elements
  have hperm : (sorted.map (fun v => (v, kind))).Perm (vals.map (fun v => (v, kind))) := by
    rw [← hsorted]; exact sortLe_perm _ _
  have hmem : ∀ v ∈ sorted, v ∈ vals := by
    intro v hv
    have hm : (v, kind) ∈ vals.map (fun v => (v, kind)) :=
      hperm.mem_iff.mp (List.mem_map_of_mem hv)
    obtain ⟨w, hw, hwe⟩ := List.mem_map.1 hm
    cases hwe; exact hw
  have hlens : sorted.length = vals.length := by
    have h := hperm.length_eq; simpa using h
  have hnorms : ∀ v ∈ sorted, kind.normalize v = v := fun v hv => hnormv v (hmem v hv)
  have hstage_len : ∀ i, i ≤ vals.length →
      (sortStage kind sorted vals tail i).length = cap := by
    intro i hi
    simp only [sortStage, intVals, List.length_append, List.length_map,
      List.length_take, List.length_drop]
    omega
  have hstage_norm : ∀ i, ∀ x ∈ sortStage kind sorted vals tail i,
      ∃ w : Int, x = .int w kind ∧ kind.normalize w = w := by
    intro i x hx
    simp only [sortStage, intVals, List.mem_append] at hx
    rcases hx with hx | hx | hx
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      exact ⟨v, rfl, hnorms v (List.mem_of_mem_take hv)⟩
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      exact ⟨v, rfl, hnormv v (List.mem_of_mem_drop hv)⟩
    · exact htail x hx
  have hstage0 : sortStage kind sorted vals tail 0 = intVals kind vals ++ tail := by
    simp [sortStage, intVals]
  have hstagen : sortStage kind sorted vals tail vals.length
      = intVals kind sorted ++ tail := by
    simp only [sortStage, intVals]
    rw [show sorted.take vals.length = sorted from by
      rw [← hlens]; exact List.take_length,
      show vals.drop vals.length = [] from List.drop_length]
    simp
  have hres : sortStageState σ sta cap kind sorted vals tail vals.length
      = { σ with
          heap := Heap.set σ.heap (.base sta)
            (intArrayCell cap kind (intVals kind sorted ++ tail)) } := by
    rw [sortStageState, hstagen]
  -- the operand, the slice validation, and the two `for i in [:len]` loops
  simp only [applyStmtOp, valueAsSlice, Std.Legacy.Range.forIn_eq_forIn_range',
    validateSlice, Bind.bind, Except.bind, pure, Except.pure,
    if_neg (show ¬ (vals.length > cap) by omega)]
  rw [show ([:vals.length] : Std.Legacy.Range).size = vals.length from by
    simp [Std.Legacy.Range.size]]
  -- LOOP 1 — load the visible elements
  rw [forIn_range'_inv (N := vals.length)
    (Q := fun i r => r = ((vals.take i).map (fun v => (v, kind))).toArray)
    (out := fun i r => r.push ((vals[i]!), kind))
    (res := (vals.map (fun v => (v, kind))).toArray) ?hload (by omega) (by simp)
    (by intro b' hb'; rw [hb']; simp)]
  · -- LOOP 2 — store the sorted image back
    dsimp only
    rw [hsorted]
    rw [forIn_range'_inv (N := vals.length) (n := vals.length) (j := 0) (b := σ)
      (Q := fun i b => b = sortStageState σ sta cap kind sorted vals tail i)
      (out := fun i _ => sortStageState σ sta cap kind sorted vals tail (i + 1))
      (res := sortStageState σ sta cap kind sorted vals tail vals.length)
      ?hstore (by omega) ?hinit (by intro b' h; rw [h, Nat.zero_add])]
    · rw [hres]
    · case hstore =>
        intro i b' hi hb'
        subst hb'
        have hilen : i < sorted.length := by omega
        have hget : (sorted.map (fun v => (v, kind))).toArray[i]?
            = some ((sorted[i]'hilen), kind) := by
          rw [Array.getElem?_eq_getElem (by simpa using hilen)]
          simp
        rw [hget]
        dsimp only
        rw [sliceIndexLoc_prefix hi (by omega)]
        dsimp only
        refine ⟨?_, rfl⟩
        have hilev : i < vals.length := hi
        have hdrop : intVals kind (vals.drop i)
            = GoValue.int (vals[i]'hilev) kind :: intVals kind (vals.drop (i + 1)) := by
          rw [intVals, intVals, List.drop_eq_getElem_cons hilev, List.map_cons]
        have hsplit : sortStage kind sorted vals tail i
            = intVals kind (sorted.take i)
                ++ (GoValue.int (vals[i]'hilev) kind
                    :: (intVals kind (vals.drop (i + 1)) ++ tail)) := by
          rw [sortStage, hdrop, List.cons_append]
        have htake : intVals kind (sorted.take (i + 1))
            = intVals kind (sorted.take i) ++ [GoValue.int (sorted[i]'hilen) kind] := by
          rw [intVals, intVals,
            show sorted.take (i + 1) = sorted.take i ++ [sorted[i]'hilen] from by
              rw [List.take_add_one, List.getElem?_eq_getElem hilen]; rfl,
            List.map_append]
          rfl
        have hsplit' : sortStage kind sorted vals tail (i + 1)
            = intVals kind (sorted.take i)
                ++ (GoValue.int (sorted[i]'hilen) kind
                    :: (intVals kind (vals.drop (i + 1)) ++ tail)) := by
          rw [sortStage, htake, List.append_assoc, List.cons_append, List.nil_append]
        have hlen : (intVals kind (sorted.take i)).length = i := by
          simp [intVals]; omega
        have hlk : Heap.lookup (sortStageState σ sta cap kind sorted vals tail i).heap
            (.base sta) = some (intArrayCell cap kind (sortStage kind sorted vals tail i)) := by
          rw [sortStageState]
          exact heap_lookup_set_base_self _ _ _
        have hset : arraySet (sortStage kind sorted vals tail i).toArray (Int.ofNat i)
            (GoValue.int (sorted[i]'hilen) kind)
            = .ok (sortStage kind sorted vals tail (i + 1)).toArray := by
          rw [hsplit, hsplit', Int.ofNat_eq_natCast]
          exact arraySet_middle' hlen.symm (by simp [coerceStoredValue, hnorms _ (List.getElem_mem hilen)])
        have hnormarr : normalizeValueForTy (sortStageState σ sta cap kind sorted vals tail i)
            (.array cap (.int kind)) (.array (sortStage kind sorted vals tail (i + 1)).toArray)
            = .ok (.array (sortStage kind sorted vals tail (i + 1)).toArray) :=
          normalizeValueForTy_intArray (hstage_len (i + 1) (by omega))
            (hstage_norm (i + 1))
        simp only [storeLoc, loadLoc, hlk, intArrayCell, hset, hnormarr,
          Bind.bind, Except.bind, pure, Except.pure]
        rw [sortStageState, sortStageState]
        simp only [heap_set_set_of_lookup hlook, intArrayCell]
    · case hinit =>
        rw [sortStageState, hstage0, heap_set_self_of_lookup hlook]
  · case hload =>
      intro i b' hi hb'
      subst hb'
      have hsplit : intVals kind vals ++ tail
          = intVals kind (vals.take i)
              ++ (GoValue.int (vals[i]'hi) kind
                  :: (intVals kind (vals.drop (i + 1)) ++ tail)) := by
        rw [intVals, intVals, intVals, list_map_split (fun v => GoValue.int v kind) vals i hi]
        simp
      have hlen : (intVals kind (vals.take i)).length = i := by
        simp [intVals]; omega
      have hload : loadLoc σ (.index (.base sta) (Int.ofNat i))
          = .ok (GoValue.int (vals[i]'hi) kind) := by
        simp only [loadLoc, hlook, intArrayCell, Bind.bind, Except.bind, pure,
          Except.pure, Int.ofNat_eq_natCast]
        rw [hsplit]
        exact arrayGet_middle' hlen.symm
      rw [sliceIndexLoc_prefix hi (by omega)]
      dsimp only
      rw [hload]
      have hval : vals[i]! = vals[i]'hi := getElem!_pos vals i hi
      rw [hval]
      refine ⟨rfl, ?_⟩
      simp only [List.map_take]
      rw [List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem hi]
      simp

/-- The default `[n]uint64` at a SYMBOLIC length: `n` zeros. -/
theorem buildDefaultArrayValue_int (σ : ExecState) (kind : IntKind) (n : Nat) :
    buildDefaultArrayValue σ n (.int kind)
      = .ok (.array (List.replicate n (.int 0 kind)).toArray) := by
  simp only [buildDefaultArrayValue, buildArrayValue,
    Std.Legacy.Range.forIn_eq_forIn_range', Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show ([:n] : Std.Legacy.Range).size = n from by simp [Std.Legacy.Range.size]]
  rw [forIn_range'_inv (N := n) (n := n) (j := 0) (b := (#[] : Array GoValue))
    (Q := fun i acc => acc = (List.replicate i (GoValue.int 0 kind)).toArray)
    (out := fun _ acc => acc.push (.int 0 kind))
    (res := (List.replicate n (GoValue.int 0 kind)).toArray)
    ?hfill (by omega) (by simp) (by intro b' h; rw [h, Nat.zero_add])]
  · rfl
  · case hfill =>
      intro i acc hi hacc
      refine ⟨by simp [defaultValue, defaultValueFuel, typeResolutionFuel], ?_⟩
      rw [hacc, List.replicate_succ']
      simp [← List.toArray_replicate]

/-- Go's `a[:n]` bounds check on a prefix of a long-enough array. -/
theorem checkSliceBounds_prefix {limit n : Nat} (h : n ≤ limit) :
    checkSliceBounds "length" limit 0 (n : Int) = .ok (0, n) := by
  simp only [checkSliceBounds, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (by omega : ¬ ((n : Int) < 0)),
    if_neg (by omega : ¬ ((n : Int) > (limit : Int))),
    if_neg (by omega : ¬ ((0 : Int) < 0)),
    if_neg (by omega : ¬ ((0 : Int) > (n : Int)))]
  simp



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

/-! ### The map-entry SEARCH at a symbolic entry array

`mapEntryIndex?` is a `for … do if … then return i` loop over the
snapshot: at a LITERAL entry array `simp` unrolls it, at a symbolic one
nothing does. These two lemmas are the induction — stated over an
abstract loop body so the caller's actual one unifies — and the two
`mapLookupValue` characterizations they buy: the key is absent (Go's zero
value and `false`), or SOME entry carries it (that entry's value and
`true`). Target-free: no program, no lowering, no quorum value; the key
KIND is a quantified `{kind : IntKind}` (generalized at the 2026-08-01
pre-merge audit response — the first form pinned `.uint64`, the target's
key type, though nothing in the proofs needed it: `valueEqFuel`'s int arm
compares payloads and ignores kinds). -/

/-- The search loop when NO entry matches: it runs to the end with the
early-return slot still empty. -/
theorem forIn_find_none {α ε : Type}
    {f : α → (MProd (Option (Option Nat)) Nat) → Except ε (ForInStep (MProd (Option (Option Nat)) Nat))} :
    ∀ (l : List α) (j : Nat),
      (∀ a ∈ l, ∀ i : Nat, f a ⟨none, i⟩ = .ok (.yield ⟨none, i + 1⟩)) →
      forIn l (⟨none, j⟩ : MProd (Option (Option Nat)) Nat) f
        = .ok ⟨none, j + l.length⟩
  | [], j, _ => by simp
  | a :: t, j, h => by
    rw [List.forIn_cons, h a (by simp) j]
    simp only [Bind.bind, Except.bind]
    rw [forIn_find_none t (j + 1) (fun x hx i => h x (by simp [hx]) i),
      show j + 1 + t.length = j + (a :: t).length from by simp; omega]

/-- The search loop when the FIRST matching entry is at `pre.length`: the
prefix all misses, then the body returns that index. -/
theorem forIn_find_some {α ε : Type}
    {f : α → (MProd (Option (Option Nat)) Nat) → Except ε (ForInStep (MProd (Option (Option Nat)) Nat))}
    (p : α) (rest : List α)
    (hhit : ∀ i : Nat, f p ⟨none, i⟩ = .ok (.done ⟨some (some i), i⟩)) :
    ∀ (pre : List α) (j : Nat),
      (∀ a ∈ pre, ∀ i : Nat, f a ⟨none, i⟩ = .ok (.yield ⟨none, i + 1⟩)) →
      forIn (pre ++ p :: rest) (⟨none, j⟩ : MProd (Option (Option Nat)) Nat) f
        = .ok ⟨some (some (j + pre.length)), j + pre.length⟩
  | [], j, _ => by
    rw [List.nil_append, List.forIn_cons, hhit j]
    simp only [Bind.bind, Except.bind, List.length_nil, Nat.add_zero, pure,
      Except.pure]
  | a :: t, j, h => by
    rw [List.cons_append, List.forIn_cons, h a (by simp) j]
    simp only [Bind.bind, Except.bind]
    rw [forIn_find_some p rest hhit t (j + 1) (fun x hx i => h x (by simp [hx]) i),
      show j + 1 + t.length = j + (a :: t).length from by simp; omega]

section

variable {σ : ExecState} {mba : Addr} {mty : Option Ty} {valTy : Ty}
variable {entries : Array (GoValue × GoValue)} {q : Int}

/-- Splitting a list at its FIRST element satisfying a decidable
property — the shape the map-entry search needs (all earlier entries
miss, this one hits). -/
theorem list_split_first_match {α : Type _} (P : α → Prop) :
    ∀ (l : List α), (∃ x ∈ l, P x) →
      ∃ pre p rest, l = pre ++ p :: rest ∧ (∀ a ∈ pre, ¬ P a) ∧ P p
  | [], h => by simp at h
  | a :: t, h => by
    by_cases ha : P a
    · exact ⟨[], a, t, rfl, by simp, ha⟩
    · have h' : ∃ x ∈ t, P x := by
        obtain ⟨x, hx, hpx⟩ := h
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact absurd hpx ha
        · exact ⟨x, hx', hpx⟩
      obtain ⟨pre, p, rest, hsplit, hpre, hp⟩ := list_split_first_match P t h'
      refine ⟨a :: pre, p, rest, by rw [List.cons_append, hsplit], ?_, hp⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact ha
      · exact hpre x hx'

/-- Integer key comparison, as the search loop performs it. -/
theorem valueEq_int {kind kind' : IntKind} {a b : Int} :
    valueEq σ (.int kind) (.int a kind') (.int b kind') = .ok (a == b) := by
  simp only [valueEq, valueEqFuel, typeResolutionFuel, pure, Except.pure]

/-- **The comma-ok read, key ABSENT**: every entry's key is an `int` that
differs from the looked-up one, so Go delivers the value type's zero and
`false`. -/
theorem mapLookupValue_miss {dv : GoValue} {kind : IntKind}
    (hl : Heap.lookup σ.heap (.base mba) = some ⟨mty, .mapData entries⟩)
    (hdef : defaultValue σ valTy = .ok dv)
    (hall : ∀ p ∈ entries.toList, ∃ w : Int, p.1 = .int w kind ∧ w ≠ q) :
    mapLookupValue σ ⟨some (.base mba)⟩ (.int q kind) (.int kind) valTy
      = .ok (dv, false) := by
  simp only [mapLookupValue, mapEntries, loadLoc, hl, mapEntryIndex?,
    checkKeyHashable, valueHashability, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [← Array.forIn_toList, forIn_find_none entries.toList 0 ?hmiss]
  · simp only [hdef]
  · case hmiss =>
      intro a ha i
      obtain ⟨w, hw, hne⟩ := hall a ha
      rw [hw]
      simp only [valueEq_int, Bind.bind, Except.bind]
      rw [if_neg (by simpa using hne)]

/-- **The comma-ok read, key PRESENT**: the first entry carrying the key
answers, and any entry carrying it answers the same when the snapshot is
FUNCTIONAL at that key (`hfun`) — which is what an encoding predicate
supplies. -/
theorem mapLookupValue_hit {v : GoValue} {kind : IntKind}
    (hl : Heap.lookup σ.heap (.base mba) = some ⟨mty, .mapData entries⟩)
    (hkeys : ∀ p ∈ entries.toList, ∃ w : Int, p.1 = .int w kind)
    (hfun : ∀ p ∈ entries.toList, p.1 = .int q kind → p.2 = v)
    (hmem : ∃ p ∈ entries.toList, p.1 = .int q kind) :
    mapLookupValue σ ⟨some (.base mba)⟩ (.int q kind) (.int kind) valTy
      = .ok (v, true) := by
  -- split the snapshot at the FIRST entry carrying the key
  obtain ⟨pre, p, rest, hsplit, hpre, hp⟩ :
      ∃ pre p rest, entries.toList = pre ++ p :: rest
        ∧ (∀ a ∈ pre, a.1 ≠ .int q kind) ∧ p.1 = .int q kind :=
    list_split_first_match (fun a => a.1 = GoValue.int q kind) entries.toList hmem
  have hpv : p.2 = v := hfun p (by rw [hsplit]; simp) hp
  simp only [mapLookupValue, mapEntries, loadLoc, hl, mapEntryIndex?,
    checkKeyHashable, valueHashability, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [← Array.forIn_toList, hsplit, forIn_find_some p rest ?hhit pre 0 ?hmiss]
  · simp only [Nat.zero_add]
    rw [show entries[pre.length]? = some p from by
      rw [← Array.getElem?_toList, hsplit]
      exact list_getElem?_middle pre p rest]
    obtain ⟨pk, pv⟩ := p
    dsimp only at hpv ⊢
    rw [hpv]
  · case hhit =>
      intro i
      rw [hp]
      simp only [valueEq_int, Bind.bind, Except.bind]
      rw [if_pos (by simp)]
  · case hmiss =>
      intro a ha i
      obtain ⟨w, hw⟩ := hkeys a (by rw [hsplit]; simp [ha])
      rw [hw]
      simp only [valueEq_int, Bind.bind, Except.bind]
      rw [if_neg (by
        have hne : a.1 ≠ .int q kind := hpre a ha
        rw [hw] at hne
        simp only [beq_iff_eq, decide_eq_true_eq]
        intro hcon
        exact hne (by rw [hcon]))]

end

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

/-! ## The one-entry `mapLookupValue` computation (general; factored out
of the n = 1 quorum walk when the lookup laws were widened to arbitrary
entry arrays — proof-automation arc phase 3). -/

/-- The comma-ok lookup's answer on a ONE-ENTRY int-keyed map: the key is
present, so the stored value comes back with `found = true`. General in
the key, the value, the KIND (the quantified `{kind : IntKind}` —
generalized at the 2026-08-01 pre-merge audit response from a `.uint64`
pin nothing in the proof needed), the value TYPE and the data cell's
declared type — this is the `hpair` premise of
`wp_map_lookup`/`wp_map_lookup_ackedIndex` at the instance the n = 1 walk
uses, factored out when those were widened to arbitrary entry arrays
(proof-automation arc phase 3). -/
theorem mapLookupValue_singleton {mba : Addr} {mty : Option Ty} {q v : Int}
    {kind : IntKind} {valTy : Ty} (σ : ExecState)
    (hl : Heap.lookup σ.heap (.base mba)
      = some ⟨mty, .mapData #[(.int q kind, .int v kind)]⟩) :
    mapLookupValue σ ⟨some (.base mba)⟩ (.int q kind) (.int kind) valTy
      = .ok (.int v kind, true) := by
  simp [mapLookupValue, mapEntries, loadLoc, hl, mapEntryIndex?, valueEq,
    valueEqFuel, typeResolutionFuel, checkKeyHashable, valueHashability,
    Bind.bind, Except.bind]

end GoLean.Iris
