import GoLeanProofs.Laws.Eval
import GoLeanProofs.SliceMem

/-!
# Slice-index WP laws (verified-examples slice 2b, 2026-08-13)

The §9e build list's slice laws (`docs/2026-08-12_example-spec-form.md`):

* `wp_index_get_slice` — the index-READ law: `s[i]` at a slice handle
  loads the backing cell, bounds-checks at evaluation, and delivers the
  element. The heap-reading core is the general
  `wp_strict_apply_read`; this law packages the slice-specific
  discharge (`SliceMem.applyStrictOp_indexGet_slice`).
* `wp_len_slice` — `len(s)` evaluation: state-free (the handle carries
  its length), so a `wp_strict_apply_pure` instance.
* `wp_store_index_slice_u64` — the index-target STORE law: a phase-2
  store through a completed `.chain (slice) [i] [.index]` reference
  (`s[i] = v`); the chain's bounds check fires at STORE time
  (BUG-029), and the write lands in the backing cell with the array
  re-normalized at its declared type. Stated on the `[]uint64`
  fragment (the store path normalizes the WHOLE backing array against
  the declared element type, so a fully general law needs a
  value/type-generic normal-form story — recorded growth point, not
  smuggled in).

**Build-list finding, recorded**: the fourth item — "the index-target
multi-assign walk (the tgtOpK spine at index-step target shapes)" —
needs NO new law: the existing spine laws
(`wp_assign_many_start`/`wp_tgtop_shift`/`wp_tgtop_next`/`wp_tgtop_rhs`
/`wp_rhs_shift`/`wp_rhs_stores_vals`) are already shape-generic in
`TargetShape`, and `completeTargetRef (.chain [.index]) [handle, idx]`
discharges by `rfl`. The same-commit witness below
(`wp_swap_witness`) IS that walk — the two-target index-shape
multi-assign `s[0], s[1] = s[1], s[0]` — so the spine's index-shape
instances are exercised rather than merely claimed.

Every law ships with its discharge witness in this file (non-vacuity
gate): `wp_index_get_witness`, `wp_len_slice_witness`, and
`wp_swap_witness` (one walk discharging the store law, re-discharging
the read law, and exercising the multi-assign spine at index shapes,
on a concrete two-element slice). Witnesses are registered in
`proofs/Audit.lean`.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.SliceMem

namespace GoLean.Iris

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **The slice index-read law** (`s[i]` evaluation at the strict-apply
step): the backing cell is owned and rides through unchanged; the
bounds check (`i < len`, at EVALUATION — the expression-position
check) and the handle's well-formedness (`len ≤ cap`) are premises;
the element at `off + i` is delivered. -/
theorem wp_index_get_slice {a : Addr} {dty : Option Ty}
    {off len cap i : Nat} {ik : IntKind} {vs : Array GoValue}
    {w : GoValue} {env k}
    (hcap : len ≤ cap) (hi : i < len)
    (hget : vs[off + i]? = some w) :
    a.id ↦ (⟨dty, .array vs⟩ : HeapCell)
      ∗ (a.id ↦ (⟨dty, .array vs⟩ : HeapCell) -∗
          WP (Config.retV w k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.int (i : Nat) ik)
            (.strictK .indexGet [.slice ⟨some (.base a), off, len, cap⟩] []
              env k)) @ s ; E {{ Φ }} :=
  wp_strict_apply_read (happly := fun _σ _htypes hlook =>
    applyStrictOp_indexGet_slice hlook hcap hi hget)

/-- **The `len(s)` law**: the handle carries its length, so the apply
step is state-free (`wp_strict_apply_pure`); only the handle's
well-formedness (`len ≤ cap`) is needed, for the machine's
`validateSlice`. Delivered at Go's `int` kind, as the machine does. -/
theorem wp_len_slice {b : Loc} {off len cap : Nat} {elem : Ty} {env k}
    (hcap : len ≤ cap) :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.retV (.int (len : Nat) .int) k) @ s ; E {{ Φ }})
      ⊢ WP (Config.retV (.slice ⟨some b, off, len, cap⟩)
            (.strictK (.lengthOf (some (.slice elem))) [] [] env k))
          @ s ; E {{ Φ }} :=
  wp_strict_apply_pure (happly := fun _σ =>
    applyStrictOp_len_slice hcap)

/-- **The slice index-target store law** (`s[i] = v` on `[]uint64`,
phase 2): one `storeK` store through a completed
`.chain (slice-handle) [i] [.index]` reference. The chain's OWN
bounds check fires HERE, at store time (BUG-029) — `hi` discharges
it — and the write lands in the BACKING cell: the array with element
`off + i` set, re-normalized at the cell's declared array type
(identity on the in-range `[]uint64` fragment — the range premises).
The `Loc.index` write resolves to a `Heap.set` at the BASE address,
which is why the owned resource is the backing cell. -/
theorem wp_store_index_slice_u64 {a : Addr} {off len cap i n : Nat}
    {ik : IntKind} {l : List Int} {w : Int}
    {rs : List TargetRef} {vals : List GoValue} {body : Stmt}
    {env : LocalEnv} {k}
    (hcap : len ≤ cap) (hi : i < len)
    (hsz : off + i < l.length) (hn : l.length = n)
    (hl : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64)
    (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    a.id ↦ (⟨some (.array n (.int .uint64)),
              .array ⟨l.map (fun v => .int v .uint64)⟩⟩ : HeapCell)
      ∗ (a.id ↦ (⟨some (.array n (.int .uint64)),
            .array ⟨(l.set (off + i) w).map (fun v => .int v .uint64)⟩⟩ :
              HeapCell) -∗
          WP (Config.next (.storeK rs vals body env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.storeK
            (.chain (.slice ⟨some (.base a), off, len, cap⟩)
              [.int (i : Nat) ik] [.index] :: rs)
            (.int w .uint64 :: vals) body env k)) @ s ; E {{ Φ }} :=
  wp_store_target (fun _σ₁ _htypes hlook =>
    storeTarget_slice_u64 hlook hcap hi hsz hn hl hw)

/-! ## Discharge witnesses (non-vacuity gate; same commit as the laws)

A concrete two-element `[]uint64`: backing cell `[7, 9]` at `ba`, the
handle in the local `s`'s cell at `sa`. The swap witness walks the
frontend's exact shape for `s[0], s[1] = s[1], s[0]` — the two-target
index-shape multi-assign — through phase 1 (targets then RHS: two
`wp_index_get_slice` reads), then phase 2 (two
`wp_store_index_slice_u64` stores), landing with the backing cell
holding `[9, 7]`. This is simultaneously the discharge witness for the
build list's fourth item: the tgtOpK spine at index-step target
shapes, `completeTargetRef` discharged by `rfl` at both targets. -/

/-- The two-element backing cell. -/
private abbrev wcell (l : List Int) : HeapCell :=
  ⟨some (.array 2 (.int .uint64)), .array ⟨l.map (fun v => .int v .uint64)⟩⟩

/-- The handle cell (`s`'s local). -/
private abbrev whandle (ba : Addr) : HeapCell :=
  ⟨some (.slice (.int .uint64)), .slice ⟨some (.base ba), 0, 2, 2⟩⟩

/-- The frontend's lowering shape for `s[0], s[1] = s[1], s[0]`. -/
private abbrev wswap : Stmt :=
  .assignMany
    #[.addr (.indexAddr (.var "s") (.intLit 0 .int)),
      .addr (.indexAddr (.var "s") (.intLit 1 .int))]
    #[.indexGet (.var "s") (.intLit 1 .int),
      .indexGet (.var "s") (.intLit 0 .int)]

local macro "idance" : tactic =>
  `(tactic| (iapply fupd_intro; inext; iapply fupd_intro; iintro -))

/-- **Discharge witness** for `wp_index_get_slice` (and the strict-op
entry at `indexGet`): evaluating `s[1]` on the concrete slice delivers
`9`. Every law premise is discharged concretely. -/
theorem wp_index_get_witness {sa ba : Addr} {env : LocalEnv} {k : Cont}
    (hres : LocalEnv.lookup env "s" = some (.base sa)) :
    sa.id ↦ whandle ba
      ∗ ba.id ↦ wcell [7, 9]
      ∗ (sa.id ↦ whandle ba ∗ ba.id ↦ wcell [7, 9] -∗
          WP (Config.retV (.int 9 .uint64) k) @ s ; E {{ Φ }})
      ⊢ WP (Config.evalE (.indexGet (.var "s") (.intLit 1 .int)) env k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hs, Hb, Hk⟩
  iapply (wp_eval_strict (op := .indexGet) (e₁ := .var "s")
    (rest := [.intLit 1 .int]) rfl)
  idance
  iapply (wp_eval_var (a := sa) (cell := whandle ba) (hres := hres))
  isplitl [Hs]
  · iexact Hs
  iintro Hs
  iapply wp_strict_shift
  idance
  iapply wp_eval_intLit
  idance
  rw [show IntKind.normalize .int 1 = ((1 : Nat) : Int) from by decide]
  iapply (wp_index_get_slice (a := ba) (off := 0) (len := 2) (cap := 2)
    (i := 1) (vs := ⟨[7, 9].map (fun v => .int v .uint64)⟩)
    (w := .int 9 .uint64)
    (hcap := by omega) (hi := by omega) (hget := by simp))
  isplitl [Hb]
  · iexact Hb
  iintro Hb
  iapply Hk
  isplitl [Hs]
  · iexact Hs
  · iexact Hb

/-- **Discharge witness** for `wp_len_slice`: `len(s)` on the concrete
slice delivers `2`. -/
theorem wp_len_slice_witness {sa ba : Addr} {env : LocalEnv} {k : Cont}
    (hres : LocalEnv.lookup env "s" = some (.base sa)) :
    sa.id ↦ whandle ba
      ∗ (sa.id ↦ whandle ba -∗
          WP (Config.retV (.int 2 .int) k) @ s ; E {{ Φ }})
      ⊢ WP (Config.evalE
            (.length (.var "s") (some (.slice (.int .uint64)))) env k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hs, Hk⟩
  iapply (wp_eval_strict (op := .lengthOf (some (.slice (.int .uint64))))
    (e₁ := .var "s") (rest := []) rfl)
  idance
  iapply (wp_eval_var (a := sa) (cell := whandle ba) (hres := hres))
  isplitl [Hs]
  · iexact Hs
  iintro Hs
  iapply (wp_len_slice (b := .base ba) (off := 0) (len := 2) (cap := 2)
    (hcap := by omega))
  idance
  iapply Hk
  iexact Hs

/-- **Discharge witness** for `wp_store_index_slice_u64` AND the
tgtOpK spine at index-step target shapes (build-list item 4): the full
two-target index-shape multi-assign `s[0], s[1] = s[1], s[0]` on the
concrete slice — phase 1 (both targets' operands, both RHS reads
through `wp_index_get_slice`), phase 2 (both stores through
`wp_store_index_slice_u64`) — landing with the backing cell reversed. -/
theorem wp_swap_witness {sa ba : Addr} {env : LocalEnv} {k : Cont}
    (hres : LocalEnv.lookup env "s" = some (.base sa)) :
    sa.id ↦ whandle ba
      ∗ ba.id ↦ wcell [7, 9]
      ∗ (sa.id ↦ whandle ba ∗ ba.id ↦ wcell [9, 7] -∗
          WP (Config.exec (.seqn #[]) env k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec wswap env k) @ s ; E {{ Φ }} := by
  iintro ⟨Hs, Hb, Hk⟩
  iapply (wp_assign_many_start (sh := .chain [.index]) (e := .var "s")
    (ops := [.intLit 0 .int])
    (rest := [(.chain [.index], [.var "s", .intLit 1 .int])])
    rfl rfl)
  idance
  -- target 1 operands: s, 0
  iapply (wp_eval_var (a := sa) (cell := whandle ba) (hres := hres))
  isplitl [Hs]
  · iexact Hs
  iintro Hs
  iapply wp_tgtop_shift
  idance
  iapply wp_eval_intLit
  idance
  rw [show IntKind.normalize .int 0 = ((0 : Nat) : Int) from by decide]
  iapply (wp_tgtop_next
    (r := .chain (.slice ⟨some (.base ba), 0, 2, 2⟩) [.int ((0 : Nat) : Int) .int]
      [.index]) rfl)
  idance
  -- target 2 operands: s, 1
  iapply (wp_eval_var (a := sa) (cell := whandle ba) (hres := hres))
  isplitl [Hs]
  · iexact Hs
  iintro Hs
  iapply wp_tgtop_shift
  idance
  iapply wp_eval_intLit
  idance
  rw [show IntKind.normalize .int 1 = ((1 : Nat) : Int) from by decide]
  iapply (wp_tgtop_rhs
    (r := .chain (.slice ⟨some (.base ba), 0, 2, 2⟩) [.int ((1 : Nat) : Int) .int]
      [.index]) rfl)
  idance
  -- RHS 1: s[1] — the index-read law
  iapply (wp_eval_strict (op := .indexGet) (e₁ := .var "s")
    (rest := [.intLit 1 .int]) rfl)
  idance
  iapply (wp_eval_var (a := sa) (cell := whandle ba) (hres := hres))
  isplitl [Hs]
  · iexact Hs
  iintro Hs
  iapply wp_strict_shift
  idance
  iapply wp_eval_intLit
  idance
  rw [show IntKind.normalize .int 1 = ((1 : Nat) : Int) from by decide]
  iapply (wp_index_get_slice (a := ba) (off := 0) (len := 2) (cap := 2)
    (i := 1) (vs := ⟨[7, 9].map (fun v => .int v .uint64)⟩)
    (w := .int 9 .uint64)
    (hcap := by omega) (hi := by omega) (hget := by simp))
  isplitl [Hb]
  · iexact Hb
  iintro Hb
  iapply wp_rhs_shift
  idance
  -- RHS 2: s[0]
  iapply (wp_eval_strict (op := .indexGet) (e₁ := .var "s")
    (rest := [.intLit 0 .int]) rfl)
  idance
  iapply (wp_eval_var (a := sa) (cell := whandle ba) (hres := hres))
  isplitl [Hs]
  · iexact Hs
  iintro Hs
  iapply wp_strict_shift
  idance
  iapply wp_eval_intLit
  idance
  rw [show IntKind.normalize .int 0 = ((0 : Nat) : Int) from by decide]
  iapply (wp_index_get_slice (a := ba) (off := 0) (len := 2) (cap := 2)
    (i := 0) (vs := ⟨[7, 9].map (fun v => .int v .uint64)⟩)
    (w := .int 7 .uint64)
    (hcap := by omega) (hi := by omega) (hget := by simp))
  isplitl [Hb]
  · iexact Hb
  iintro Hb
  iapply wp_rhs_stores_vals
  idance
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append]
  -- phase 2, store 1: s[0] := 9 — the index-target store law
  iapply (wp_store_index_slice_u64 (a := ba) (off := 0) (len := 2)
    (cap := 2) (i := 0) (n := 2) (l := [7, 9]) (w := 9)
    (hcap := by omega) (hi := by omega) (hsz := by simp) (hn := by simp)
    (hl := by intro v hv; simp at hv; rcases hv with rfl | rfl <;> omega)
    (hw := by omega))
  isplitl [Hb]
  · iexact Hb
  iintro Hb
  rw [show (([7, 9] : List Int).set (0 + 0) 9) = [9, 9] from rfl]
  -- phase 2, store 2: s[1] := 7
  iapply (wp_store_index_slice_u64 (a := ba) (off := 0) (len := 2)
    (cap := 2) (i := 1) (n := 2) (l := [9, 9]) (w := 7)
    (hcap := by omega) (hi := by omega) (hsz := by simp) (hn := by simp)
    (hl := by intro v hv; simp at hv; omega)
    (hw := by omega))
  isplitl [Hb]
  · iexact Hb
  iintro Hb
  rw [show (([9, 9] : List Int).set (0 + 1) 7) = [9, 7] from rfl]
  iapply wp_stores_done
  idance
  iapply Hk
  isplitl [Hs]
  · iexact Hs
  · iexact Hb

end

end GoLean.Iris
