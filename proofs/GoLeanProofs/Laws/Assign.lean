import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.Rel
import GoLeanProofs.Lifting
import GoLeanProofs.Inversions

/-!
# Store-family laws + witnesses
The read law, var-assign, deref-store, read-through pointer store, var-copy —
each law co-located with its non-vacuity witness.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel

namespace GoLean.Iris

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **The heap read law**. Owning the target cell pins what the interpreter/
relation reads from it: `a.id ↦ cell` forces `loadLoc σ (.base a) = .ok
cell.value`. Unlike the store, this is *not* a standalone WP law — GoCore's CK
machine has no bare deref `Step` (reads are `ExprR` premises inside statement
steps like `assign`/`if`), so the read side is exposed as this ownership⟹value
lemma, which discharges a deref-RHS inside a `wp_assign`'s `hred`. -/
theorem pointsTo_loadLoc {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
    {σ : ExecState} {a : Addr} {cell : HeapCell} :
    genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ.heap) ∗ a.id ↦ cell
      ⊢ |==> ⌜loadLoc σ (.base a) = .ok cell.value⌝ := by
  iintro ⟨Hσ, Hpt⟩
  imod genHeap_valid $$ [$Hσ $Hpt] with %Hmap
  imodintro; ipureintro
  apply loadLoc_base_of_lookup
  rw [get?_heapToMap] at Hmap; simpa using Hmap

/-- **The heap store law over `Step.assign` — now a usable Hoare law** (CEK
reshape, `docs/2026-07-19_cek-reshape-plan.md`; closes the pre-merge audit
finding D2-4/D2-5).

The earlier version's `hred` was unsatisfiable: it quantified `∀ σ₁`
constrained only on `σ₁.heap`, yet a variable LHS `x = e` needs
`AssigneeR σ₁ (.var id) …` resolved from `σ₁.locals` — an `ExecState` field
`hred` never pinned, so an empty-locals `σ₁` met the antecedent while admitting
no step. Relocating locals into the control `env` (CEK) fixes exactly this: the
target `x` now resolves against `env`, which is **fixed in the WP goal** (it
rides in the `Config`, not the quantified state `σ₁`). So resolution becomes the
pure, dischargeable premise `hres : LocalEnv.lookup env id = some (.base a)` — no
state camera, no `∀σ₁`. The heap core is the spike's `wp_store`.

The remaining premises are the operational facts about the right-hand side and
the store, all legitimately dischargeable for a concrete assign (none has the
old locals problem):
- `hrhs` — `rhs` evaluates to `v` without changing the state (its existence);
- `hrhs_det` — `rhs` evaluates *only* to `v` (determinism), which rules out the
  panic step-rules during inversion;
- `hstore` — storing `v` at the owned cell yields the heap update to `newcell`.

Owning `a.id ↦ oldcell`, the assign steps deterministically to `.next k` with the
cell updated to `newcell`; the continuation runs owning `a.id ↦ newcell`. See
`wp_assign_lit` for the payoff: every premise discharged for a concrete
`x = intLit n`. -/
theorem wp_assign {a : Addr} {oldcell newcell : HeapCell} {v : GoValue}
    {id rhs env k}
    (hres : LocalEnv.lookup env id = some (.base a))
    (hrhs : ∀ σ₁ : ExecState, ExprR env σ₁ rhs (.value v σ₁))
    (hrhs_det : ∀ σ₁ (out : ExprOut), ExprR env σ₁ rhs out → out = .value v σ₁)
    (hstore : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
        storeLoc σ₁ (.base a) v
          = .ok { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) :
    a.id ↦ oldcell ∗ (a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.var id) rhs) env k) @ s ; E {{ Φ }} := by
  -- The reduction facts the old proof took as `hred`, now *derived* from the
  -- pure resolution premise plus the rhs/store operational facts.
  have hred : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
      Step (Config.exec (.assign (.var id) rhs) env k) σ₁ (.next k)
           { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell } ∧
      (∀ c' s', Step (Config.exec (.assign (.var id) rhs) env k) σ₁ c' s' →
           c' = Config.next k ∧
           s' = { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) := by
    intro σ₁ hlook
    refine ⟨Step.assign (AssigneeR.var hres) (hrhs σ₁) (hstore σ₁ hlook), ?_⟩
    intro c' s' hst
    cases hst with
    | assign hass hr hs =>
      cases hass with
      | var hl =>
        -- target location is `.base a` (hl + hres); rhs value/state are `v`/σ₁
        rw [hres] at hl; injection hl with hloc
        have hd := hrhs_det σ₁ _ hr; injection hd with hv hs2
        rw [← hloc, hv, hs2, hstore σ₁ hlook] at hs; injection hs with hs3
        exact ⟨rfl, hs3.symm⟩
    | assignTargetPanic hass => cases hass
    | assignValuePanic _ hr =>
      exact ExprOut.noConfusion (hrhs_det _ _ hr)
    | assignStorePanic hass hr hs =>
      cases hass with
      | var hl =>
        rw [hres] at hl; injection hl with hloc
        have hd := hrhs_det σ₁ _ hr; injection hd with hv hs2
        rw [← hloc, hv, hs2, hstore σ₁ hlook] at hs
        simp at hs
  exact wp_store_step rfl hred

/-- **A store-through-address law `*aexpr = e`.** The assignee is `.addr aexpr`
(store at the address that `aexpr` evaluates to), resolved through
`AssigneeR.addr`; shares the gen_heap core (`wp_store_step`) with `wp_assign` —
only the assignee resolution differs.

**Scope — read this before using it** (corrected per the 2026-07-19 directional
audit; the prior docstring overclaimed):

The `hres`/`hres_det` premises are `∀σ₁` — they require `aexpr` to evaluate to
the target address `.base a` *in every state*. That holds only for a
**heap-independent** address expression, i.e. one resolved purely from the
control `env`: `aexpr = .ref x` (`&x`) via `ExprR.ref`, or a resolved location.
`wp_deref_store_ref` is the discharge witness proving the law is genuinely
non-vacuous for that case.

It does **not** yet cover the frontend's real `*p` where `p` is a pointer
*variable*: there the address is the *value* of `p`'s cell, so `hres`'s `∀σ₁` is
unsatisfiable (an `σ₁` where `p`'s cell holds a different address meets nothing).
That read-through case needs the `hres`/`hrhs` premises **conditioned on the
owned cell(s)** plus multi-`↦` ownership (own `p`'s cell *and* the target) — the
tracked next increment (`docs/2026-07-19_vertical-slice-plan.md`, L5), not this
law. So `inc`'s body `*p = *p + 1` is not yet provable by this law alone.

Premises:
- `hres`/`hres_det` — `aexpr` evaluates only to `.addr (.base a)`, state
  unchanged (heap-independent; see scope). Determinism additionally rules out the
  `addrNil`/`addr` panic steps during inversion.
- `hrhs`/`hrhs_det` — `e` evaluates only to `v`, state unchanged.
- `hstore` — storing `v` at the owned cell yields the update to `newcell`. -/
theorem wp_deref_store {a : Addr} {oldcell newcell : HeapCell} {v : GoValue}
    {aexpr rhs env k}
    (hres : ∀ σ₁ : ExecState, ExprR env σ₁ aexpr (.value (.addr (.base a)) σ₁))
    (hres_det : ∀ σ₁ (out : ExprOut),
        ExprR env σ₁ aexpr out → out = .value (.addr (.base a)) σ₁)
    (hrhs : ∀ σ₁ : ExecState, ExprR env σ₁ rhs (.value v σ₁))
    (hrhs_det : ∀ σ₁ (out : ExprOut), ExprR env σ₁ rhs out → out = .value v σ₁)
    (hstore : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
        storeLoc σ₁ (.base a) v
          = .ok { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) :
    a.id ↦ oldcell ∗ (a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.addr aexpr) rhs) env k) @ s ; E {{ Φ }} := by
  have hred : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
      Step (Config.exec (.assign (.addr aexpr) rhs) env k) σ₁ (.next k)
           { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell } ∧
      (∀ c' s', Step (Config.exec (.assign (.addr aexpr) rhs) env k) σ₁ c' s' →
           c' = Config.next k ∧
           s' = { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) := by
    intro σ₁ hlook
    refine ⟨Step.assign (AssigneeR.addr (hres σ₁)) (hrhs σ₁) (hstore σ₁ hlook), ?_⟩
    intro c' s' hst
    cases hst with
    | assign hass hr hs =>
      cases hass with
      | addr haddr =>
        -- addr expr resolves to `.base a`, state unchanged (hres_det)
        have hd := hres_det σ₁ _ haddr; injection hd with hav has1
        injection hav with hloc
        have hd2 := hrhs_det σ₁ _ (has1 ▸ hr); injection hd2 with hv hs2
        rw [hloc, hv, hs2, hstore σ₁ hlook] at hs; injection hs with hs3
        exact ⟨rfl, hs3.symm⟩
    | assignTargetPanic hass =>
      cases hass with
      | addrNil haddr => have hd := hres_det σ₁ _ haddr; simp at hd
      | addrPanic haddr => exact ExprOut.noConfusion (hres_det σ₁ _ haddr)
    | assignValuePanic _ hr =>
      exact ExprOut.noConfusion (hrhs_det _ _ hr)
    | assignStorePanic hass hr hs =>
      cases hass with
      | addr haddr =>
        have hd := hres_det σ₁ _ haddr; injection hd with hav has1
        injection hav with hloc
        have hd2 := hrhs_det σ₁ _ (has1 ▸ hr); injection hd2 with hv hs2
        rw [hloc, hv, hs2, hstore σ₁ hlook] at hs
        simp at hs
  exact wp_store_step rfl hred

/-- **Payoff: `wp_assign` is genuinely instantiable — with ZERO hypotheses.**
This is what task #23 was blocked on — the old law's `hred` was unsatisfiable
for *every* real assign (`docs/2026-07-19_premerge-audit-results.md`,
D2-4/D2-5). Every premise is discharged: resolution by `simp` against the
concrete control environment binding `x ↦ .base a`; the rhs premises outright
for an integer literal (`ExprR.intLit` / `exprR_intLit_det`); and the store
side-condition by `storeLoc_int_cell` (the cell is int-typed, so the store's
re-normalization collapses by `intKind_normalize_idem`). The owned cell's prior
value `w` is arbitrary — this is the general "assign a literal over anything in
an int cell" spec, closed. (Arc `slice-l5-pure` item 1: `hstore` was previously
an open `∀σ` hypothesis; the Audit ledger's `◌` is now `✓`.) -/
theorem wp_assign_lit {a : Addr} {w : GoValue} {n : Int}
    {kind : IntKind} {rest : LocalEnv} {k} :
    a.id ↦ (⟨some (.int kind), w⟩ : HeapCell)
      ∗ (a.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.var "x") (.intLit n kind))
              ([("x", Loc.base a)] :: rest) k) @ s ; E {{ Φ }} :=
  wp_assign (id := "x") (v := .int (kind.normalize n) kind)
    (by simp [LocalEnv.lookup, Scope.lookup])
    (fun _ => ExprR.intLit)
    (fun _ _ h => exprR_intLit_det h)
    (fun _ hlook => storeLoc_int_cell hlook n)

/-- **Non-vacuity witness for `wp_deref_store` — ZERO hypotheses.** Discharges
the heap-independent address case the law genuinely covers: `*(&x) = n` —
assignee `.addr (.ref "x")`, whose address resolves purely from `env`
(`x ↦ .base a`) via `ExprR.ref`, so the `∀σ₁` `hres`/`hres_det` premises hold.
`hrhs`/`hrhs_det` discharge for the integer literal, and the store side-condition
by `storeLoc_int_cell` (arbitrary prior value `w` in an int-typed cell). This
proves `wp_deref_store` is a real (non-scaffold) law — contrast the read-through
`*p` case, whose address comes from a pointer variable's cell and therefore needs
cell-conditioned premises + multi-`↦` ownership (arc item 3, not this witness). -/
theorem wp_deref_store_ref {a : Addr} {w : GoValue} {n : Int}
    {kind : IntKind} {rest : LocalEnv} {k} :
    a.id ↦ (⟨some (.int kind), w⟩ : HeapCell)
      ∗ (a.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.addr (.ref "x")) (.intLit n kind))
              ([("x", Loc.base a)] :: rest) k) @ s ; E {{ Φ }} :=
  wp_deref_store (a := a) (v := .int (kind.normalize n) kind)
    (fun _ => ExprR.ref (by simp [LocalEnv.lookup, Scope.lookup]))
    (fun _ _ h => exprR_ref_det (by simp [LocalEnv.lookup, Scope.lookup]) h)
    (fun _ => ExprR.intLit)
    (fun _ _ h => exprR_intLit_det h)
    (fun _ hlook => storeLoc_int_cell hlook n)

/-! ## Arc `slice-l5-pure` item 3 — the read-through pointer store `*p = …`

The case `wp_deref_store` cannot cover: the target address is the *value of
`p`'s cell*, so resolution is heap-dependent. The premises here are
**conditioned on the owned cells** (this is what the `∀σ₁`-unsatisfiability of
the state-independent premises forces), and the law consumes the two-cell core
`wp_store_step₂`: own `p`'s cell (read) and the target cell (written). -/

/-- **The read-through pointer store law `*p = e`** — `p` is a pointer
*variable*; the target address is the value of `p`'s cell. Premises are
conditioned on the two owned cells (that conditioning is exactly what the
audit-established unsatisfiability of state-independent premises requires):
- `hres` — `p` resolves in `env` to its own cell `pa`;
- `hpval` — `p`'s cell holds the target address `.addr (.base a)`;
- `hrhs`/`hrhs_det` — under both cell facts, `rhs` evaluates only to `v`;
- `hstore` — storing `v` at the owned target yields the update.
Consumes the two-cell core; the continuation regains both cells, target
updated. Witness: `wp_inc_via_ptr` (`*p = *p + 1`, zero hypotheses). -/
theorem wp_store_via_ptr {pa a : Addr} {pcell oldcell newcell : HeapCell}
    {v : GoValue} {p : String} {rhs env k}
    (hres : LocalEnv.lookup env p = some (.base pa))
    (hpval : pcell.value = .addr (.base a))
    (hrhs : ∀ σ₁ : ExecState,
        Heap.lookup σ₁.heap (.base pa) = some pcell →
        Heap.lookup σ₁.heap (.base a) = some oldcell →
        ExprR env σ₁ rhs (.value v σ₁))
    (hrhs_det : ∀ σ₁ (out : ExprOut),
        Heap.lookup σ₁.heap (.base pa) = some pcell →
        Heap.lookup σ₁.heap (.base a) = some oldcell →
        ExprR env σ₁ rhs out → out = .value v σ₁)
    (hstore : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base a) = some oldcell →
        storeLoc σ₁ (.base a) v
          = .ok { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) :
    pa.id ↦ pcell ∗ a.id ↦ oldcell
      ∗ (pa.id ↦ pcell ∗ a.id ↦ newcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.addr (.var p)) rhs) env k) @ s ; E {{ Φ }} := by
  have hred : ∀ σ₁ : ExecState,
      Heap.lookup σ₁.heap (.base pa) = some pcell →
      Heap.lookup σ₁.heap (.base a) = some oldcell →
      Step (Config.exec (.assign (.addr (.var p)) rhs) env k) σ₁ (.next k)
           { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell } ∧
      (∀ c' s', Step (Config.exec (.assign (.addr (.var p)) rhs) env k) σ₁ c' s' →
           c' = Config.next k ∧
           s' = { σ₁ with heap := Heap.set σ₁.heap (.base a) newcell }) := by
    intro σ₁ hlp hla
    have hloadp : loadLoc σ₁ (.base pa) = .ok (.addr (.base a)) := by
      rw [loadLoc_base_of_lookup hlp, hpval]
    refine ⟨Step.assign (AssigneeR.addr (ExprR.var hres hloadp))
      (hrhs σ₁ hlp hla) (hstore σ₁ hla), ?_⟩
    intro c' s' hst
    cases hst with
    | assign hass hr hs =>
      cases hass with
      | addr haddr =>
        have hd := exprR_var_det hres hloadp haddr
        injection hd with hav hs1
        injection hav with hloc
        rw [hs1] at hr
        have hd2 := hrhs_det σ₁ _ hlp hla hr
        injection hd2 with hv hs2
        rw [hloc, hv, hs2, hstore σ₁ hla] at hs
        injection hs with hs3
        exact ⟨rfl, hs3.symm⟩
    | assignTargetPanic hass =>
      cases hass with
      | addrNil haddr =>
        have hd := exprR_var_det hres hloadp haddr
        injection hd with hav _
        exact GoValue.noConfusion hav
      | addrPanic haddr =>
        exact ExprOut.noConfusion (exprR_var_det hres hloadp haddr)
    | assignValuePanic hass hr =>
      cases hass with
      | addr haddr =>
        have hd := exprR_var_det hres hloadp haddr
        injection hd with _ hs1
        exact ExprOut.noConfusion (hrhs_det σ₁ _ (hs1 ▸ hlp) (hs1 ▸ hla) (hs1 ▸ hr))
    | assignStorePanic hass hr hs =>
      cases hass with
      | addr haddr =>
        have hd := exprR_var_det hres hloadp haddr
        injection hd with hav hs1
        injection hav with hloc
        rw [hs1] at hr
        have hd2 := hrhs_det σ₁ _ hlp hla hr
        injection hd2 with hv hs2
        rw [hloc, hv, hs2, hstore σ₁ hla] at hs
        simp at hs
  exact wp_store_step₂ rfl hred

/-- **Zero-hypothesis witness: `*p = *p + lit` (∀-general over `m` AND `lit`;
`inc`'s body is the `lit = 1` instance).** Own `p`'s cell
(holding a pointer to `a`) and the target int cell (holding `m`); after the
statement the target holds the normalized `m + 1` and `p`'s cell is unchanged.
Every premise of `wp_store_via_ptr` is discharged: resolution by `simp`
against the concrete env, the conditioned rhs evaluation by
`ExprR.addInt`/`ExprR.deref`/`ExprR.var`, its determinism by `exprR_inc_det`,
and the store by `storeLoc_int_cell`. The first multi-`↦` closed spec — the
`{p ↦ –, a ↦ m} *p = *p+1 {p ↦ –, a ↦ m+1}` shape the slice's `inc` needs
(∀ m: general, not specialized to an example value). -/
theorem wp_inc_via_ptr {pa a : Addr} {pdecl : Option Ty} {ty : Ty}
    {kind : IntKind} {m lit : Int} {rest : LocalEnv} {k} :
    pa.id ↦ (⟨pdecl, .addr (.base a)⟩ : HeapCell)
      ∗ a.id ↦ (⟨some (.int kind), .int m kind⟩ : HeapCell)
      ∗ (pa.id ↦ (⟨pdecl, .addr (.base a)⟩ : HeapCell)
          ∗ a.id ↦ (⟨some (.int kind), .int (kind.normalize (m + kind.normalize lit)) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec
              (.assign (.addr (.var "p"))
                (.add (.deref (.var "p") ty) (.intLit lit kind)))
              ([("p", Loc.base pa)] :: rest) k) @ s ; E {{ Φ }} :=
  wp_store_via_ptr (pa := pa) (a := a)
    (v := .int (kind.normalize (m + kind.normalize lit)) kind)
    (by simp [LocalEnv.lookup, Scope.lookup])
    rfl
    (fun σ₁ hlp hla =>
      ExprR.addInt
        (ExprR.deref (ExprR.var (loc := .base pa)
            (by simp [LocalEnv.lookup, Scope.lookup])
            (by rw [loadLoc_base_of_lookup hlp]))
          (by rw [loadLoc_base_of_lookup hla]))
        ExprR.intLit
        (intKind_compatibleResult_self kind))
    (fun σ₁ out hlp hla h =>
      exprR_inc_det (by simp [LocalEnv.lookup, Scope.lookup]) hlp rfl hla h)
    (fun σ₁ hla => storeLoc_int_cell hla (m + kind.normalize lit))

/-! ## Arc `slice-call-frame` item 4b — the call law

`Step.call` enters a fresh frame, ALLOCATING the parameter cell. The law's
continuation therefore receives a **fresh** `↦` for an address chosen by the
machine (`∀ pa` on the Iris side), and the function is resolved against the
state-interp-pinned program (`GoCoreGS.prog`) — a pure premise, not a `∀σ` one
(`docs/2026-07-20_call-law-design.md`). -/

/-- **Var-to-var assignment `tgt = src`** (the lowering of `return x`'s
result-local write): read the source cell, write the target cell — the
two-cell core again, both resolutions fixed-env facts. Witness:
`wp_assign_var_int`. -/
theorem wp_assign_var {sa ta : Addr} {scell tcell newtcell : HeapCell}
    {tgt src : String} {env k}
    (hres_t : LocalEnv.lookup env tgt = some (.base ta))
    (hres_s : LocalEnv.lookup env src = some (.base sa))
    (hstore : ∀ σ₁ : ExecState, Heap.lookup σ₁.heap (.base ta) = some tcell →
        storeLoc σ₁ (.base ta) scell.value
          = .ok { σ₁ with heap := Heap.set σ₁.heap (.base ta) newtcell }) :
    sa.id ↦ scell ∗ ta.id ↦ tcell
      ∗ (sa.id ↦ scell ∗ ta.id ↦ newtcell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.var tgt) (.var src)) env k) @ s ; E {{ Φ }} := by
  have hred : ∀ σ₁ : ExecState,
      Heap.lookup σ₁.heap (.base sa) = some scell →
      Heap.lookup σ₁.heap (.base ta) = some tcell →
      Step (Config.exec (.assign (.var tgt) (.var src)) env k) σ₁ (.next k)
           { σ₁ with heap := Heap.set σ₁.heap (.base ta) newtcell } ∧
      (∀ c' s', Step (Config.exec (.assign (.var tgt) (.var src)) env k) σ₁ c' s' →
           c' = Config.next k ∧
           s' = { σ₁ with heap := Heap.set σ₁.heap (.base ta) newtcell }) := by
    intro σ₁ hls hlt
    have hloads : loadLoc σ₁ (.base sa) = .ok scell.value :=
      loadLoc_base_of_lookup hls
    refine ⟨Step.assign (AssigneeR.var hres_t) (ExprR.var hres_s hloads)
      (hstore σ₁ hlt), ?_⟩
    intro c' s' hst
    cases hst with
    | assign hass hr hs =>
      cases hass with
      | var hl =>
        rw [hres_t] at hl
        injection hl with hloc
        have hd := exprR_var_det hres_s hloads hr
        injection hd with hv hs2
        rw [← hloc, hv, hs2, hstore σ₁ hlt] at hs
        injection hs with hs3
        exact ⟨rfl, hs3.symm⟩
    | assignTargetPanic hass => cases hass
    | assignValuePanic hass hr =>
      cases hass with
      | var _ => exact ExprOut.noConfusion (exprR_var_det hres_s hloads hr)
    | assignStorePanic hass hr hs =>
      cases hass with
      | var hl =>
        rw [hres_t] at hl
        injection hl with hloc
        have hd := exprR_var_det hres_s hloads hr
        injection hd with hv hs2
        rw [← hloc, hv, hs2, hstore σ₁ hlt] at hs
        simp at hs
  exact wp_store_step₂ rfl hred

/-- Witness for `wp_assign_var`: copy an int variable into an int target cell
(∀-general over the copied value). -/
theorem wp_assign_var_int {sa ta : Addr} {kind : IntKind} {n : Int}
    {w : GoValue} {tgt src : String} {env k}
    (hres_t : LocalEnv.lookup env tgt = some (.base ta))
    (hres_s : LocalEnv.lookup env src = some (.base sa)) :
    sa.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.int kind), w⟩ : HeapCell)
      ∗ (sa.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
          ∗ ta.id ↦ (⟨some (.int kind), .int (kind.normalize n) kind⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.assign (.var tgt) (.var src)) env k) @ s ; E {{ Φ }} :=
  wp_assign_var hres_t hres_s (fun σ₁ hlt => storeLoc_int_cell hlt n)

end

end GoLean.Iris
