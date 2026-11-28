import GoLean.GoCore.WideValue
import GoLean.GoCore.DeadCell
import GoLean.GoCore.StepErrors
import GoLean.GoCore.TableMonotonicity
import GoLean.GoCore.Equations

/-!
# The wide operators' value forms — what holds of them standing alone

[AGENT lane core/wide-value-1127], 2026-11-27, on the [USER]'s direction of that day that the
value forms be a principled surface others might target, not only the two equations a customer
asked for.

`WideValue.lean` states the value forms and the equations tying the machine's wide operator to
them. A consumer whose target has no cell cannot reach the machine's operator through those
equations, so what the kept surface says about `applyStmtOp` is stated here of
`applyStmtOpValue` itself, with what the equations leave open:

* **Transfer** (`applyStmtOpValue_plan_error_iff`, `_plan_ok_iff`): the two validate phases
  fail together with the same stop and succeed together, at any target address.
* **The target** (`applyStmtOp_plan_target`, `applyStmtOp_plan_ok_iff_value`,
  `applyStmtOp_plan_error_of_target`): a machine apply that succeeds had an address for its
  target, so the machine's plan succeeds EXACTLY when the target is an address and the value
  plan succeeds; a target that is not an address never succeeds. (`randIntn` in its two-operand
  form; with one operand it has no target.)
* **Stops** (`applyStmtOpValue_commit_noPanic`, `_plan_tame`, `_commit_tame`): a commit never
  panics; every stop is a refusal, `fatal` or a recoverable panic.
* **No dead cell** (`applyStmtOpValue_noDead`).
* **The effect** (`applyStmtOpValue_effect : … → WideEffect ctx op vs s v s₁`, and each clause
  as its own statement — `applyStmtOpValue_shape`, `_size`, `_frame`, `_frame_of_growth`,
  `_wf`): the value has the operator's constructor (`StmtOp.valueShape`); the heap grew by at
  most one cell; every existing root cell but the one backing the operator may write
  (`wideWrittenRoot?`) is as it was, and if the heap GREW no existing cell was written at all
  (a spilling `appendSlice` leaves its old backing alone); `StateWf` is kept, the allocator does
  not go back, and the value is bounded by it. Under it, the memory frame laws
  (`Store.updateCell_frame`, `storeLoc_frame`, `Mem.store_frame`, `Mem.storeElems_frame`,
  `Mem.storeRun_frame`, `Store.alloc_frame`, `Store.allocCell_frame`).
* **The stream** (`applyStmtOpValue_no_draw`, `_appendSlice_stream`, `_randIntn`): only a
  spilling `appendSlice` and `randIntn` draw; the others return the stream untouched with no
  pick record. Stated of the value forms themselves because the equation shows the returned
  stream only through a store into a target that succeeds.
* **Table slices** (`TableMono.applyStmtOpValue_plan_eq`, `_eq`, `storeValue_eq`): the value
  forms read the type table only.
* **The step** (`retV_stmtOpK_apply_value`, `_panic`, `_error`, `_store_error`,
  `retV_stmtOpK_apply_randIntn_untargeted`): `stepFn` at the apply position in terms of the
  value form. Not tagged `@[stepFn_eqns]`: they overlap the machine's own
  `retV_stmtOpK_apply*`, which the simp set already holds.

NOT STATED, and why.
* The exact value and store of each operator (an equation per operator in the style of
  `applyStmtOp_sortSlice_exact`), `randIntn` excepted: the effect gives the constructor, the
  frame and the bounds — not, say, that `allocNew`'s value is the address `s.heap.size`, nor
  what an in-place `appendSlice` or a `copySlice` leaves INSIDE the backing it writes.
* That an `int` result is in range for its kind; the `valueShape_*_normal` lemmas are
  constructor facts (any address is normal at any pointer type, …), say nothing at a named
  (`.defined`) type, and are useful with `isNormalForTy_sound`, which is not in the contract.
* The TRACE a value form returns, and which `appendSpill` width a spill consults (the stream
  statement gives «some width»).
* WHICH stop a non-address target gives: a nil target is the nil-dereference panic and any
  other non-address is `stuck`, at the point where the arm checks its target, which an operand
  refusal can precede; only «it does not succeed» is stated. When the target is the ONLY operand
  (`makeMap`/`makeChan` with no hint or capacity) the value form on `[]` succeeds where the
  machine stops, and the step is the machine's own `retV_stmtOpK_apply_panic` / `_error`.
* The machine-side theorems this module rests on or points to (`applyStmtOp_plan_tame`,
  `applyStmtOp_commit_noPanic`, `applyStmtOp_wf`, `Mem.store_noPanic`, the consumption
  theorems of `StepFnFacts.lean`) are not in the comparator contract.
-/

namespace GoLean.GoCore.Machine

open GoLean

variable {ctx : ProgramCtx}

/-! ## Transfer along the equation: the validate phase

For an operator with a value form the two plans fail together, with the same stop, and succeed
together. So every fact about the machine's validate phase — which refusal, which panic, what
it draws from the stream — is a fact about the value form's, at any target address. -/

theorem applyStmtOpValue_plan_error_iff {s : Store} {choices : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {e : Stop} (h : op.hasValueForm = true) (loc : Loc) :
    applyStmtOpValue.plan ctx s choices op nt vs = .error e
      ↔ applyStmtOp.plan ctx s choices op nt (.addr loc :: vs) = .error e := by
  rw [applyStmtOp_plan_eq_value h]
  cases applyStmtOpValue.plan ctx s choices op nt vs with
  | error e' => exact ⟨fun h => (by cases h; rfl), fun h => (by cases h; rfl)⟩
  | ok c => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

theorem applyStmtOpValue_plan_ok_iff {s : Store} {choices : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {loc : Loc}
    {c : Commit (Store × Choices × List PickRecord × AccessTrace)} (h : op.hasValueForm = true) :
    applyStmtOp.plan ctx s choices op nt (.addr loc :: vs) = .ok c
      ↔ ∃ cv, applyStmtOpValue.plan ctx s choices op nt vs = .ok cv
          ∧ c = storeValueInto ctx loc cv := by
  rw [applyStmtOp_plan_eq_value h]
  cases applyStmtOpValue.plan ctx s choices op nt vs with
  | error e' => exact ⟨fun h => (by cases h), fun ⟨_, h, _⟩ => (by cases h)⟩
  | ok cv =>
    exact ⟨fun h => ⟨cv, rfl, (by cases h; rfl)⟩, fun ⟨cv', h1, h2⟩ => (by cases h1; rw [h2]; rfl)⟩

/-- A value form's commit never raises a recoverable panic: a panic is the validate phase's
(the machine's `applyStmtOp_commit_noPanic`, through the equation — were the value commit to
panic, so would the machine's). -/
theorem applyStmtOpValue_commit_noPanic (s : Store) (choices : Choices) (op : StmtOp) (nt : Nat)
    (vs : List GoValue) : PlanNoPanic (applyStmtOpValue.plan ctx s choices op nt vs) := by
  intro cv hcv s₀ msg hp
  cases hv : op.hasValueForm with
  | false =>
    obtain ⟨m, hm⟩ := applyStmtOpValue_plan_of_not_hasValueForm (ctx := ctx) (s := s)
      (choices := choices) (nt := nt) (vs := vs) hv
    rw [hm] at hcv; cases hcv
  | true =>
    have hm := (applyStmtOpValue_plan_ok_iff (loc := .base ⟨0⟩) hv).mpr ⟨cv, hcv, rfl⟩
    refine applyStmtOp_commit_noPanic s choices op nt _ _ hm s₀ msg ?_
    show (cv s₀ >>= storeValue ctx (.base ⟨0⟩)) = _
    rw [hp]; rfl

/-! ## The target must be an address

The equation is stated at a target `.addr loc`. That is no restriction on a successful apply:
the machine's validate phase checks its target with `valueAsLoc`, so a plan that succeeds had
an address there. Together: for a targeted operator other than `randIntn`, the machine's plan
succeeds EXACTLY when the target is an address and the value plan succeeds
(`applyStmtOp_plan_ok_iff_value`). `randIntn` is the one operator whose first operand may
legitimately not be a target (`applyStmtOp_plan_randIntn_untargeted`). -/

theorem valueAsLoc_post (tv : GoValue) : Post (valueAsLoc tv) fun loc => tv = .addr loc := by
  intro loc h
  cases tv <;> first | (cases h; rfl) | cases h

section
local macro_rules | `(tactic| nd_db) => `(tactic| exact valueAsLoc_post _)

/-- Close a swept goal: the target's `valueAsLoc` answered, and the target is the head operand. -/
local macro "wv_target" : tactic => `(tactic| (
  all_goals first
    | exact Post.pure ⟨_, ‹_ = GoValue.addr _›⟩
    | exact Post.pure
        ⟨_, ((List.cons.injEq _ _ _ _).mp ‹_ :: _ = _›).1.trans ‹_ = GoValue.addr _›⟩))

theorem applyStmtOpCore_plan_target_allocNew {s : Store} {tv : GoValue} {vs : List GoValue} {typ : Ty} :
    Post (applyStmtOpCore.plan ctx s (.allocNew typ) (tv :: vs)) fun _ => ∃ loc, tv = .addr loc := by
  unfold applyStmtOpCore.plan; nd; wv_target

theorem applyStmtOpCore_plan_target_makeSlice {s : Store} {tv : GoValue} {vs : List GoValue} {elem : Ty} {hasCap : Bool} :
    Post (applyStmtOpCore.plan ctx s (.makeSlice elem hasCap) (tv :: vs)) fun _ => ∃ loc, tv = .addr loc := by
  unfold applyStmtOpCore.plan; nd; wv_target

theorem applyStmtOpCore_plan_target_makeMap {s : Store} {tv : GoValue} {vs : List GoValue} {hasSpace : Bool} :
    Post (applyStmtOpCore.plan ctx s (.makeMap hasSpace) (tv :: vs)) fun _ => ∃ loc, tv = .addr loc := by
  unfold applyStmtOpCore.plan; nd; wv_target

theorem applyStmtOpCore_plan_target_makeChan {s : Store} {tv : GoValue} {vs : List GoValue} {elem : Ty} {hasCap : Bool} :
    Post (applyStmtOpCore.plan ctx s (.makeChan elem hasCap) (tv :: vs)) fun _ => ∃ loc, tv = .addr loc := by
  unfold applyStmtOpCore.plan; nd; wv_target

theorem applyStmtOpCore_plan_target_copySlice {s : Store} {tv : GoValue} {vs : List GoValue}  :
    Post (applyStmtOpCore.plan ctx s .copySlice (tv :: vs)) fun _ => ∃ loc, tv = .addr loc := by
  unfold applyStmtOpCore.plan; nd; wv_target

theorem applyStmtOp_plan_target_appendSlice {s : Store} {choices : Choices} {nt : Nat}
    {tv : GoValue} {vs : List GoValue} {elem : Ty} :
    Post (applyStmtOp.plan ctx s choices (.appendSlice elem) nt (tv :: vs))
      fun _ => ∃ loc, tv = .addr loc := by
  unfold applyStmtOp.plan; nd; wv_target

theorem applyStmtOp_plan_target_randIntn {s : Store} {choices : Choices} {nt : Nat}
    {tv b : GoValue} {rest : List GoValue} :
    Post (applyStmtOp.plan ctx s choices .randIntn nt (tv :: b :: rest))
      fun _ => ∃ loc, tv = .addr loc := by
  unfold applyStmtOp.plan; nd
  all_goals first
    | exact Post.pure
        ⟨_, ((List.cons.injEq _ _ _ _).mp ‹_ :: _ = _›).1.trans ‹_ = GoValue.addr _›⟩
    | (have hc := ‹_ :: _ = _›; simp at hc)

/-- **A wide operator that succeeds had an address for its target.** For `randIntn` the claim
is about its TARGETED operand list (two operands): with one operand there is no target, and the
operand is the bound (`applyStmtOp_plan_randIntn_untargeted`). -/
theorem applyStmtOp_plan_target {s : Store} {choices : Choices} {op : StmtOp} {nt : Nat}
    {tv : GoValue} {vs : List GoValue} (h : op.hasValueForm = true)
    (hr : op = .randIntn → vs ≠ []) :
    Post (applyStmtOp.plan ctx s choices op nt (tv :: vs)) fun _ => ∃ loc, tv = .addr loc := by
  cases op with
  | appendSlice elem => exact applyStmtOp_plan_target_appendSlice
  | randIntn =>
    cases vs with
    | nil => exact absurd rfl (hr rfl)
    | cons b rest => exact applyStmtOp_plan_target_randIntn
  | allocNew typ =>
    unfold applyStmtOp.plan
    exact Post.bind applyStmtOpCore_plan_target_allocNew fun _ h => Post.pure h
  | makeSlice elem hasCap =>
    unfold applyStmtOp.plan
    exact Post.bind applyStmtOpCore_plan_target_makeSlice fun _ h => Post.pure h
  | makeMap hasSpace =>
    unfold applyStmtOp.plan
    exact Post.bind applyStmtOpCore_plan_target_makeMap fun _ h => Post.pure h
  | makeChan elem hasCap =>
    unfold applyStmtOp.plan
    exact Post.bind applyStmtOpCore_plan_target_makeChan fun _ h => Post.pure h
  | copySlice =>
    unfold applyStmtOp.plan
    exact Post.bind applyStmtOpCore_plan_target_copySlice fun _ h => Post.pure h
  | _ => cases h

/-- A target that is not an address: the machine's plan does not succeed. (WHICH stop it gives
is not stated here: a nil target is the nil-dereference panic and any other non-address is
`stuck`, raised where the arm checks its target — after the operand checks in some arms — so
an earlier operand refusal can come first.) -/
theorem applyStmtOp_plan_error_of_target {s : Store} {choices : Choices} {op : StmtOp} {nt : Nat}
    {tv : GoValue} {vs : List GoValue} (h : op.hasValueForm = true)
    (hr : op = .randIntn → vs ≠ []) (hnot : ∀ loc, tv ≠ .addr loc) :
    ∃ e, applyStmtOp.plan ctx s choices op nt (tv :: vs) = .error e := by
  cases hp : applyStmtOp.plan ctx s choices op nt (tv :: vs) with
  | error e => exact ⟨e, rfl⟩
  | ok c =>
    obtain ⟨loc, hl⟩ := applyStmtOp_plan_target h hr c hp
    exact absurd hl (hnot loc)

/-- **The machine's wide operator succeeds exactly when its target is an address and its value
form succeeds**, and then its commit is the value form's followed by the store. -/
theorem applyStmtOp_plan_ok_iff_value {s : Store} {choices : Choices} {op : StmtOp} {nt : Nat}
    {tv : GoValue} {vs : List GoValue}
    {c : Commit (Store × Choices × List PickRecord × AccessTrace)}
    (h : op.hasValueForm = true) (hr : op = .randIntn → vs ≠ []) :
    applyStmtOp.plan ctx s choices op nt (tv :: vs) = .ok c
      ↔ ∃ loc cv, tv = .addr loc ∧ applyStmtOpValue.plan ctx s choices op nt vs = .ok cv
          ∧ c = storeValueInto ctx loc cv := by
  constructor
  · intro hc
    obtain ⟨loc, rfl⟩ := applyStmtOp_plan_target h hr _ hc
    obtain ⟨cv, hcv, rfl⟩ := (applyStmtOpValue_plan_ok_iff h).mp hc
    exact ⟨loc, cv, rfl, hcv, rfl⟩
  · rintro ⟨loc, cv, rfl, hcv, rfl⟩
    exact (applyStmtOpValue_plan_ok_iff h).mpr ⟨cv, hcv, rfl⟩

end

/-! ## No dead cell

The value forms create no dead cell (`Store.NoDead`, `DeadCell.lean`): what the operator's own
allocation and element writes leave is `NoDead` when the store was. -/

theorem applyStmtOpValueCore.plan_noDead {s : Store} {op : StmtOp} {vs : List GoValue} :
    Post (applyStmtOpValueCore.plan ctx s op vs) fun c => Commit.NoDead c fun r => r.2.1 := by
  unfold applyStmtOpValueCore.plan; nd
macro_rules | `(tactic| nd_db) => `(tactic| exact applyStmtOpValueCore.plan_noDead)

theorem applyStmtOpValue.plan_noDead {s : Store} {choices : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} :
    Post (applyStmtOpValue.plan ctx s choices op nt vs) fun c => Commit.NoDead c fun r => r.2.1 := by
  unfold applyStmtOpValue.plan; nd

theorem applyStmtOpValue_noDead {s : Store} {choices : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} (h : s.NoDead) :
    Post (applyStmtOpValue ctx s choices op nt vs) fun r => r.2.1.NoDead := by
  unfold applyStmtOpValue
  exact Post.bind applyStmtOpValue.plan_noDead fun c hc => hc s h

/-! ## Strictness: what a value form can stop with

As the machine's operator: a refusal, `fatal`, or a recoverable panic — never a deadlock, a race
report or fuel exhaustion — in the validate phase and in every commit. -/

theorem applyStmtOpValue_plan_tame {s : Store} {choices : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} : ErrP Stop.Tame (applyStmtOpValue.plan ctx s choices op nt vs) := by
  intro e he
  cases hv : op.hasValueForm with
  | false =>
    obtain ⟨m, hm⟩ := applyStmtOpValue_plan_of_not_hasValueForm (ctx := ctx) (s := s)
      (choices := choices) (nt := nt) (vs := vs) hv
    rw [hm] at he; cases he; trivial
  | true =>
    exact applyStmtOp_plan_tame _ ((applyStmtOpValue_plan_error_iff hv (.base ⟨0⟩)).mp he)

theorem applyStmtOpValue_commit_tame {s : Store} {choices : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {cv : Commit (GoValue × Store × Choices × List PickRecord × AccessTrace)}
    (hcv : applyStmtOpValue.plan ctx s choices op nt vs = .ok cv) (s₀ : Store) :
    ErrP Stop.Tame (cv s₀) := by
  intro e he
  cases hv : op.hasValueForm with
  | false =>
    obtain ⟨m, hm⟩ := applyStmtOpValue_plan_of_not_hasValueForm (ctx := ctx) (s := s)
      (choices := choices) (nt := nt) (vs := vs) hv
    rw [hm] at hcv; cases hcv
  | true =>
    have hm := (applyStmtOpValue_plan_ok_iff (loc := .base ⟨0⟩) hv).mpr ⟨cv, hcv, rfl⟩
    have hc := applyStmtOp_plan_commitOk (ctx := ctx) (s := s) (ch := choices) (op := op)
      (nt := nt) (vs := .addr (.base ⟨0⟩) :: vs)
    unfold CommitOk at hc
    refine hc _ hm s₀ e ?_
    show (cv s₀ >>= storeValue ctx (.base ⟨0⟩)) = _
    rw [he]; rfl

/-! ## The memory frame: what a write leaves alone -/

theorem Store.updateCell_frame {s s' : Store} {a : Addr} {f : HeapCell → Except Stop HeapCell}
    (h : s.updateCell a f = .ok s') :
    s'.heap.size = s.heap.size
      ∧ ∀ b : Addr, b ≠ a → Heap.lookup s'.heap (.base b) = Heap.lookup s.heap (.base b) := by
  unfold Store.updateCell at h
  split at h
  · rename_i hi
    cases hf : f s.heap[a.id] with
    | error e => rw [hf] at h; cases h
    | ok c =>
      rw [hf] at h; cases h
      refine ⟨by simp, fun b hb => ?_⟩
      have hne : a.id ≠ b.id := fun e => hb (by cases a; cases b; simp_all)
      rw [Heap.lookup_base, Heap.lookup_base, Array.getElem?_set]
      simp only [hne, ↓reduceIte]
  · cases h

theorem storeLoc_frame {s s' : Store} {l : Loc} {v : GoValue} (h : storeLoc ctx s l v = .ok s') :
    s'.heap.size = s.heap.size
      ∧ ∀ b : Addr, b ≠ (Loc.rootPath l).1 →
          Heap.lookup s'.heap (.base b) = Heap.lookup s.heap (.base b) := by
  unfold storeLoc at h
  exact Store.updateCell_frame h

theorem Mem.store_frame {s s' : Store} {l : Loc} {v : GoValue} {tr : AccessTrace}
    (h : Mem.store ctx s l v = .ok (s', tr)) :
    s'.heap.size = s.heap.size
      ∧ ∀ b : Addr, b ≠ (Loc.rootPath l).1 →
          Heap.lookup s'.heap (.base b) = Heap.lookup s.heap (.base b) := by
  unfold Mem.store at h
  cases hs : storeLoc ctx s l v with
  | error e => rw [hs] at h; cases h
  | ok s₁ => rw [hs] at h; cases h; exact storeLoc_frame hs

theorem Mem.storeElems_frame {base : Loc} :
    ∀ {vs : List GoValue} {s s' : Store} {start : Nat} {tr : AccessTrace},
      Mem.storeElems ctx s base start vs = .ok (s', tr) →
      s'.heap.size = s.heap.size
        ∧ ∀ b : Addr, b ≠ (Loc.rootPath base).1 →
            Heap.lookup s'.heap (.base b) = Heap.lookup s.heap (.base b)
  | [], s, s', start, tr, h => by
    unfold Mem.storeElems at h; cases h; exact ⟨rfl, fun _ _ => rfl⟩
  | v :: vs, s, s', start, tr, h => by
    unfold Mem.storeElems at h
    cases h1 : Mem.store ctx s (.index base (Int.ofNat start)) v with
    | error e => rw [h1] at h; cases h
    | ok r1 =>
      rw [h1] at h
      cases h2 : Mem.storeElems ctx r1.1 base (start + 1) vs with
      | error e => simp [h2, bind, Except.bind] at h
      | ok r2 =>
        simp only [h2, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        obtain ⟨hs1, hf1⟩ := Mem.store_frame (tr := r1.2) (s' := r1.1) h1
        obtain ⟨hs2, hf2⟩ := Mem.storeElems_frame (tr := r2.2) (s' := r2.1) h2
        exact ⟨hs2.trans hs1, fun b hb => (hf2 b hb).trans (hf1 b hb)⟩

theorem Mem.storeRun_frame {s s' : Store} {sl : SliceValue} {start : Nat} {vs : List GoValue}
    {tr : AccessTrace} (h : Mem.storeRun ctx s sl start vs = .ok (s', tr)) :
    s'.heap.size = s.heap.size
      ∧ ∀ b : Addr, some b ≠ sl.base.map (fun l => (Loc.rootPath l).1) →
          Heap.lookup s'.heap (.base b) = Heap.lookup s.heap (.base b) := by
  unfold Mem.storeRun at h
  split at h
  · rename_i bl hbase
    obtain ⟨hs, hf⟩ := Mem.storeElems_frame h
    exact ⟨hs, fun b hb => hf b (fun e => hb (by rw [hbase, e]; rfl))⟩
  · split at h
    · cases h; exact ⟨rfl, fun _ _ => rfl⟩
    · cases h

theorem Store.alloc_frame {s s' : Store} {v : GoValue} {ty : Ty} {l : Loc}
    (h : Store.alloc ctx s v ty = .ok (l, s')) :
    ∀ b : Addr, b.id < s.heap.size →
      Heap.lookup s'.heap (.base b) = Heap.lookup s.heap (.base b) := by
  unfold Store.alloc at h
  cases hn : normalizeValueForTy ctx ty v with
  | error e => simp [hn, Bind.bind, Except.bind] at h
  | ok v' =>
    simp only [hn, Bind.bind, Except.bind, pure, Except.pure, Store.allocCell, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    intro b hb
    rw [Heap.lookup_base, Heap.lookup_base, Array.getElem?_push_lt hb, Array.getElem?_eq_getElem hb]

theorem Store.allocCell_frame (s : Store) (c : HeapCell) :
    ∀ b : Addr, b.id < s.heap.size →
      Heap.lookup (s.allocCell c).2.heap (.base b) = Heap.lookup s.heap (.base b) := by
  intro b hb
  simp only [Store.allocCell]
  rw [Heap.lookup_base, Heap.lookup_base, Array.getElem?_push_lt hb, Array.getElem?_eq_getElem hb]

/-! ## What a value form does: the value's shape, the store's growth, the frame, well-formedness -/

/-- The constructor of the value each targeted operator returns. -/
def StmtOp.valueShape : StmtOp → GoValue → Prop
  | .allocNew _, v => ∃ loc, v = .addr loc
  | .makeSlice _ _, v => ∃ sv, v = .slice sv
  | .appendSlice _, v => ∃ sv, v = .slice sv
  | .makeMap _, v => ∃ mv, v = .map mv
  | .makeChan _ _, v => ∃ cv, v = .chan cv
  | .copySlice, v => ∃ n, v = .int n .int
  | .randIntn, v => ∃ n, v = .int n .int
  | .mapAssign _ _, _ | .mapDelete _, _ | .clearMap, _ | .clearSlice _, _ | .sortSlice _, _
  | .print _, _ => False

/-- The one root cell a value form may write besides its own fresh cell: the destination
backing of `copySlice`, the appended-to backing of `appendSlice` (written only when the append
fits in place). Every other operator writes no existing cell. -/
def wideWrittenRoot? : StmtOp → List GoValue → Option Addr
  | .copySlice, [.slice sl, _] => sl.base.map fun l => (Loc.rootPath l).1
  | .appendSlice _, [.slice sl, _] => sl.base.map fun l => (Loc.rootPath l).1
  | _, _ => none

/-- What a successful value form did, in one statement. -/
structure WideEffect (ctx : ProgramCtx) (op : StmtOp) (vs : List GoValue) (s : Store)
    (v : GoValue) (s₁ : Store) : Prop where
  /-- The value has the operator's constructor. -/
  shape : op.valueShape v
  /-- The heap grew by at most one cell. -/
  size : s.heap.size ≤ s₁.heap.size ∧ s₁.heap.size ≤ s.heap.size + 1
  /-- Every existing root cell but the operator's written backing is as it was. -/
  frame : ∀ b : Addr, b.id < s.heap.size → some b ≠ wideWrittenRoot? op vs →
    Heap.lookup s₁.heap (.base b) = Heap.lookup s.heap (.base b)
  /-- If the heap grew, the operator wrote NO existing cell (its one write was the fresh cell):
  in particular a spilling `appendSlice` leaves its old backing as it was. -/
  grown : s₁.heap.size = s.heap.size + 1 → ∀ b : Addr, b.id < s.heap.size →
    Heap.lookup s₁.heap (.base b) = Heap.lookup s.heap (.base b)
  /-- Well-formedness is kept, the allocator does not go back, and the value is bounded. -/
  wf : StateWf ctx s → goValueListSup vs ≤ s.nextAddr →
    StmtOpPres ctx s s₁ ∧ GoValue.locSup v ≤ s₁.nextAddr

/-! The four things a value form's commit can do: allocate a value cell, allocate a payload
cell, write a run of elements in place, or nothing. -/

theorem WideEffect.of_alloc {op : StmtOp} {vs : List GoValue} {s s' : Store} {val : GoValue}
    {ty : Ty} {l : Loc} {mk : Loc → GoValue} (hshape : op.valueShape (mk l))
    (ha : Store.alloc ctx s val ty = .ok (l, s'))
    (hval : StateWf ctx s → goValueListSup vs ≤ s.nextAddr → GoValue.locSup val ≤ s.nextAddr)
    (hmk : GoValue.locSup (mk l) ≤ Loc.locSup l) : WideEffect ctx op vs s (mk l) s' := by
  obtain ⟨hl, hsz⟩ := Store.alloc_shape ha
  refine ⟨hshape, ⟨by omega, by omega⟩, fun b hb _ => Store.alloc_frame ha b hb,
    fun _ b hb => Store.alloc_frame ha b hb, fun hw hvs => ?_⟩
  obtain ⟨hw', hloc, hn⟩ := alloc_wf hw (hval hw hvs) ha
  exact ⟨⟨hw', by omega⟩, Nat.le_trans hmk hloc⟩

theorem WideEffect.of_allocCell {op : StmtOp} {vs : List GoValue} {s : Store} {cell : HeapCell}
    {mk : Loc → GoValue} (hshape : op.valueShape (mk (s.allocCell cell).1))
    (hcell : HeapCell.locSup cell = 0) (hn : HeapCell.normal ctx.types cell = true)
    (hmk : ∀ l, GoValue.locSup (mk l) ≤ Loc.locSup l) :
    WideEffect ctx op vs s (mk (s.allocCell cell).1) (s.allocCell cell).2 := by
  refine ⟨hshape, ⟨by simp [Store.allocCell], by simp [Store.allocCell]⟩,
    fun b hb _ => Store.allocCell_frame s cell b hb,
    fun _ b hb => Store.allocCell_frame s cell b hb, fun hw hvs => ?_⟩
  obtain ⟨hw', hloc, hnx⟩ := allocCell_wf (l := (s.allocCell cell).1) (σ' := (s.allocCell cell).2)
    hw (by omega) rfl hn
  exact ⟨⟨hw', by omega⟩, Nat.le_trans (hmk _) hloc⟩

theorem WideEffect.of_storeRun {op : StmtOp} {vs : List GoValue} {s s' : Store} {sl : SliceValue}
    {start : Nat} {vals : List GoValue} {trW : AccessTrace} {v : GoValue}
    (hshape : op.valueShape v) (hr : Mem.storeRun ctx s sl start vals = .ok (s', trW))
    (hroot : wideWrittenRoot? op vs = sl.base.map fun l => (Loc.rootPath l).1)
    (hb : StateWf ctx s → goValueListSup vs ≤ s.nextAddr → optLocSup sl.base ≤ s.nextAddr)
    (hvals : StateWf ctx s → goValueListSup vs ≤ s.nextAddr → goValueListSup vals ≤ s.nextAddr)
    (hv : StateWf ctx s → goValueListSup vs ≤ s.nextAddr → GoValue.locSup v ≤ s.nextAddr) :
    WideEffect ctx op vs s v s' := by
  obtain ⟨hsz, hf⟩ := Mem.storeRun_frame hr
  refine ⟨hshape, ⟨by omega, by omega⟩, fun b _ hne => hf b (hroot ▸ hne),
    fun hg => absurd hg (by omega), fun hw hvs => ?_⟩
  have hp := Mem.storeRun_pres hw (hb hw hvs) (hvals hw hvs) hr
  exact ⟨hp, Nat.le_trans (hv hw hvs) hp.2⟩

theorem WideEffect.of_pure {op : StmtOp} {vs : List GoValue} {s : Store} {v : GoValue}
    (hshape : op.valueShape v)
    (hv : StateWf ctx s → goValueListSup vs ≤ s.nextAddr → GoValue.locSup v ≤ s.nextAddr) :
    WideEffect ctx op vs s v s :=
  ⟨hshape, ⟨Nat.le_refl _, Nat.le_succ _⟩, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun hw hvs => ⟨stmtOpPres_refl hw, hv hw hvs⟩⟩

/-- A bind that keeps the equation of what it bound. -/
theorem _root_.GoLean.GoCore.Post.bind_eq {α β : Type} {x : Except Stop α}
    {k : α → Except Stop β} {R : β → Prop} (hk : ∀ a, x = .ok a → Post (k a) R) :
    Post (x >>= k) R := by
  intro b hb
  cases hx : x with
  | error e => rw [hx] at hb; cases hb
  | ok a => rw [hx] at hb; exact hk a hx b hb

/-- Walk a validate phase to its commits, keeping the equation of every bind. -/
local macro "wsweep" : tactic => `(tactic| (
  repeat' first
    | exact Post.error
    | exact Post.throw
    | exact Post.stuck
    | exact Post.panic
    | exact Post.unsupported
    | (refine Post.bind_eq fun _ _ => ?_)
    | dsimp only
    | split))

/-- The effect of a commit on the store its plan read. -/
def CommitEffect (ctx : ProgramCtx) (op : StmtOp) (vs : List GoValue) (s : Store) {α : Type}
    (val : α → GoValue) (st : α → Store) (c : Commit α) : Prop :=
  ∀ r, c s = .ok r → WideEffect ctx op vs s (val r) (st r)

theorem valueAsSlice_eq {v : GoValue} {sl : SliceValue} (h : valueAsSlice v = .ok sl) :
    v = .slice sl := by
  cases v <;> first | (cases h; rfl) | cases h

theorem applyStmtOpValueCore_effect_allocNew {s : Store} {vs : List GoValue} {typ : Ty} :
    Post (applyStmtOpValueCore.plan ctx s (.allocNew typ) vs)
      (CommitEffect ctx (.allocNew typ) vs s (·.1) (·.2.1)) := by
  unfold applyStmtOpValueCore.plan
  wsweep
  refine Post.pure fun r hr => ?_
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
  obtain ⟨⟨l, s'⟩, ha, rfl⟩ := hr
  exact WideEffect.of_alloc (mk := GoValue.addr) ⟨_, rfl⟩ ha
    (fun _ hvs => by simp only [goValueListSup] at hvs; omega) (Nat.le_refl _)

theorem applyStmtOpValueCore_effect_makeSlice {s : Store} {vs : List GoValue} {elem : Ty}
    {hasCap : Bool} :
    Post (applyStmtOpValueCore.plan ctx s (.makeSlice elem hasCap) vs)
      (CommitEffect ctx (.makeSlice elem hasCap) vs s (·.1) (·.2.1)) := by
  unfold applyStmtOpValueCore.plan
  wsweep
  all_goals (
    refine Post.pure fun r hr => ?_
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
    obtain ⟨⟨l, s'⟩, ha, rfl⟩ := hr
    exact WideEffect.of_alloc
      (mk := fun l => .slice { base := some l, offset := 0, len := _, cap := _ }) ⟨_, rfl⟩ ha
      (fun _ _ => by rw [buildDefaultArrayValue_locSup ‹_›]; exact Nat.zero_le _) (Nat.le_refl _))

theorem applyStmtOpValueCore_effect_makeMap {s : Store} {vs : List GoValue} {hasSpace : Bool} :
    Post (applyStmtOpValueCore.plan ctx s (.makeMap hasSpace) vs)
      (CommitEffect ctx (.makeMap hasSpace) vs s (·.1) (·.2.1)) := by
  unfold applyStmtOpValueCore.plan
  wsweep
  all_goals (
    refine Post.pure fun r hr => ?_
    cases hr
    exact WideEffect.of_allocCell (mk := fun l => .map { base := some l }) ⟨_, rfl⟩ rfl rfl
      (fun _ => Nat.le_refl _))

theorem applyStmtOpValueCore_effect_makeChan {s : Store} {vs : List GoValue} {elem : Ty}
    {hasCap : Bool} :
    Post (applyStmtOpValueCore.plan ctx s (.makeChan elem hasCap) vs)
      (CommitEffect ctx (.makeChan elem hasCap) vs s (·.1) (·.2.1)) := by
  unfold applyStmtOpValueCore.plan
  wsweep
  all_goals (
    refine Post.pure fun r hr => ?_
    cases hr
    exact WideEffect.of_allocCell (mk := fun l => .chan { base := some l }) ⟨_, rfl⟩ rfl rfl
      (fun _ => Nat.le_refl _))

theorem applyStmtOpValueCore_effect_copySlice {s : Store} {vs : List GoValue} :
    Post (applyStmtOpValueCore.plan ctx s .copySlice vs)
      (CommitEffect ctx .copySlice vs s (·.1) (·.2.1)) := by
  unfold applyStmtOpValueCore.plan
  wsweep
  refine Post.pure fun r hr => ?_
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
  obtain ⟨⟨s', trW⟩, hrun, rfl⟩ := hr
  rename_i dstV srcV dst hdst src hsrc _ _ _ _ vals hload
  cases valueAsSlice_eq hdst
  refine WideEffect.of_storeRun ⟨_, rfl⟩ hrun rfl (fun _ hvs => ?_) (fun hw _ => ?_)
    (fun _ _ => Nat.zero_le _)
  · have := valueAsSlice_locSup hdst
    simp only [goValueListSup] at hvs; omega
  · exact Nat.le_trans (Mem.loadRun_locSup hload) hw.heap_le

theorem applyStmtOpValue_plan_effect_appendSlice {s : Store} {choices : Choices} {nt : Nat}
    {vs : List GoValue} {elem : Ty} :
    Post (applyStmtOpValue.plan ctx s choices (.appendSlice elem) nt vs)
      (CommitEffect ctx (.appendSlice elem) vs s (·.1) (·.2.1)) := by
  unfold applyStmtOpValue.plan
  wsweep
  · -- the append fits: the element run written in place
    refine Post.pure fun r hr => ?_
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
    obtain ⟨⟨s', trW⟩, hrun, rfl⟩ := hr
    rename_i sliceV elemsV sl hsl el hel _ _ _ _ ev hload hfit
    cases valueAsSlice_eq hsl
    have hbase : goValueListSup [GoValue.slice sl, elemsV] ≤ s.nextAddr →
        optLocSup sl.base ≤ s.nextAddr := fun hvs => by
      have := valueAsSlice_locSup hsl
      simp only [goValueListSup] at hvs; omega
    exact WideEffect.of_storeRun ⟨_, rfl⟩ hrun rfl (fun _ hvs => hbase hvs)
      (fun hw _ => Nat.le_trans (Mem.loadSlice_locSup hload) hw.heap_le) (fun _ hvs => hbase hvs)
  · -- the append spills: a fresh backing
    refine Post.pure fun r hr => ?_
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
    obtain ⟨⟨l, s'⟩, ha, rfl⟩ := hr
    rename_i sliceV elemsV sl hsl el hel _ _ _ _ ev hload _ _ _ _ _ _ old hold _ _ backing hback
    exact WideEffect.of_alloc
      (mk := fun l => .slice { base := some l, offset := 0, len := _, cap := _ }) ⟨_, rfl⟩ ha
      (fun hw _ => Nat.le_trans (buildAppendBackingValue_locSup hback)
        (Nat.max_le.mpr ⟨Nat.le_trans (Mem.loadSlice_locSup hold) hw.heap_le,
          Nat.le_trans (Mem.loadSlice_locSup hload) hw.heap_le⟩))
      (Nat.le_refl _)

theorem applyStmtOpValue_plan_effect_randIntn {s : Store} {choices : Choices} {nt : Nat}
    {vs : List GoValue} :
    Post (applyStmtOpValue.plan ctx s choices .randIntn nt vs)
      (CommitEffect ctx .randIntn vs s (·.1) (·.2.1)) := by
  unfold applyStmtOpValue.plan
  wsweep
  refine Post.pure fun r hr => ?_
  cases hr
  exact WideEffect.of_pure ⟨_, rfl⟩ (fun _ _ => Nat.zero_le _)

/-- A core value plan's effect, lifted beside the stream. -/
theorem commitEffect_lift {op : StmtOp} {vs : List GoValue} {s : Store} {choices : Choices}
    {c : Commit (GoValue × Store × AccessTrace)}
    (hc : CommitEffect ctx op vs s (·.1) (·.2.1) c) :
    CommitEffect ctx op vs s (·.1) (·.2.1)
      (fun s => do
        let (v, s₁, tr) ← c s
        return (v, s₁, choices, ([] : List PickRecord), tr)) := by
  intro r hr
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  exact hc x hx

/-- **What a successful value plan's commit does**, for every operator. -/
theorem applyStmtOpValue_plan_effect {s : Store} {choices : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} :
    Post (applyStmtOpValue.plan ctx s choices op nt vs)
      (CommitEffect ctx op vs s (·.1) (·.2.1)) := by
  cases op with
  | appendSlice elem => exact applyStmtOpValue_plan_effect_appendSlice
  | randIntn => exact applyStmtOpValue_plan_effect_randIntn
  | allocNew typ =>
    unfold applyStmtOpValue.plan
    exact Post.bind applyStmtOpValueCore_effect_allocNew fun _ hc => Post.pure (commitEffect_lift hc)
  | makeSlice elem hasCap =>
    unfold applyStmtOpValue.plan
    exact Post.bind applyStmtOpValueCore_effect_makeSlice fun _ hc => Post.pure (commitEffect_lift hc)
  | makeMap hasSpace =>
    unfold applyStmtOpValue.plan
    exact Post.bind applyStmtOpValueCore_effect_makeMap fun _ hc => Post.pure (commitEffect_lift hc)
  | makeChan elem hasCap =>
    unfold applyStmtOpValue.plan
    exact Post.bind applyStmtOpValueCore_effect_makeChan fun _ hc => Post.pure (commitEffect_lift hc)
  | copySlice =>
    unfold applyStmtOpValue.plan
    exact Post.bind applyStmtOpValueCore_effect_copySlice fun _ hc => Post.pure (commitEffect_lift hc)
  | mapAssign _ _ | mapDelete _ | clearMap | clearSlice _ | sortSlice _ | print _ =>
    intro c hc
    simp only [applyStmtOpValue.plan, applyStmtOpValueCore.plan] at hc
    cases hc

/-- **What a successful value form did**: the value has the operator's constructor; the heap
grew by at most one cell; every existing root cell but the operator's written backing is
untouched; well-formedness is kept and the value is bounded by the allocator. -/
theorem applyStmtOpValue_effect {s s₁ : Store} {choices ch' : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {v : GoValue} {ps : List PickRecord} {tr : AccessTrace}
    (h : applyStmtOpValue ctx s choices op nt vs = .ok (v, s₁, ch', ps, tr)) :
    WideEffect ctx op vs s v s₁ := by
  unfold applyStmtOpValue at h
  rw [bind_eq_ok] at h
  obtain ⟨c, hc, hcs⟩ := h
  exact applyStmtOpValue_plan_effect c hc _ hcs

/-! The value is normal at the UNNAMED type its constructor belongs to — constructor facts (any
address is normal at any pointer type, any slice value at any slice type, …; `rfl`), recorded so
a consumer need not unfold `isNormalForTy`. They say nothing at a named (`.defined`) type, and
an `int` result — `copySlice`'s count, `randIntn`'s pick — is an `.int _ .int` whose range is
not stated. -/

theorem valueShape_allocNew_normal {types : TypeEnv} {typ : Ty} {v : GoValue}
    (h : (StmtOp.allocNew typ).valueShape v) (t : Ty) : isNormalForTy types (.pointer t) v = true := by
  obtain ⟨l, rfl⟩ := h; rfl

theorem valueShape_makeSlice_normal {types : TypeEnv} {elem : Ty} {hasCap : Bool} {v : GoValue}
    (h : (StmtOp.makeSlice elem hasCap).valueShape v) (t : Ty) :
    isNormalForTy types (.slice t) v = true := by
  obtain ⟨sv, rfl⟩ := h; rfl

theorem valueShape_appendSlice_normal {types : TypeEnv} {elem : Ty} {v : GoValue}
    (h : (StmtOp.appendSlice elem).valueShape v) (t : Ty) :
    isNormalForTy types (.slice t) v = true := by
  obtain ⟨sv, rfl⟩ := h; rfl

theorem valueShape_makeMap_normal {types : TypeEnv} {hasSpace : Bool} {v : GoValue}
    (h : (StmtOp.makeMap hasSpace).valueShape v) (k t : Ty) :
    isNormalForTy types (.map k t) v = true := by
  obtain ⟨mv, rfl⟩ := h; rfl

theorem valueShape_makeChan_normal {types : TypeEnv} {elem : Ty} {hasCap : Bool} {v : GoValue}
    (h : (StmtOp.makeChan elem hasCap).valueShape v) (d : ChanDir) (t : Ty) :
    isNormalForTy types (.chan d t) v = true := by
  obtain ⟨cv, rfl⟩ := h; rfl

/-! The effect's clauses, each as its own statement (so that each is a frozen statement of the
contract in its own right, not only through the definition of `WideEffect`). -/

theorem applyStmtOpValue_shape {s s₁ : Store} {choices ch' : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {v : GoValue} {ps : List PickRecord} {tr : AccessTrace}
    (h : applyStmtOpValue ctx s choices op nt vs = .ok (v, s₁, ch', ps, tr)) :
    op.valueShape v := (applyStmtOpValue_effect h).shape

theorem applyStmtOpValue_size {s s₁ : Store} {choices ch' : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {v : GoValue} {ps : List PickRecord} {tr : AccessTrace}
    (h : applyStmtOpValue ctx s choices op nt vs = .ok (v, s₁, ch', ps, tr)) :
    s.heap.size ≤ s₁.heap.size ∧ s₁.heap.size ≤ s.heap.size + 1 := (applyStmtOpValue_effect h).size

/-- Every existing root cell but the backing the operator may write is as it was. -/
theorem applyStmtOpValue_frame {s s₁ : Store} {choices ch' : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {v : GoValue} {ps : List PickRecord} {tr : AccessTrace}
    (h : applyStmtOpValue ctx s choices op nt vs = .ok (v, s₁, ch', ps, tr))
    {b : Addr} (hb : b.id < s.heap.size) (hne : some b ≠ wideWrittenRoot? op vs) :
    Heap.lookup s₁.heap (.base b) = Heap.lookup s.heap (.base b) :=
  (applyStmtOpValue_effect h).frame b hb hne

/-- If the heap grew, NO existing root cell was written — a spilling `appendSlice` leaves its
old backing as it was. -/
theorem applyStmtOpValue_frame_of_growth {s s₁ : Store} {choices ch' : Choices} {op : StmtOp}
    {nt : Nat} {vs : List GoValue} {v : GoValue} {ps : List PickRecord} {tr : AccessTrace}
    (h : applyStmtOpValue ctx s choices op nt vs = .ok (v, s₁, ch', ps, tr))
    (hg : s₁.heap.size = s.heap.size + 1) {b : Addr} (hb : b.id < s.heap.size) :
    Heap.lookup s₁.heap (.base b) = Heap.lookup s.heap (.base b) :=
  (applyStmtOpValue_effect h).grown hg b hb

/-- Well-formedness is kept, the allocator does not go back, and the value is bounded by it. -/
theorem applyStmtOpValue_wf {s s₁ : Store} {choices ch' : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {v : GoValue} {ps : List PickRecord} {tr : AccessTrace}
    (h : applyStmtOpValue ctx s choices op nt vs = .ok (v, s₁, ch', ps, tr))
    (hw : StateWf ctx s) (hvs : goValueListSup vs ≤ s.nextAddr) :
    StateWf ctx s₁ ∧ s.nextAddr ≤ s₁.nextAddr ∧ GoValue.locSup v ≤ s₁.nextAddr := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := (applyStmtOpValue_effect h).wf hw hvs
  exact ⟨h1, h2, h3⟩

/-! ## The stream: which value forms draw, and what they return

The choice stream and the pick records a value form returns are the machine's — but that is
visible through the equation only when the store into a target succeeds, and a consumer with
no target cell has no such store. So it is stated of the value forms themselves: only
`appendSlice` (when it spills) and `randIntn` draw. -/

/-- Every value form but `appendSlice` and `randIntn` returns the stream untouched, no picks. -/
theorem applyStmtOpValue_no_draw {s s₁ : Store} {choices ch' : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} {v : GoValue} {ps : List PickRecord} {tr : AccessTrace}
    (hop : ∀ e, op ≠ .appendSlice e) (hr : op ≠ .randIntn)
    (h : applyStmtOpValue ctx s choices op nt vs = .ok (v, s₁, ch', ps, tr)) :
    ch' = choices ∧ ps = [] := by
  unfold applyStmtOpValue at h
  rw [bind_eq_ok] at h
  obtain ⟨c, hc, hcs⟩ := h
  cases op with
  | appendSlice e => exact absurd rfl (hop e)
  | randIntn => exact absurd rfl hr
  | _ =>
    simp only [applyStmtOpValue.plan, bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hc
    obtain ⟨c', -, rfl⟩ := hc
    simp only [bind_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hcs
    obtain ⟨x, -, -, -, rfl, rfl, -⟩ := hcs
    exact ⟨rfl, rfl⟩

/-- `appendSlice`: in place (the heap keeps its size) it draws nothing; spilling (the heap grows
by the new backing) it makes exactly one `appendSpill` consult, and returns the stream and the
pick record of that consult. -/
theorem applyStmtOpValue_appendSlice_stream {s s₁ : Store} {choices ch' : Choices} {elem : Ty}
    {nt : Nat} {vs : List GoValue} {v : GoValue} {ps : List PickRecord} {tr : AccessTrace}
    (h : applyStmtOpValue ctx s choices (.appendSlice elem) nt vs = .ok (v, s₁, ch', ps, tr)) :
    (s₁.heap.size = s.heap.size ∧ ch' = choices ∧ ps = [])
      ∨ (s₁.heap.size = s.heap.size + 1
          ∧ ∃ w, ch' = (Choices.consumeAtE .appendSpill w choices).2.1
              ∧ ps = (Choices.consumeAtE .appendSpill w choices).2.2) := by
  unfold applyStmtOpValue at h
  rw [bind_eq_ok] at h
  obtain ⟨c, hc, hcs⟩ := h
  have key : Post (applyStmtOpValue.plan ctx s choices (.appendSlice elem) nt vs) fun c =>
      ∀ r, c s = .ok r →
        (r.2.1.heap.size = s.heap.size ∧ r.2.2.1 = choices ∧ r.2.2.2.1 = [])
          ∨ (r.2.1.heap.size = s.heap.size + 1
              ∧ ∃ w, r.2.2.1 = (Choices.consumeAtE .appendSpill w choices).2.1
                  ∧ r.2.2.2.1 = (Choices.consumeAtE .appendSpill w choices).2.2) := by
    unfold applyStmtOpValue.plan
    wsweep
    · refine Post.pure fun r hr => ?_
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
      obtain ⟨⟨s', trW⟩, hrun, rfl⟩ := hr
      exact .inl ⟨(Mem.storeRun_frame hrun).1, rfl, rfl⟩
    · refine Post.pure fun r hr => ?_
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hr
      obtain ⟨⟨l, s'⟩, ha, rfl⟩ := hr
      exact .inr ⟨(Store.alloc_shape ha).2, _, rfl, rfl⟩
  exact key c hc _ hcs

/-- `randIntn`, exactly: one `intn` consult at the bound; the value is the pick, the store is
untouched, the stream and the pick record are the consult's, the trace is empty. -/
theorem applyStmtOpValue_randIntn {s : Store} {choices : Choices} {nt : Nat} {n : Int}
    (hn : ¬ n < 1) :
    applyStmtOpValue ctx s choices .randIntn nt [.int n .int]
      = .ok (.int (Choices.consumeAtE .intn n.toNat choices).1 .int, s,
          (Choices.consumeAtE .intn n.toNat choices).2.1,
          (Choices.consumeAtE .intn n.toNat choices).2.2, []) := by
  simp only [applyStmtOpValue, applyStmtOpValue.plan, hn, ↓reduceIte]
  rfl

end GoLean.GoCore.Machine

/-! ## Table slices

The value forms read the type table and nothing else of the context: under two contexts that
agree off the function, method and promotion tables (`tablesFree`, the G16 relation's
table-free half) they are the same functions. So a value-form fact proved against a slice of
the program's tables holds against the whole. -/

namespace GoLean.GoCore.TableMono
open GoLean GoLean.GoCore.Machine
variable {a b : ProgramCtx}

theorem applyStmtOpValueCore_plan_eq (h : a.tablesFree = b.tablesFree) :
    @applyStmtOpValueCore.plan a = @applyStmtOpValueCore.plan b := by
  delta applyStmtOpValueCore.plan
  simp only [types_eq h, Mem_loadRun_eq h, Mem_storeRun_eq h, Store_alloc_eq h,
    buildDefaultArrayValue_eq h]

theorem applyStmtOpValue_plan_eq (h : a.tablesFree = b.tablesFree) :
    @applyStmtOpValue.plan a = @applyStmtOpValue.plan b := by
  delta applyStmtOpValue.plan
  simp only [types_eq h, Mem_loadSlice_eq h, Mem_storeRun_eq h, Store_alloc_eq h,
    applyStmtOpValueCore_plan_eq h, buildAppendBackingValue_eq h, appendSpillFootprintCheck_eq h]

theorem applyStmtOpValue_eq (h : a.tablesFree = b.tablesFree) :
    @applyStmtOpValue a = @applyStmtOpValue b := by
  delta applyStmtOpValue
  simp only [applyStmtOpValue_plan_eq h]

theorem storeValue_eq (h : a.tablesFree = b.tablesFree) : @storeValue a = @storeValue b := by
  delta storeValue
  simp only [Mem_store_eq h]

end GoLean.GoCore.TableMono

/-! ## The step

`stepFn` at the wide apply position — the last operand arrived under `stmtOpK` — in terms of
the value form, for a targeted operator whose target is an address: the value form's outcome,
then the store into the target. Four outcomes, one equation each (the machine's own equations
`retV_stmtOpK_apply`, `_panic`, `_error` read through `applyStmtOp_eq_value`). A targeted
operator prints nothing (`stmtOpOut_of_hasValueForm`). -/

namespace GoLean.GoCore.Machine
open GoLean GoLean.GoCore.Equations
variable {ctx : ProgramCtx}

theorem stmtOpOut_of_hasValueForm {op : StmtOp} (h : op.hasValueForm = true) (vs : List GoValue) :
    stmtOpOut op vs = [] := by
  cases op <;> first | rfl | cases h

/-- The value form answers and the store into the target succeeds: one step, the statement
completes, the trace is the operator's then the store's. -/
theorem retV_stmtOpK_apply_value {s s₁ s' : Store} {v w : GoValue} {op : StmtOp} {nt : Nat}
    {done vs : List GoValue} {loc : Loc} {ch' : Choices} {ps : List PickRecord}
    {tr trT : AccessTrace} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hv : op.hasValueForm = true) (hops : (v :: done).reverse = .addr loc :: vs)
    (h : applyStmtOpValue ctx s ch op nt vs = .ok (w, s₁, ch', ps, tr))
    (hs : Mem.store ctx s₁ loc w = .ok (s', trT)) :
    stepFn ctx s (.retV v (.stmtOpK op nt done [] env k')) ch
      = .ok (.next k', s', ch', ⟨tr ++ trT, ps, []⟩) := by
  have ha : applyStmtOp ctx s ch op nt (v :: done).reverse = .ok (s', ch', ps, tr ++ trT) := by
    rw [hops, applyStmtOp_eq_value hv, h]
    show storeValue ctx loc (w, s₁, ch', ps, tr) = _
    simp only [storeValue, hs]; rfl
  rw [retV_stmtOpK_apply env k' ch ha, stmtOpOut_of_hasValueForm hv]

/-- The value form's validate phase panics: the panic unwinds over the untouched store. -/
theorem retV_stmtOpK_apply_value_panic {s : Store} {v : GoValue} {op : StmtOp} {nt : Nat}
    {done vs : List GoValue} {loc : Loc} {msg : String} (env : LocalEnv) (k' : Cont)
    (ch : Choices) (hv : op.hasValueForm = true) (hops : (v :: done).reverse = .addr loc :: vs)
    (h : applyStmtOpValue ctx s ch op nt vs = .error (.panic msg)) :
    stepFn ctx s (.retV v (.stmtOpK op nt done [] env k')) ch
      = .ok (.panicking [panicEntry msg] k', s, ch, ⟨[], [], []⟩) := by
  refine retV_stmtOpK_apply_panic env k' ch ?_
  rw [hops, applyStmtOp_eq_value hv, h]; rfl

/-- The value form refuses (any stop but a panic): the step is that stop. -/
theorem retV_stmtOpK_apply_value_error {s : Store} {v : GoValue} {op : StmtOp} {nt : Nat}
    {done vs : List GoValue} {loc : Loc} {e : Stop} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hv : op.hasValueForm = true) (hops : (v :: done).reverse = .addr loc :: vs)
    (h : applyStmtOpValue ctx s ch op nt vs = .error e) (hne : ∀ msg, e ≠ .panic msg) :
    stepFn ctx s (.retV v (.stmtOpK op nt done [] env k')) ch = .error e := by
  refine retV_stmtOpK_apply_error env k' ch ?_ hne
  rw [hops, applyStmtOp_eq_value hv, h]; rfl

/-- The value form answers and the store into the target refuses (the target cell's declared
type, a dead or missing cell): the step is the store's stop. `Mem.store` never panics. -/
theorem retV_stmtOpK_apply_value_store_error {s s₁ : Store} {v w : GoValue} {op : StmtOp}
    {nt : Nat} {done vs : List GoValue} {loc : Loc} {ch' : Choices} {ps : List PickRecord}
    {tr : AccessTrace} {e : Stop} (env : LocalEnv) (k' : Cont) (ch : Choices)
    (hv : op.hasValueForm = true) (hops : (v :: done).reverse = .addr loc :: vs)
    (h : applyStmtOpValue ctx s ch op nt vs = .ok (w, s₁, ch', ps, tr))
    (hs : Mem.store ctx s₁ loc w = .error e) :
    stepFn ctx s (.retV v (.stmtOpK op nt done [] env k')) ch = .error e := by
  refine retV_stmtOpK_apply_error env k' ch ?_ fun msg hm => ?_
  · rw [hops, applyStmtOp_eq_value hv, h]
    show storeValue ctx loc (w, s₁, ch', ps, tr) = _
    simp only [storeValue, hs]; rfl
  · subst hm
    exact Mem.store_noPanic s₁ loc w msg hs

/-- `randIntn` without a target at the apply position: the value form's outcome with the pick
dropped — the store untouched by it, the stream and pick record the consult's. -/
theorem retV_stmtOpK_apply_randIntn_untargeted {s s₁ : Store} {v w : GoValue} {nt : Nat}
    {ch' : Choices} {ps : List PickRecord} {tr : AccessTrace} (env : LocalEnv) (k' : Cont)
    (ch : Choices)
    (h : applyStmtOpValue ctx s ch .randIntn nt [v] = .ok (w, s₁, ch', ps, tr)) :
    stepFn ctx s (.retV v (.stmtOpK .randIntn nt [] [] env k')) ch
      = .ok (.next k', s₁, ch', ⟨tr, ps, []⟩) := by
  have ha : applyStmtOp ctx s ch .randIntn nt (v :: ([] : List GoValue)).reverse
      = .ok (s₁, ch', ps, tr) := by
    show applyStmtOp ctx s ch .randIntn nt [v] = _
    rw [applyStmtOp_randIntn_untargeted, h]; rfl
  rw [retV_stmtOpK_apply env k' ch ha]; rfl

end GoLean.GoCore.Machine
