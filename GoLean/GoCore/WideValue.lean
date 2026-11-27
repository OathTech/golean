import GoLean.GoCore.Machine
import GoLean.GoCore.StateWf

/-!
# The wide operators' VALUE forms (raft-proofs' request of 2026-11-27)

[AGENT lane core/wide-value-1127], 2026-11-27, on the [USER] approval of the same day (the
request is the raft-proofs session's: its next lifting layer takes a local whose address is
never taken out of the store, so a wide operator's target may have no cell to store into).

Seven wide-operator arms take their TARGET as an address operand and end by storing a computed
value into it: `allocNew`, `makeSlice`, `makeMap`, `makeChan`, `copySlice` (the count),
`appendSlice` (in place and spilling) and `randIntn` in its targeted form. None uses the target
for anything but that last store, and none reads the target's current value (`append` takes the
slice as its own operand). This module states each arm WITHOUT the store:

* `applyStmtOpValue.plan` — the validate phase on the operands MINUS the target, returning a
  commit that performs the operator's own writes (the backing array's or payload's allocation,
  the in-place element writes) and returns the VALUE the machine would store into the target,
  with the store after those writes, the choice stream, the picks and the trace so far;
* `storeValue` — the store that was left out, on one result: `Mem.store` of that value into the
  target, its trace appended; `storeValueInto` is `storeValue` after a commit;
* `applyStmtOp_plan_eq_value` — the machine's own `applyStmtOp.plan` at a target that IS an
  address equals the value plan followed by `storeValueInto`; `applyStmtOp_eq_value` is the
  un-split form.

NOTHING HERE IS RUN BY THE MACHINE: `applyStmtOp`, `applyStmtOp.plan`, `applyStmtOpCore.plan`
and `stepFn` are untouched, and the value forms are definitions beside them whose agreement
with them is the theorem. The arms below are the machine's arms with the target operand and the
last store removed, refusal texts included; a later edit to one side without the other is a
build failure at the equation, never a silent divergence.

What the equation does NOT say. (1) It is stated for a target `.addr loc`. The machine checks
its target with `valueAsLoc` inside the validate phase, at a position that differs per arm (a
nil target is the nil-dereference panic, any other non-address is `stuck`); with the target an
address the check cannot fail, and the value form has no target to check. (2) «The value» is
the OPERAND of the final `Mem.store`, which normalizes at the target cell's declared type and
can refuse; a consumer holding the value outside a cell applies `normalizeValueForTy` at the
variable's type itself. (3) The operators with no target — `mapAssign`, `mapDelete`,
`clearMap`, `clearSlice`, `sortSlice`, `print`, and `randIntn` without a target — have no value
form: `applyStmtOpValue.plan` refuses them by name, and `StmtOp.hasValueForm` says which are
covered. The comma-ok forms are `applyRhsOp`'s, which already returns values.
-/

namespace GoLean.GoCore.Machine

open GoLean

/-- The wide operators that store a computed value into a target, hence have a value form. -/
def StmtOp.hasValueForm : StmtOp → Bool
  | .allocNew _ | .makeSlice _ _ | .makeMap _ | .makeChan _ _ | .copySlice | .appendSlice _
  | .randIntn => true
  | .mapAssign _ _ | .mapDelete _ | .clearMap | .clearSlice _ | .sortSlice _ | .print _ => false

variable (ctx : ProgramCtx)

/-- The value form of the five stream-free targeted arms of `applyStmtOpCore.plan`: the same
validation on the operands minus the target, and a commit that makes the operator's own
allocation or element writes and returns the value the machine stores into the target. -/
def applyStmtOpValueCore.plan (s : Store) (op : StmtOp)
    (vs : List GoValue) : Except Stop (Commit (GoValue × Store × AccessTrace)) := do
  match op with
  | .allocNew typ =>
      match vs with
      | [value] => do
          return fun s => do
            let (nloc, s₁) ← Store.alloc ctx s value typ
            return (.addr nloc, s₁, [])
      | _ => stuck "malformed allocNew operands"
  | .makeSlice elem hasCap => do
      let (lenV, capV?) ←
        match vs, hasCap with
        | [lenV], false => pure (lenV, none)
        | [lenV, capV], true => pure (lenV, some capV)
        | _, _ => stuck "malformed makeSlice operands"
      let lenValue ← valueAsInt lenV
      let capValue ←
        match capV? with
        | none => pure lenValue
        | some capV => valueAsInt capV
      let elemSize ← tySizeBytes ctx.types elem
      if capValue < 0 || capValue * elemSize > maxAllocBytes
          || lenValue < 0 || lenValue > capValue then
        if lenValue < 0 || lenValue * elemSize > maxAllocBytes then
          panic "runtime error: makeslice: len out of range"
        else
          panic "runtime error: makeslice: cap out of range"
      let len := lenValue.toNat
      let cap := capValue.toNat
      if cap > sliceCapBudget then
        unsupported s!"make([]T, len {len}, cap {cap}): a slice backing of {cap} elements exceeds the interpreter's materialization budget ({sliceCapBudget} elements, sliceCapBudget — the element-wise whole-backing read `Mem.loadElems` overflows the native stack past it; BUG-090 cost boundary, refused by name)"
      let elemLeaves ← tyLeafCount ctx.types elem
      if cap * elemLeaves > arrayFootprintBudget then
        unsupported s!"make([]T, len {len}, cap {cap}): a slice backing of {cap} elements of {elemLeaves} scalar elements each materializes {cap * elemLeaves} scalar elements, past the interpreter's footprint budget for a run-time-length make ({arrayFootprintBudget} elements, arrayFootprintBudget — the constant-length form refuses at decode, checkMakeFootprint; BUG-131 cost boundary, refused by name)"
      let backing ← buildDefaultArrayValue ctx cap elem
      return fun s => do
        let (base, s₁) ← Store.alloc ctx s backing (.array cap elem)
        return (.slice { base := some base, offset := 0, len, cap }, s₁, [])
  | .makeMap hasSpace => do
      let spaceV? ←
        match vs, hasSpace with
        | [], false => pure none
        | [spaceV], true => pure (some spaceV)
        | _, _ => stuck "malformed makeMap operands"
      match spaceV? with
      | none => pure ()
      | some spaceV => do
          let _ ← valueAsInt spaceV
      return fun s => do
        let (base, s₁) := s.allocCell (.mapPayload #[] 0)
        return (.map { base := some base }, s₁, [])
  | .makeChan elem hasCap => do
      let capV? ←
        match vs, hasCap with
        | [], false => pure none
        | [capV], true => pure (some capV)
        | _, _ => stuck "malformed makeChan operands"
      let capacity ←
        match capV? with
        | none => pure 0
        | some capV => do
            let size ← valueAsInt capV
            let elemSize ← tySizeBytes ctx.types elem
            if size < 0 || size * elemSize > maxAllocBytes - chanHeaderBytes then
              panic "makechan: size out of range"
            pure size.toNat
      return fun s => do
        let (base, s₁) := s.allocCell (.chanPayload #[] capacity false)
        return (.chan { base := some base }, s₁, [])
  | .copySlice =>
      match vs with
      | [dstV, srcV] => do
          let dstSlice ← valueAsSlice dstV
          let srcSlice ← valueAsSlice srcV
          validateSlice dstSlice
          validateSlice srcSlice
          let count := Nat.min dstSlice.len srcSlice.len
          let (values, trR) ← Mem.loadRun ctx s srcSlice count
          return fun s => do
            let (current, trW) ← Mem.storeRun ctx s dstSlice 0 values
            return (.int (Int.ofNat count), current, trR ++ trW)
      | _ => stuck "malformed copySlice operands"
  | op => stuck s!"the wide operator {repr op} stores into no target: it has no value form"

/-- **The value form of `applyStmtOp.plan`** for the seven targeted arms: the operands are the
machine's MINUS the target; the commit performs the operator's own writes and returns the value
the machine would store into the target, the store after those writes, and the stream, picks
and trace exactly as the machine threads them up to that store. -/
def applyStmtOpValue.plan (s : Store) (choices : Choices) (op : StmtOp) (_nt : Nat)
    (vs : List GoValue) :
    Except Stop (Commit (GoValue × Store × Choices × List PickRecord × AccessTrace)) := do
  match op with
  | .appendSlice elem =>
      match vs with
      | [sliceV, elemsV] => do
          let slice ← valueAsSlice sliceV
          let elems ← valueAsSlice elemsV
          validateSlice slice
          validateSlice elems
          let (elemValues, trE) ← Mem.loadSlice ctx s elems
          let newLen := slice.len + elemValues.size
          if newLen <= slice.cap then
            return fun s => do
              let (current, trW) ← Mem.storeRun ctx s slice slice.len elemValues.toList
              return (.slice { slice with len := newLen }, current, choices, [], trE ++ trW)
          else
            let elemSize ← tySizeBytes ctx.types elem
            if newLen ≥ intExclusiveUpperBound || newLen * elemSize > maxAllocBytes then
              panic "runtime error: growslice: len out of range"
            let pointerful ← tyHasPointers ctx.types elem
            let (oldValues, trO) ← Mem.loadSlice ctx s slice
            let width := appendSpillWidth slice.cap newLen
            let (extra, choices, ps) := Choices.consumeAtE .appendSpill width choices
            let newCap := appendSpillCapAt elemSize pointerful slice.cap newLen extra
            appendSpillFootprintCheck ctx elem newLen newCap
            let backing ← buildAppendBackingValue ctx elem oldValues elemValues newCap
            return fun s => do
              let (base, current) ← Store.alloc ctx s backing (.array newCap elem)
              return (.slice { base := some base, offset := 0, len := newLen, cap := newCap },
                current, choices, ps, trE ++ trO)
      | _ => stuck "malformed appendSlice operands"
  | .randIntn =>
      match vs with
      | [.int n .int] =>
          if n < 1 then
            stuck s!"rand-intn: bound {n} ≤ 0 reached the draw (the lowering's guard was bypassed — forged wire)"
          else
            let (pick, choices, ps) := Choices.consumeAtE .intn n.toNat choices
            return fun s => return (.int pick .int, s, choices, ps, [])
      | _ => stuck "malformed rand-intn operands (expected [target address,] an int bound)"
  | op => do
      let c ← applyStmtOpValueCore.plan ctx s op vs
      return fun s => do
        let (v, s₁, tr) ← c s
        return (v, s₁, choices, [], tr)

@[inherit_doc applyStmtOpValue.plan]
def applyStmtOpValue (s : Store) (choices : Choices) (op : StmtOp) (nt : Nat)
    (vs : List GoValue) :
    Except Stop (GoValue × Store × Choices × List PickRecord × AccessTrace) := do
  let c ← applyStmtOpValue.plan ctx s choices op nt vs
  c s

/-- The store a value form leaves out, on one result: write the value into the target, the
write's trace appended to the operator's. `Mem.store` normalizes at the target cell's declared
type and can refuse. -/
def storeValue (loc : Loc) :
    GoValue × Store × Choices × List PickRecord × AccessTrace →
      Except Stop (Store × Choices × List PickRecord × AccessTrace)
  | (v, s₁, choices, ps, tr) => do
      let (s', trT) ← Mem.store ctx s₁ loc v
      return (s', choices, ps, tr ++ trT)

/-- `storeValue` after a value form's commit. -/
def storeValueInto (loc : Loc)
    (c : Commit (GoValue × Store × Choices × List PickRecord × AccessTrace)) :
    Commit (Store × Choices × List PickRecord × AccessTrace) := fun s =>
  c s >>= storeValue ctx loc

end GoLean.GoCore.Machine

namespace GoLean.GoCore.Machine
open GoLean
variable {ctx : ProgramCtx}

/-! ## The equation: the machine's plan at an address target is the value plan, then the store -/

private theorem error_bind' {α β : Type} (e : Stop) (k : α → Except Stop β) :
    ((Except.error e : Except Stop α) >>= k) = Except.error e := rfl

private theorem error_map' {α β : Type} (e : Stop) (f : α → β) :
    f <$> (Except.error e : Except Stop α) = Except.error e := rfl

/-- Normalize both plans (monad laws, the target's `valueAsLoc`, refusals absorbing their
continuations), then both commits. -/
local macro "wv_norm" : tactic => `(tactic| (
  simp only [valueAsLoc, bind_assoc, pure_bind, map_bind, map_pure, bind_pure_comp, stuck_def,
    panic_def, unsupported_def, error_bind', error_map', Commit.withStream, storeValueInto,
    List.nil_append, List.append_assoc, Functor.map_map, bind_map_left]))

/-- Close a normalized goal: walk the two plans in step (same binds, same branches) down to
their commits, and decide each pair of commits at an arbitrary store. -/
local macro "wv_commit" : tactic => `(tactic| (
  repeat' first
    | rfl
    | (funext s0; simp [Commit.withStream, storeValueInto, storeValue]; done)
    | wv_norm
    | (refine bind_congr fun _ => ?_)
    | (refine congrArg (f := Pure.pure) ?_)
    | (refine congrArg (f := Except.ok) ?_)
    | split
    | (congr 1; funext _)))

theorem applyStmtOp_plan_eq_value_allocNew {s : Store} {choices : Choices} {nt : Nat} {loc : Loc}
    {vs : List GoValue} {typ : Ty} :
    applyStmtOp.plan ctx s choices (.allocNew typ) nt (.addr loc :: vs)
      = storeValueInto ctx loc <$> applyStmtOpValue.plan ctx s choices (.allocNew typ) nt vs := by
  simp only [applyStmtOp.plan, applyStmtOpCore.plan, applyStmtOpValue.plan, applyStmtOpValueCore.plan]
  rcases vs with _ | ⟨v1, _ | ⟨v2, rest⟩⟩ <;> wv_norm
  all_goals wv_commit

theorem applyStmtOp_plan_eq_value_makeMap {s : Store} {choices : Choices} {nt : Nat} {loc : Loc}
    {vs : List GoValue} {hasSpace : Bool} :
    applyStmtOp.plan ctx s choices (.makeMap hasSpace) nt (.addr loc :: vs)
      = storeValueInto ctx loc <$> applyStmtOpValue.plan ctx s choices (.makeMap hasSpace) nt vs := by
  simp only [applyStmtOp.plan, applyStmtOpCore.plan, applyStmtOpValue.plan, applyStmtOpValueCore.plan]
  rcases vs with _ | ⟨v1, _ | ⟨v2, rest⟩⟩ <;> cases hasSpace <;> wv_norm
  all_goals wv_commit

theorem applyStmtOp_plan_eq_value_makeSlice {s : Store} {choices : Choices} {nt : Nat} {loc : Loc}
    {vs : List GoValue} {elem : Ty} {hasCap : Bool} :
    applyStmtOp.plan ctx s choices (.makeSlice elem hasCap) nt (.addr loc :: vs)
      = storeValueInto ctx loc <$> applyStmtOpValue.plan ctx s choices (.makeSlice elem hasCap) nt vs := by
  simp only [applyStmtOp.plan, applyStmtOpCore.plan, applyStmtOpValue.plan, applyStmtOpValueCore.plan]
  rcases vs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, rest⟩⟩⟩ <;> cases hasCap <;> wv_norm
  all_goals wv_commit

theorem applyStmtOp_plan_eq_value_makeChan {s : Store} {choices : Choices} {nt : Nat} {loc : Loc}
    {vs : List GoValue} {elem : Ty} {hasCap : Bool} :
    applyStmtOp.plan ctx s choices (.makeChan elem hasCap) nt (.addr loc :: vs)
      = storeValueInto ctx loc <$> applyStmtOpValue.plan ctx s choices (.makeChan elem hasCap) nt vs := by
  simp only [applyStmtOp.plan, applyStmtOpCore.plan, applyStmtOpValue.plan, applyStmtOpValueCore.plan]
  rcases vs with _ | ⟨v1, _ | ⟨v2, rest⟩⟩ <;> cases hasCap <;> wv_norm
  all_goals wv_commit

theorem applyStmtOp_plan_eq_value_copySlice {s : Store} {choices : Choices} {nt : Nat} {loc : Loc}
    {vs : List GoValue}  :
    applyStmtOp.plan ctx s choices (.copySlice) nt (.addr loc :: vs)
      = storeValueInto ctx loc <$> applyStmtOpValue.plan ctx s choices (.copySlice) nt vs := by
  simp only [applyStmtOp.plan, applyStmtOpCore.plan, applyStmtOpValue.plan, applyStmtOpValueCore.plan]
  rcases vs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, rest⟩⟩⟩ <;> wv_norm
  all_goals wv_commit

theorem applyStmtOp_plan_eq_value_appendSlice {s : Store} {choices : Choices} {nt : Nat} {loc : Loc}
    {vs : List GoValue} {elem : Ty} :
    applyStmtOp.plan ctx s choices (.appendSlice elem) nt (.addr loc :: vs)
      = storeValueInto ctx loc <$> applyStmtOpValue.plan ctx s choices (.appendSlice elem) nt vs := by
  simp only [applyStmtOp.plan, applyStmtOpValue.plan]
  rcases vs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, rest⟩⟩⟩ <;> wv_norm
  all_goals wv_commit

theorem applyStmtOp_plan_eq_value_randIntn {s : Store} {choices : Choices} {nt : Nat} {loc : Loc}
    {vs : List GoValue} :
    applyStmtOp.plan ctx s choices .randIntn nt (.addr loc :: vs)
      = storeValueInto ctx loc <$> applyStmtOpValue.plan ctx s choices .randIntn nt vs := by
  simp only [applyStmtOp.plan, applyStmtOpValue.plan]
  rcases vs with _ | ⟨v1, _ | ⟨v2, rest⟩⟩
  · wv_norm
  · cases v1 with
    | int n k => cases k <;> wv_norm <;> wv_commit <;> simp
    | _ => wv_norm
  · cases v1 with
    | int n k => cases k <;> wv_norm
    | _ => wv_norm

/-- **The machine's wide operator at an address target is its value form, then the store.**
For each of the seven targeted operators (`StmtOp.hasValueForm`): the validate phase of
`applyStmtOp.plan` on `.addr loc :: vs` is `applyStmtOpValue.plan`'s on `vs` — the same
refusals and panics in the same order, the same consultations of the choice stream — and its
commit is the value form's commit followed by `Mem.store` of the returned value into `loc`,
the store's trace appended (`storeValueInto`). -/
theorem applyStmtOp_plan_eq_value {s : Store} {choices : Choices} {op : StmtOp} {nt : Nat}
    {loc : Loc} {vs : List GoValue} (h : op.hasValueForm = true) :
    applyStmtOp.plan ctx s choices op nt (.addr loc :: vs)
      = storeValueInto ctx loc <$> applyStmtOpValue.plan ctx s choices op nt vs := by
  cases op with
  | allocNew typ => exact applyStmtOp_plan_eq_value_allocNew
  | makeSlice elem hasCap => exact applyStmtOp_plan_eq_value_makeSlice
  | makeMap hasSpace => exact applyStmtOp_plan_eq_value_makeMap
  | makeChan elem hasCap => exact applyStmtOp_plan_eq_value_makeChan
  | copySlice => exact applyStmtOp_plan_eq_value_copySlice
  | appendSlice elem => exact applyStmtOp_plan_eq_value_appendSlice
  | randIntn => exact applyStmtOp_plan_eq_value_randIntn
  | _ => cases h

/-- The un-split form: the machine's wide apply at an address target is the value form's apply,
then the store of its value into the target. -/
theorem applyStmtOp_eq_value {s : Store} {choices : Choices} {op : StmtOp} {nt : Nat}
    {loc : Loc} {vs : List GoValue} (h : op.hasValueForm = true) :
    applyStmtOp ctx s choices op nt (.addr loc :: vs)
      = applyStmtOpValue ctx s choices op nt vs >>= storeValue ctx loc := by
  unfold applyStmtOp applyStmtOpValue
  rw [applyStmtOp_plan_eq_value h]
  cases applyStmtOpValue.plan ctx s choices op nt vs with
  | error e => rfl
  | ok c => rfl

end GoLean.GoCore.Machine
